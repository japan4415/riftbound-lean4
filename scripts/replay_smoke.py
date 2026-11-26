"""Exercise the real-card live protocol and replay CLI together."""

import argparse
import json
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from live import Lean, ROOT


def ask(live: Lean, command: str) -> dict:
    response = json.loads(live.ask(command))
    assert "error" not in response, (command.split(maxsplit=1)[0], response)
    return response


def choose(live: Lean, response: dict, kind: str, actor: str | None = None) -> dict:
    choice = next(
        item for item in response["legal"]
        if item["a"]["kind"] == kind and (actor is None or item["a"]["actor"] == actor)
    )
    return ask(live, f"act {choice['k']}")


def keep(live: Lean, response: dict) -> dict:
    while any(item["a"]["kind"] == "mulliganDone" for item in response["legal"]):
        response = choose(live, response, "mulliganDone")
    return response


def play_to_turn(live: Lean, response: dict, turn: int) -> dict:
    priorities = ("mulliganDone", "manaAbility", "runeAbility", "playCard", "standardMove", "pass")
    for _ in range(100):
        if response["steps"][-1]["state"]["turn"] >= turn:
            return response
        choice = next(
            (item for kind in priorities for item in response["legal"]
             if item["a"]["kind"] == kind
             and (kind != "runeAbility" or item["a"]["ability"] == "exhaust")), None,
        )
        if choice is None:
            choice = next(item for item in response["legal"] if item["a"]["kind"] != "concede")
        response = ask(live, f"act {choice['k']}")
    raise AssertionError(f"the fixture did not reach turn {turn}")


def start(live: Lean, setup: dict) -> dict:
    return ask(live, f"start-json 71 01 {json.dumps(setup)}")


def played_match(live: Lean, setup: dict) -> dict:
    turn = play_to_turn(live, start(live, setup), 5)
    assert any(turn["steps"][-1]["state"]["points"])
    ask(live, "judge")
    assert not ask(live, "undo")["over"]
    judge = ask(live, "judge")
    assert judge["match"]["sameBattlefields"] and not judge["sideboard"]["allowed"]
    second = keep(live, ask(live, "next"))
    win = choose(live, second, "concede", "p1")
    assert win["match"]["wins"] == [1, 0]

    reg = setup["decks"]["constructed"]["decks"][1]
    champion = {"code": "RAD-112"}
    outgoing = {"code": "RAD-094"}
    deck = {**reg["deck"], "chosenChampion": champion, "main": [*reg["deck"]["main"], champion]}
    deck["main"].remove(outgoing)
    registration = {"deck": deck, "sideboard": [outgoing, {"code": "RAD-097"}]}
    assert "error" in json.loads(live.ask(f"register 1 {json.dumps({**registration, 'sideboard': []})}"))
    ask(live, f"register 1 {json.dumps(registration)}")
    assert ask(live, "next")["choice"] == 1
    third = keep(live, ask(live, "next first"))
    final = choose(live, third, "concede", "p1")
    assert final["match"]["wins"] == [2, 0] and final["archiveAvailable"]

    saved = ask(live, "replay")
    assert saved["input"]["games"][2]["decks"]["constructed"]["decks"][1] == registration
    first, second, third = [game["summary"] for game in saved["games"]]
    assert first["battlefields"] == second["battlefields"]
    assert first["turnOrder"] == second["turnOrder"] == [{"n": 0}, {"n": 1}]
    assert third["turnOrder"] == [{"n": 1}, {"n": 0}]
    return saved


def check_match_endings(live: Lean, setup: dict) -> None:
    keep(live, start(live, setup))
    ask(live, "judge")
    assert ask(live, "time-between-games")["match"]["winner"] is None
    assert "error" in json.loads(live.ask("next"))
    assert ask(live, "replay")["summary"]["result"] == "draw"

    keep(live, start(live, setup))
    timed = ask(live, "clock")
    turns = {timed["steps"][-1]["state"]["turn"]}
    for _ in range(10):
        if timed["over"]:
            break
        timed = choose(live, timed, "pass")
        turns.update(step["state"]["turn"] for step in timed["steps"] if step["state"]["result"] is None)
    assert timed["match"]["finished"] and len(turns) == 4
    assert ask(live, "replay")["games"][0]["summary"]["timed"]

    start(live, setup)
    ask(live, "concede-match 0")
    archive = ask(live, "replay")
    assert archive["summary"]["wins"] == [0, 0]
    assert archive["games"][0]["summary"]["result"] is None


def check_cli(folder: Path, saved: dict, setup: dict) -> None:
    tool = ROOT / ".lake/build/bin/riftbound-replay"
    source = folder / "inputs.json"
    archive = folder / "archive.json"
    trace = folder / "trace.json"

    def command(*args: str | Path, error: str | None = None) -> str:
        result = subprocess.run([tool, *args], capture_output=True, text=True, check=False)
        if error is None:
            assert result.returncode == 0, result.stderr
        else:
            assert result.returncode == 1 and error in result.stderr, result.stderr
        return result.stdout

    source.write_text(json.dumps(saved["input"]), encoding="utf-8")
    assert json.loads(command("record", source, archive)) == saved["summary"]
    assert json.loads(archive.read_text(encoding="utf-8")) == saved
    assert json.loads(command("verify", archive)) == saved["summary"]
    legacy = json.loads(archive.read_text(encoding="utf-8"))
    for game in legacy["input"]["games"]:
        game.pop("openingOrder", None)
    for game in legacy["games"]:
        game["input"].pop("openingOrder", None)
    legacy_archive = folder / "previous-format.json"
    legacy_archive.write_text(json.dumps(legacy), encoding="utf-8")
    assert json.loads(command("verify", legacy_archive)) == saved["summary"]
    command("view", archive, trace)
    view = json.loads(trace.read_text(encoding="utf-8"))
    assert len(view["games"]) == 3 and view["wins"] == [2, 0] and view["exact"]
    assert not view["cardsFullyChecked"] and saved["games"][0]["summary"]["uncheckedCards"][0]

    witness = saved["games"][0]["checkpoints"][2]
    witness["state"] = "0"
    corrupted = folder / "changed-checkpoint.json"
    corrupted.write_text(json.dumps(saved), encoding="utf-8")
    command("verify", corrupted, error="game 1: checkpoint 2")

    answers = saved["input"]["games"][0]["answers"]
    observed = answers[0]["observed"]["action"]
    answers[0] = {"inferred": {"action": observed, "evidence": "reconstructed from later evidence"}}
    source.write_text(json.dumps(saved["input"]), encoding="utf-8")
    assert not json.loads(command("record", source, folder / "inferred.json"))["exact"]
    answers[0] = {"unknown": {"description": "shuffle was hidden"}}
    source.write_text(json.dumps(saved["input"]), encoding="utf-8")
    command("record", source, folder / "unknown.json", error="game 1: answer 1 is unobserved")

    p0, p1, p2, p3 = [{"n": index} for index in range(4)]
    decks = setup["decks"]["constructed"]["decks"] * 2
    team_game = {
        "decks": decks, "chooser": p0, "order": [p0, p2, p1, p3],
        "battlefields": [[p, decks[p["n"]]["deck"]["battlefields"][0]] for p in (p2, p1, p3)],
        "points": [10, 8], "ending": "time", "timed": True, "answers": [],
    }
    team_record = {
        "seats": {"team0": [p0, p1], "team1": [p2, p3]},
        "tournament": {**setup["tournament"], "format": "twoVTwo"},
        "legalSets": setup["config"]["formatLegality"]["legalSets"],
        "winsRequired": 2, "games": [team_game], "ending": "finalGame",
    }
    team_input = folder / "team.json"
    team_input.write_text(json.dumps(team_record), encoding="utf-8")
    assert json.loads(command("check-team", team_input))["wins"] == [1, 0]
    team_game["order"] = [p0, p1, p2, p3]
    team_input.write_text(json.dumps(team_record), encoding="utf-8")
    command("check-team", team_input, error="team game 1: turn order")

    def observed(actor: object, kind: object) -> dict:
        return {"observed": {"action": {"actor": actor, "kind": kind}}}

    # Two copies of the already recorded shuffle orders, with new object IDs for the second pair.
    first_shuffles = saved["games"][0]["input"]["answers"][:4]
    offset = sum(1 + sum(len(reg["deck"][field]) for field in
                         ("reserveLegends", "main", "runes", "battlefields")) for reg in decks[:2])
    other_shuffles = [observed("chance", {"arrange": {"order": [
        {"n": item["n"] + offset} for item in answer["observed"]["action"]["kind"]["arrange"]["order"]
    ]}}) for answer in first_shuffles]
    team_order = [p0, p2, p1, p3]
    team_game.update(
        order=team_order, points=[0, 0], timed=False, ending={"concede": {"seat": p1}},
        answers=[*first_shuffles, *other_shuffles,
                 *[observed("chance", {"pick": {"index": 0}}) for _ in range(3)],
                 *[observed({"player": {"p": seat}}, "mulliganDone") for seat in team_order],
                 observed({"player": {"p": p1}}, "concede")],
    )
    team_record["winsRequired"] = 1
    team_input.write_text(json.dumps(team_record), encoding="utf-8")
    team_archive = folder / "team-archive.json"
    assert json.loads(command("record-team", team_input, team_archive))["wins"] == [0, 1]
    assert json.loads(command("verify-team", team_archive))["wins"] == [0, 1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="keep the generated archive and viewer trace here")
    args = parser.parse_args()
    setup = json.loads((ROOT / "data/replay/constructed-example.json").read_text(encoding="utf-8"))
    live = Lean(ROOT / ".lake/build/bin/riftbound-live")
    try:
        saved = played_match(live, setup)
        check_match_endings(live, setup)
    finally:
        live.close()
        live.proc.wait()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        check_cli(args.output, saved, setup)
    else:
        with TemporaryDirectory() as folder:
            check_cli(Path(folder), saved, setup)
    print("replay smoke: OK")


if __name__ == "__main__":
    main()
