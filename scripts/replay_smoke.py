"""Exercise the real-card live protocol and replay CLI together."""

import argparse
import json
import subprocess
from collections.abc import Callable
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


def play_to_turn(live: Lean, response: dict, turn: int, move: bool = True) -> dict:
    priorities = ("mulliganDone", "manaAbility", "runeAbility", "playCard")
    priorities += ("standardMove", "pass") if move else ("pass",)
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


def group_move_match(live: Lean, setup: dict) -> dict:
    response = keep(live, start(live, setup))
    for _ in range(70):
        if any(item["a"]["kind"] == "startGroupMove" for item in response["legal"]):
            break
        legal = [item for item in response["legal"] if item["a"]["kind"] != "concede"]
        choice = next((item for kind in ("runeAbility", "playCard", "pass") for item in legal
                       if item["a"]["kind"] == kind and (kind != "runeAbility" or
                       item["a"]["ability"] == "exhaust")), legal[0])
        response = ask(live, f"act {choice['k']}")
    else:
        raise AssertionError("no simultaneous Standard Move was offered")
    response = choose(live, response, "startGroupMove")
    response = choose(live, response, "choose")
    response = choose(live, response, "choose")
    finish = next(item for item in response["legal"] if item["a"].get("yes") is True)
    units = finish["a"]["groupMoveUnits"]
    response = ask(live, f"act {finish['k']}")
    assert [e["unit"] for e in response["steps"][-1]["events"] if e["t"] == "moved_unit"] == units
    ask(live, "concede-match 1")
    return ask(live, "replay")


def elimination_match(live: Lean, setup: dict) -> dict:
    keep(live, start(live, {**setup, "singleElimination": True}))
    tied = ask(live, "judge")
    assert tied["match"]["wins"] == [0, 0] and not tied["match"]["finished"]
    clock = ask(live, "time-between-games")
    assert clock["match"]["timedTiebreaker"] and not clock["external"]["betweenGames"]
    second = keep(live, ask(live, "next"))
    assert not second["external"]["clock"]
    sudden_death = play_to_turn(live, second, 7, move=False)
    assert sudden_death["steps"][-1]["state"]["points"] == [0, 0]
    won = choose(live, sudden_death, "standardMove")
    for _ in range(8):
        if won["over"]:
            break
        won = choose(live, won, "pass")
    assert won["archiveAvailable"] and won["match"]["winner"] == 0
    archive = ask(live, "replay")
    assert archive["input"]["elimination"]["timeAfterGames"] == 1
    assert archive["games"][1]["summary"]["suddenDeathTurn"] == 7
    return archive


def observed(actor: object, kind: object) -> dict:
    return {"observed": {"action": {"actor": actor, "kind": kind}}}


def limited_answers(decks: list[dict], order: list[dict], team: bool = False) -> list[dict]:
    answers = []
    offset = 0
    for deck in decks:
        for zone in ("main", "runes"):
            ids = [{"n": i} for i in range(offset, offset + len(deck[zone]))]
            answers.append(observed("chance", {"arrange": {"order": ids}}))
            offset += len(ids)
        offset += len(deck["battlefields"])
    contributors = order[1:] if team else order
    answers.extend(observed("chance", {"pick": {"index": 0}}) for _ in contributors)
    if not team:
        answers.append(observed("chance", {"arrangePlayers": {"order": order}}))
    answers.extend(observed({"player": {"p": seat}}, "mulliganDone") for seat in order)
    answers.append(observed({"player": {"p": {"n": 3 if team else 1}}}, "concede"))
    return answers


def limited_fixtures(setup: dict) -> tuple[dict, dict]:
    originals = [reg["deck"] for reg in setup["decks"]["constructed"]["decks"]]
    p0, p1, p2, p3 = [{"n": i} for i in range(4)]
    legal_sets = setup["config"]["formatLegality"]["legalSets"]
    blank = {"code": "TKN-LimitedBlank"}

    def build_decks(game: int) -> list[dict]:
        return [
            {"identity": ["fury", "order", "chaos"], "chosenChampion": None, "legend": None,
             "reserveLegends": [], "main": deck["main"][game:25 + game],
             "runes": deck["runes"], "battlefields": [deck["battlefields"][game]]}
            for deck in originals
        ]

    duel_games = []
    team_games = []
    for game in range(2):
        configuration = build_decks(game)
        duel_games.append({"decks": {"limited": {"decks": configuration}}, "chooser": [p0, p1][game],
                           "answers": limited_answers(configuration, [p0, p1])})
        order = [p1, p3, p0, p2]
        team_decks = [configuration[0], {**configuration[1], "battlefields": []},
                      configuration[0], {**configuration[1], "battlefields": [blank]}]
        team_games.append(
            {"sealedDecks": team_decks, "chooser": [p0, p1][game], "order": order,
             "battlefields": [[p, team_decks[p["n"]]["battlefields"][0]] for p in order[1:]],
             "points": [0, 0], "ending": {"concede": {"seat": p3}}, "timed": False,
             "answers": limited_answers(team_decks, order, team=True)}
        )
    duel = {"config": {**setup["config"], "ruleSet": {"tournament": {"format": "draft"}},
                       "formatLegality": {"legalSets": legal_sets, "banned": []}},
            "limitedPools": [d["main"] + d["battlefields"] for d in originals],
            "winsRequired": 2, "fuel": 100, "games": duel_games, "ending": "finalGame"}
    cards = originals[0]["main"] + originals[1]["main"] + originals[0]["battlefields"]
    packs = [cards[i::8] for i in range(8)]
    team = {"seats": {"team0": [p0, p1], "team1": [p2, p3]}, "legalSets": legal_sets,
            "sealed": {"team0": packs, "team1": packs}, "winsRequired": 2, "games": team_games,
            "ending": "finalGame"}
    return duel, team


def check_limited_cli(folder: Path, setup: dict, command: Callable[..., str]) -> None:
    duel, team = limited_fixtures(setup)
    for label, inputs, suffix in (("draft", duel, ""), ("sealed-team", team, "-team")):
        source = folder / f"{label}-input.json"
        archive = folder / f"{label}-archive.json"
        trace = folder / f"{label}-trace.json"
        source.write_text(json.dumps(inputs), encoding="utf-8")
        summary = json.loads(command("record" + suffix, source, archive))
        assert summary["wins"] == [2, 0] and summary["exact"]
        assert json.loads(command("verify" + suffix, archive)) == summary
        command("view" + suffix, archive, trace)
        exported = json.loads(trace.read_text(encoding="utf-8"))
        assert exported["winner"] == 0 and len(exported["games"]) == 2
        assert exported["cards"][blank["code"]]["name"] == "Blank Battlefield"


def bo1_registration(original: dict) -> dict:
    previous = original["deck"]
    champion = {"code": "RAD-112"}
    outgoing = {"code": "RAD-094"}
    main = list(previous["main"])
    main[main.index(outgoing)] = champion
    return {
        "deck": {**previous, "main": main, "chosenChampion": champion},
        "sideboard": [outgoing if card == champion else card for card in original["sideboard"]],
    }


def live_bo1_match(live: Lean, setup: dict) -> dict:
    config = {**setup, "bo1Sideboarding": True, "winsRequired": 1}
    originals = config["decks"]["constructed"]["decks"]
    wrong_format = json.loads(live.ask(f"start-json 71 01 {json.dumps({**config, 'winsRequired': 2})}"))
    assert "initial sideboarding requires a Constructed Best of 1 match" in wrong_format["error"]
    automated = ask(live, f"start-json 71 0 {json.dumps(config)}")
    assert automated["bo1"]["chooser"] is None
    assert [seat["player"] for seat in automated["bo1"]["sideboards"]] == [0]
    assert [row["action"]["kind"] for row in automated["steps"][1:]] == ["pick", "pick", "arrangePlayers"]

    started = start(live, config)
    assert started["bo1"] == {"chooser": 1, "sideboards": []}
    assert [row["action"]["kind"] for row in started["steps"][1:]] == ["pick", "pick"]
    assert "no Best of 1 sideboard window" in json.loads(live.ask("bo1-sideboard"))["error"]
    changed = bo1_registration(originals[1])
    register = f"register 1 {json.dumps(changed)}"
    assert "cannot be used now" in json.loads(live.ask(register))["error"]
    initiative = ask(live, "bo1-first first")
    assert initiative["bo1"]["chooser"] is None
    assert initiative["steps"][0]["bo1Initiative"]
    assert initiative["steps"][0]["action"]["turnOrder"] == [1, 0]
    assert "p1.championZone" not in initiative["steps"][0]["state"]["zones"]
    assert [seat["player"] for seat in initiative["bo1"]["sideboards"]] == [0, 1]
    assert ask(live, "undo")["bo1"] == started["bo1"]
    alternate = ask(live, "bo1-first second")
    assert alternate["steps"][0]["action"]["turnOrder"] == [0, 1]
    assert ask(live, "undo")["bo1"] == started["bo1"]
    assert ask(live, "bo1-first first") == initiative
    illegal = json.loads(live.ask(f"register 1 {json.dumps({**changed, 'sideboard': []})}"))
    assert "registered pool or fixed slots changed" in illegal["error"]
    registered = ask(live, register)
    assert registered["steps"] == []
    reverted = ask(live, "undo")
    assert reverted["bo1"] == initiative["bo1"]
    ask(live, register)

    p0 = originals[0]["deck"]
    outgoing = next(card for card in p0["main"] if card != p0["chosenChampion"])
    incoming = originals[0]["sideboard"][0]
    swap = f"swap {outgoing['code']} {incoming['code']} 0"
    swapped = ask(live, swap)
    assert any(card["id"] == outgoing["code"] for card in swapped["bo1"]["sideboards"][0]["side"])
    confirmed = ask(live, "bo1-sideboard")
    assert confirmed["bo1"] is None and confirmed["steps"][0]["bo1Sideboard"]
    state = confirmed["steps"][0]["state"]
    champion_id = state["zones"]["p1.championZone"][0]
    assert state["new"][str(champion_id)]["card"] == changed["deck"]["chosenChampion"]["code"]
    assert all(f"p{seat}.hand" not in state["zones"] for seat in (0, 1))
    assert confirmed["steps"][1]["action"]["kind"] == "arrange"
    assert ask(live, "undo")["bo1"] == swapped["bo1"]
    assert ask(live, "bo1-sideboard") == confirmed
    assert "cannot be used now" in json.loads(live.ask(register))["error"]
    final = choose(live, keep(live, confirmed), "concede", "p0")
    assert final["archiveAvailable"] and final["match"]["winner"] == 1
    archive = ask(live, "replay")
    game = archive["input"]["games"][0]
    assert game["bo1Setup"] == originals and game["answers"][3] == "bo1Sideboard"
    assert game["decks"]["constructed"]["decks"][1] == changed
    assert archive["games"][0]["summary"]["turnOrder"] == [{"n": 1}, {"n": 0}]
    return archive


def live_team_matches(live: Lean, setup: dict) -> dict[str, tuple[dict, list[int]]]:
    original = setup["decks"]["constructed"]["decks"]
    team = json.loads((ROOT / "data/replay/team-constructed-example.json").read_text(encoding="utf-8"))

    def start_team(config: dict) -> dict:
        return ask(live, f"start-team-json 71 0123 {json.dumps(config)}")

    opened = start_team(team)
    assert opened["players"] == 4 and opened["teams"] == [[0, 1], [2, 3]]
    assert opened["teamFormat"] == "constructed"
    first = keep(live, opened)
    invite = choose(live, first, "inviteTeammate", "p1")
    choose(live, invite, "pass", "p0")
    drawn = ask(live, "judge")
    assert drawn["match"]["wins"] == [0, 0] and drawn["match"]["sameBattlefields"]
    registration = f"register 3 {json.dumps(bo1_registration(original[1]))}"
    assert "cannot be used now" in json.loads(live.ask(registration))["error"]
    assert "draw preserves the same turn order" in json.loads(live.ask("team-next 0213"))["error"]
    second = keep(live, ask(live, "team-next"))
    won = choose(live, second, "concede", "p3")
    assert won["match"]["wins"] == [1, 0] and won["sideboard"]["allowed"]
    ask(live, registration)
    choices = ask(live, "team-next")["teamChoice"]
    assert choices["team"] == 1 and [3, 1, 2, 0] in choices["orders"]
    assert "invalid alternating A/B turn order" in json.loads(live.ask("team-next 0123"))["error"]
    third = keep(live, ask(live, "team-next 3120"))
    match_end = choose(live, third, "concede", "p3")
    assert match_end["match"]["winner"] == 0 and match_end["archiveAvailable"]
    completed = ask(live, "replay")
    games = completed["input"]["games"]
    assert games[0]["order"] == games[1]["order"] and games[0]["battlefields"] == games[1]["battlefields"]
    assert games[2]["order"] == [{"n": seat} for seat in (3, 1, 2, 0)]
    assert games[2]["decks"][3] == bo1_registration(original[1])
    ask(live, "undo")
    assert ask(live, "concede-match 3")["match"]["winner"] == 0
    interrupted = ask(live, "replay")
    assert interrupted["input"]["games"][2]["ending"] == "matchEnded"
    assert interrupted["input"]["ending"] == {"concede": {"seat": {"n": 3}}}

    _, sealed = limited_fixtures(setup)
    sealed_games = sealed["games"]
    sealed_setup = {k: sealed[k] for k in ("legalSets", "sealed", "winsRequired")}
    sealed_setup.update(decks={"limited": {"decks": sealed_games[0]["sealedDecks"]}},
                        firstChooser=sealed_games[0]["chooser"], order=sealed_games[0]["order"])
    opened = start_team(sealed_setup)
    assert opened["teamFormat"] == "sealed"
    first_win = choose(live, keep(live, opened), "concede", "p3")
    assert first_win["match"]["wins"] == [1, 0]
    assert "uses too many copies" in json.loads(live.ask("team-next 1302"))["error"]
    second = ask(live, f"team-next 1302 {json.dumps(sealed_games[1]['sealedDecks'])}")
    assert choose(live, keep(live, second), "concede", "p3")["archiveAvailable"]
    sealed_archive = ask(live, "replay")
    assert sealed_archive["input"]["games"][1]["sealedDecks"] == sealed_games[1]["sealedDecks"]

    keep(live, start_team({**team, "singleElimination": True}))
    ask(live, "judge")
    assert ask(live, "time-between-games")["match"]["timedTiebreaker"]
    tiebreaker = ask(live, "team-next")
    assert not tiebreaker["external"]["clock"]
    ask(live, "concede-match 3")
    timed = ask(live, "replay")
    assert timed["input"]["elimination"]["timeAfterGames"] == 1
    assert timed["input"]["games"][1]["timed"]

    return {"live-team": (completed, [2, 0]), "live-team-interrupted": (interrupted, [1, 0]),
            "live-team-sealed": (sealed_archive, [2, 0]), "live-team-tiebreaker": (timed, [0, 0])}


def check_bo1_cli(folder: Path, setup: dict, command: Callable[..., str]) -> None:
    originals = setup["decks"]["constructed"]["decks"]
    changed = bo1_registration(originals[1])
    champion = changed["deck"]["chosenChampion"]
    submitted = [originals[0], changed]
    p0, p1 = {"n": 0}, {"n": 1}
    order = [p1, p0]
    initiative = observed("chance", {"arrangePlayers": {"order": order}})
    tape = [observed("chance", {"pick": {"index": i}}) for i in (1, 0)]
    tape.extend([initiative, "bo1Sideboard"])
    # One Legend and three Battlefield candidates per seat, then two Battlefield zone changes.
    offset = sum(2 + len(reg["deck"]["battlefields"]) for reg in originals)
    for registration in submitted:
        deck = registration["deck"]
        offset += len(deck["reserveLegends"]) + 1
        for size in (len(deck["main"]) - 1, len(deck["runes"])):
            order_ids = [{"n": i} for i in range(offset, offset + size)]
            tape.append(observed("chance", {"arrange": {"order": order_ids}}))
            offset += size
    tape.extend(observed({"player": {"p": p}}, "mulliganDone") for p in order)
    tape.append(observed({"player": {"p": p0}}, "concede"))
    game = {"bo1Setup": originals, "decks": {"constructed": {"decks": submitted}},
            "answers": tape, "chooser": p0}
    inputs = {"config": setup["config"], "tournament": setup["tournament"],
              "winsRequired": 1, "fuel": 100, "games": [game], "ending": "finalGame"}
    source = folder / "bo1-input.json"
    archive = folder / "bo1-archive.json"
    trace = folder / "bo1-trace.json"
    source.write_text(json.dumps(inputs), encoding="utf-8")
    summary = json.loads(command("record", source, archive))
    assert summary["wins"] == [0, 1] and summary["exact"]
    assert json.loads(command("verify", archive)) == summary
    command("view", archive, trace)
    steps = json.loads(trace.read_text(encoding="utf-8"))["games"][0]["steps"]
    assert [step["action"]["kind"] for step in steps[1:4]] == ["pick", "pick", "arrangePlayers"]
    assert "p1.championZone" not in steps[3]["state"]["zones"]
    assert steps[4]["action"] is None and steps[4]["bo1Sideboard"]
    sideboard = steps[4]["state"]
    champion_id = sideboard["zones"]["p1.championZone"][0]
    assert sideboard["new"][str(champion_id)]["card"] == champion["code"]
    assert steps[3]["state"]["zones"]["battlefield"] == sideboard["zones"]["battlefield"]
    assert steps[5]["action"]["kind"] == "arrange"

    invalid = folder / "bo1-invalid.json"
    game["answers"] = tape[:3] + tape[4:]
    invalid.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", invalid, archive, error="close the Best of 1 sideboard window")
    game["answers"] = tape[:2] + ["bo1Sideboard", initiative] + tape[4:]
    invalid.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", invalid, archive, error="no Best of 1 sideboard window is open")
    game["answers"] = tape
    changed["sideboard"] = changed["sideboard"][:-1]
    invalid.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", invalid, archive, error="must sideboard from the registered pool")


def check_cli(folder: Path, saved: dict, setup: dict, group_move: dict, elimination: dict, bo1: dict,
              team_matches: dict[str, tuple[dict, list[int]]]) -> None:
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
    assert view["cardsFullyChecked"] and not any(saved["games"][0]["summary"]["uncheckedCards"])

    group_archive = folder / "group-move-archive.json"
    group_archive.write_text(json.dumps(group_move), encoding="utf-8")
    assert json.loads(command("verify", group_archive)) == group_move["summary"]
    group_trace = folder / "group-move-trace.json"
    command("view", group_archive, group_trace)
    group_steps = json.loads(group_trace.read_text(encoding="utf-8"))["games"][0]["steps"]
    checked_move = next(row for row in group_steps if (row["action"] or {}).get("groupMoveUnits"))
    assert len(checked_move["action"]["groupMoveUnits"]) == 2
    assert len([event for event in checked_move["events"] if event["t"] == "moved_unit"]) == 2

    elimination_archive = folder / "elimination-archive.json"
    elimination_archive.write_text(json.dumps(elimination), encoding="utf-8")
    assert json.loads(command("verify", elimination_archive)) == elimination["summary"]
    elimination_trace = folder / "elimination-trace.json"
    command("view", elimination_archive, elimination_trace)
    overtime = json.loads(elimination_trace.read_text(encoding="utf-8"))["games"][1]["steps"][-1]
    assert overtime["state"]["turn"] == 7
    assert any(event["t"] == "points" for event in overtime["events"])

    witness = saved["games"][0]["checkpoints"][2]
    witness["state"] = "0"
    corrupted = folder / "changed-checkpoint.json"
    corrupted.write_text(json.dumps(saved), encoding="utf-8")
    command("verify", corrupted, error="game 1: checkpoint 2")

    answers = saved["input"]["games"][0]["answers"]
    observed_action = answers[0]["observed"]["action"]
    answers[0] = {"inferred": {"action": observed_action, "evidence": "reconstructed from later evidence"}}
    source.write_text(json.dumps(saved["input"]), encoding="utf-8")
    inferred = json.loads(command("record", source, folder / "inferred.json"))
    assert not inferred["exact"] and inferred["cardsFullyChecked"]
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
                 observed({"player": {"p": p0}}, {"inviteTeammate": {"guest": p1}}),
                 observed({"player": {"p": p1}}, "pass"),
                 observed({"player": {"p": p1}}, "concede")],
    )
    team_record["winsRequired"] = 1
    team_input.write_text(json.dumps(team_record), encoding="utf-8")
    team_archive = folder / "team-archive.json"
    summary = json.loads(command("record-team", team_input, team_archive))
    assert summary["wins"] == [0, 1] and summary["exact"] and summary["cardsFullyChecked"]
    assert json.loads(command("verify-team", team_archive)) == summary
    team_trace = folder / "team-trace.json"
    command("view-team", team_archive, team_trace)
    exported = json.loads(team_trace.read_text(encoding="utf-8"))
    assert exported["teams"] == [[0, 1], [2, 3]] and exported["winner"] == 1
    assert exported["games"][0]["players"] == 4 and exported["exact"]
    steps = exported["games"][0]["steps"]
    assert any((row["action"] or {}).get("kind") == "inviteTeammate" for row in steps)

    order_input = folder / "team-opening-order.json"
    order_archive = folder / "team-opening-order-archive.json"
    order_trace = folder / "team-opening-order-trace.json"
    order_game = {**team_game, "openingOrderEvidence": {"inferred": {"evidence": "later turns show the order"}}}
    order_record = {**team_record, "games": [order_game]}
    order_input.write_text(json.dumps(order_record), encoding="utf-8")
    order_summary = json.loads(command("record-team", order_input, order_archive))
    assert order_summary == {**summary, "exact": False}
    assert json.loads(command("verify-team", order_archive)) == order_summary
    recorded_order = json.loads(order_archive.read_text(encoding="utf-8"))
    recorded_direct = json.loads(team_archive.read_text(encoding="utf-8"))
    assert recorded_order["games"][0]["checkpoints"] == recorded_direct["games"][0]["checkpoints"]
    command("view-team", order_archive, order_trace)
    assert not json.loads(order_trace.read_text(encoding="utf-8"))["exact"]
    order_game["openingOrderEvidence"] = {"inferred": {"evidence": "  "}}
    order_input.write_text(json.dumps(order_record), encoding="utf-8")
    command("record-team", order_input, order_archive, error="an inferred starting turn order needs an explanation")
    order_game.update(order=[], openingOrderEvidence={"unknown": {"description": "the opening was hidden"}})
    order_input.write_text(json.dumps(order_record), encoding="utf-8")
    command("record-team", order_input, order_archive,
            error="team game 1: starting turn order is unobserved: the opening was hidden")

    last = team_game["answers"][-1]["observed"]["action"]
    team_game["answers"][-1] = {"inferred": {"action": last, "evidence": "team reported the concession"}}
    team_game["decks"] = [{**decks[0], "sideboard": [*decks[0]["sideboard"], {"code": "OGN-001"}]},
                          *decks[1:]]
    inferred_team = folder / "team-inferred.json"
    inferred_team.write_text(json.dumps(team_record), encoding="utf-8")
    inferred_archive = folder / "team-inferred-archive.json"
    inferred_summary = json.loads(command("record-team", inferred_team, inferred_archive))
    assert not inferred_summary["exact"] and not inferred_summary["cardsFullyChecked"]
    assert json.loads(command("verify-team", inferred_archive)) == inferred_summary
    check_limited_cli(folder, setup, command)
    check_bo1_cli(folder, setup, command)
    live_archive = folder / "live-bo1-archive.json"
    live_archive.write_text(json.dumps(bo1), encoding="utf-8")
    live_summary = json.loads(command("verify", live_archive))
    assert live_summary["exact"] and live_summary["wins"] == [0, 1]
    live_trace = folder / "live-bo1-trace.json"
    command("view", live_archive, live_trace)
    steps = json.loads(live_trace.read_text(encoding="utf-8"))["games"][0]["steps"]
    assert steps[3]["bo1Initiative"] and steps[3]["action"]["turnOrder"] == [1, 0]
    assert steps[4]["bo1Sideboard"]
    for label, (team_archive, wins) in team_matches.items():
        archive = folder / f"{label}-archive.json"
        archive.write_text(json.dumps(team_archive), encoding="utf-8")
        team_summary = json.loads(command("verify-team", archive))
        assert team_summary["exact"] and team_summary["wins"] == wins
        trace = folder / f"{label}-trace.json"
        command("view-team", archive, trace)
        exported = json.loads(trace.read_text(encoding="utf-8"))
        assert exported["teams"] == [[0, 1], [2, 3]] and exported["wins"] == wins


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="keep the generated archive and viewer trace here")
    args = parser.parse_args()
    setup = json.loads((ROOT / "data/replay/constructed-example.json").read_text(encoding="utf-8"))
    live = Lean(ROOT / ".lake/build/bin/riftbound-live")
    try:
        saved = played_match(live, setup)
        check_match_endings(live, setup)
        group_move = group_move_match(live, setup)
        elimination = elimination_match(live, setup)
        bo1 = live_bo1_match(live, setup)
        team_matches = live_team_matches(live, setup)
    finally:
        live.close()
        live.proc.wait()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        check_cli(args.output, saved, setup, group_move, elimination, bo1, team_matches)
    else:
        with TemporaryDirectory() as folder:
            check_cli(Path(folder), saved, setup, group_move, elimination, bo1, team_matches)
    print("replay smoke: OK")


if __name__ == "__main__":
    main()
