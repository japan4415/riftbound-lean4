"""Exercise the real-card live protocol and replay CLI together."""

import argparse
import json
import subprocess
from collections.abc import Callable
from copy import deepcopy
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


def inspect_game(folder: Path, command: Callable[..., str], inputs: dict, game: int,
                 suffix: str = "", error: str | None = None) -> dict:
    source = folder / f"inspect{suffix}-input.json"
    output = folder / f"inspect{suffix}-result.json"
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("inspect" + suffix, source, str(game), output, error=error)
    return {} if error is not None else json.loads(output.read_bytes())


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
        assert exported["cards"]["TKN-LimitedBlank"]["name"] == "Blank Battlefield"

    draft_setup = {**setup, "config": duel["config"], "decks": duel["games"][0]["decks"],
                   "tournament": None, "winsRequired": 1}
    live = Lean(ROOT / ".lake/build/bin/riftbound-live")
    try:
        opened = ask(live, f"start-json 1 01 {json.dumps(draft_setup)}")
        assert "TKN-LimitedBlank" in opened["cards"]
        assert ask(live, "judge-game-loss 1")["archiveAvailable"]
        saved = ask(live, "replay")
    finally:
        live.close()
        live.proc.wait()
    archive = folder / "live-draft-archive.json"
    archive.write_text(json.dumps(saved), encoding="utf-8")
    assert json.loads(command("verify", archive)) == saved["summary"]
    command("view-seat", archive, "0", folder / "live-draft-seat.json")


def check_war_concession_cli(folder: Path, command: Callable[..., str]) -> None:
    source = ROOT / "data/replay/war-concession-example.json"
    archive = folder / "war-concession-archive.json"
    trace = folder / "war-concession-trace.json"
    summary = json.loads(command("record-ffa", source, archive))
    assert summary["exact"] and summary["cardsFullyChecked"]
    assert summary["result"] == {"won": {"winners": [{"n": 2}]}}
    assert summary["points"] == [0, 0, 1, 0]
    assert json.loads(command("verify-ffa", archive)) == summary
    check_revalidation(folder, command, archive, "-ffa", summary)

    command("view-ffa", archive, trace)
    exported = json.loads(trace.read_text(encoding="utf-8"))
    steps = exported["games"][0]["steps"]
    index = next(i for i, step in enumerate(steps)
                 if step["action"] == {"actor": "p1", "kind": "concede"})
    before, after, following = [step["state"] for step in steps[index - 1:index + 2]]
    assert before["pending"] == "showdown" and after["pending"] == "priority"
    assert after["departed"] == [1] and after["points"] == [0, 0, 1, 0]
    assert [field["id"] for field in before["battlefields"]] == [field["id"] for field in after["battlefields"]]
    assert before["at"] and after["at"] == before["at"]
    field = next(field["id"] for field in after["battlefields"] if field["control"] == 2)
    assert after["new"][str(field)]["card"] == "TKN-ConcessionBattlefield"
    assert following["turn"] == after["turn"] + 1 and following["active"] == 0
    inputs = json.loads(source.read_bytes())
    inputs["game"]["answers"] = inputs["game"]["answers"][:index - 1]
    inspection = inspect_game(folder, command, inputs, 1, "-ffa")
    assert inspection["checkpoint"] == index - 1 and inspection["nextAnswer"] == index
    answers = [choice["answer"] for choice in inspection["choices"]]
    assert observed({"player": {"p": {"n": 1}}}, "concede") in answers
    assert {**inspection["state"], "new": before["new"]} == before
    observation_source = folder / "war-observations.json"
    observation_archive = folder / "war-observations-archive.json"
    inputs = json.loads(source.read_bytes())
    cards = {obj: info for row in steps[:index + 1] for obj, info in row["state"]["new"].items()}
    field_owner = {"n": cards[str(field)]["owner"]}
    unit_ids = [unit for unit, at in after["at"] if at == field and cards[str(unit)]["owner"] == 2]
    unit_cards = [{"code": cards[str(unit)]["card"]} for unit in unit_ids]
    marked = dict(after["damaged"])
    unit_states = [{"card": card, "exhausted": unit in after["exhausted"], "damage": marked.get(unit, 0)}
                   for unit, card in zip(unit_ids, unit_cards)]
    assert unit_states
    unit_attachments = [{"unit": card, "attached": []} for card in unit_cards]
    field_ref = {"owner": field_owner, "field": {"code": "TKN-ConcessionBattlefield"},
                 "controller": {"n": 2}}
    inputs["game"]["observations"] = [{"checkpoint": index, "source": "after the concession",
                                      "facts": [
        {"battlefieldControl": field_ref},
        {"battlefieldUnits": {**field_ref, "cards": unit_cards}},
        {"unitStates": {"controller": {"n": 2}, "place": {"battlefield": {
            "owner": field_owner, "field": {"code": "TKN-ConcessionBattlefield"}}},
            "units": list(reversed(unit_states))}},
        {"unitAttachments": {"controller": {"n": 2}, "place": {"battlefield": {
            "owner": field_owner, "field": {"code": "TKN-ConcessionBattlefield"}}},
            "units": unit_attachments}},
        {"score": {"seat": {"n": 2}, "points": 1}},
    ]}]
    observation_source.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record-ffa", observation_source, observation_archive)) == summary
    assert json.loads(command("verify-ffa", observation_archive)) == summary
    unit_states[0]["damage"] += 1
    observation_source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record-ffa", observation_source, observation_archive,
            error=f"seat 2 Units at Battlefield TKN-ConcessionBattlefield from seat {field_owner['n']}")
    unit_states[0]["damage"] -= 1
    unit_attachments[0]["attached"].append({"code": "SFD-009"})
    observation_source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record-ffa", observation_source, observation_archive,
            error=f"seat 2 Units at Battlefield TKN-ConcessionBattlefield from seat {field_owner['n']} attachments")
    unit_attachments[0]["attached"].clear()
    field_ref["controller"] = {"n": 0}
    observation_source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record-ffa", observation_source, observation_archive,
            error=f"game 1: checkpoint {index}: observation")
    check_seat_disclosures(folder, command, archive, "-ffa", 3, exported["games"])
    seat_steps = check_seat_view(folder, command, archive, "-ffa", 3, exported["games"])["games"][0]["steps"]
    seat_board = seat_steps[index]["state"]["zones"]["battlefield"]
    assert any(card["card"] == "TKN-ConcessionBattlefield" and card["control"] == 2
               for card in seat_board)


def check_lux_spell_energy_cli(folder: Path, command: Callable[..., str]) -> None:
    source = ROOT / "data/replay/lux-spell-energy-example.json"
    archive = folder / "lux-spell-energy-archive.json"
    trace = folder / "lux-spell-energy-trace.json"
    summary = json.loads(command("record", source, archive))
    assert summary["exact"] and summary["cardsFullyChecked"] and summary["wins"] == [1, 0]
    assert json.loads(command("verify", archive)) == summary

    command("view", archive, trace)
    steps = json.loads(trace.read_text(encoding="utf-8"))["games"][0]["steps"]
    add_index = next(i for i, row in enumerate(steps)
                     if (row["action"] or {}).get("spellEnergyAdded") == 2)
    gained, spent = steps[add_index:add_index + 2]
    assert gained["state"]["pools"][0]["energy"] == 0
    assert gained["state"]["pools"][0]["spellEnergy"] == 2
    assert spent["action"]["kind"] == "playCard" and spent["action"]["pay"] == 2
    assert spent["state"]["pools"][0].get("spellEnergy", 0) == 0

    inputs = json.loads(source.read_bytes())
    game = inputs["games"][0]
    tape = game["answers"]
    game["answers"] = tape[:add_index]
    inspection = inspect_game(folder, command, inputs, 1)
    coded, = (choice["answerByCode"] for choice in inspection["choices"]
              if choice["answer"] == tape[add_index])
    play = coded["observedCardPlay"]["play"]
    assert play["source"]["card"]["code"] == "RAD-010" and len(play["targets"]) == 1
    game["answers"] = [*tape[:add_index], coded, *tape[add_index + 1:]]
    transcription = folder / "lux-spell-by-code-input.json"
    recoded = folder / "lux-spell-by-code-archive.json"
    transcription.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", transcription, recoded)) == summary
    assert json.loads(recoded.read_bytes())["games"][0]["checkpoints"] == (
        json.loads(archive.read_bytes())["games"][0]["checkpoints"]
    )
    game["answers"][add_index] = {"inferredCardPlay": {"play": play, "evidence": "recorded Rune Pool"}}
    assert not inspect_game(folder, command, inputs, 1)["exactPrefix"]
    wrong = {**play, "payment": {**play["payment"], "energy": 3}}
    game["answers"][add_index] = {"observedCardPlay": {"play": wrong}}
    inspect_game(folder, command, inputs, 1, error="no legal play of RAD-010")


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
    champions = [[seat, state["zones"][f"p{seat}.championZone"][0]] for seat in (0, 1)]
    assert state["new"][str(champion_id)]["card"] == changed["deck"]["chosenChampion"]["code"]
    assert all(f"p{seat}.hand" not in state["zones"] for seat in (0, 1))
    assert confirmed["steps"][1]["action"]["kind"] == "arrange"
    assert ask(live, "undo")["bo1"] == swapped["bo1"]
    assert ask(live, "bo1-sideboard") == confirmed
    assert "cannot be used now" in json.loads(live.ask(register))["error"]
    final = choose(live, keep(live, confirmed), "concede", "p0")
    assert final["archiveAvailable"] and final["match"]["winner"] == 1
    archive = ask(live, "replay")
    checkpoints = archive["games"][0]["checkpoints"]
    assert all(checkpoint["chosenChampions"] == [] for checkpoint in checkpoints[:4])
    assert all(checkpoint["chosenChampions"] == champions for checkpoint in checkpoints[4:])
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


def live_judge_penalties(live: Lean, setup: dict) -> dict:
    team = json.loads((ROOT / "data/replay/team-constructed-example.json").read_text(encoding="utf-8"))
    duel_start = f"start-json 71 01 {json.dumps(setup)}"
    team_start = f"start-team-json 71 0123 {json.dumps(team)}"

    keep(live, ask(live, duel_start))
    assert "distinct registered seats" in json.loads(live.ask("judge-game-loss 11"))["error"]
    loss = ask(live, "judge-game-loss 1")
    assert loss["steps"][0]["gameLoss"] == [1] and loss["match"]["wins"] == [1, 0]
    assert ask(live, "next")["choice"] == 1
    keep(live, ask(live, "next first"))
    assert ask(live, "judge-game-loss 1")["archiveAvailable"]
    duel = ask(live, "replay")
    previous, next_game = [game["summary"]["battlefields"] for game in duel["games"]]
    assert len(previous) == len(next_game) == 2
    assert all(pair not in previous for pair in next_game)

    keep(live, ask(live, team_start))
    drawn = ask(live, "judge-game-loss 0123")
    assert drawn["match"]["wins"] == [0, 0] and not drawn["match"]["sameBattlefields"]
    keep(live, ask(live, "team-next"))
    assert ask(live, "judge-game-loss 3")["match"]["wins"] == [1, 0]
    assert ask(live, "judge-game-loss 3")["steps"] == []
    queued = ask(live, "team-next 1302")
    assert queued["archiveAvailable"] and len(queued["steps"]) == 2 and queued["steps"][1]["gameLoss"] == [3]
    team_game_loss = ask(live, "replay")
    games = team_game_loss["input"]["games"]
    assert games[0]["ending"] == {"gameLoss": {"seats": [{"n": i} for i in range(4)]}}
    assert games[0]["order"] == games[1]["order"]
    assert all(pair not in games[0]["battlefields"] for pair in games[1]["battlefields"])
    assert games[2]["battlefields"] == [] and len(games[2]["answers"]) == 1

    keep(live, ask(live, team_start))
    assert ask(live, "judge-match-loss 3")["match"]["winner"] == 0
    match_loss = ask(live, "replay")
    assert match_loss["input"]["ending"] == {"matchLoss": {"seat": {"n": 3}}}
    assert match_loss["input"]["games"][0]["ending"] == "matchEnded"

    keep(live, ask(live, duel_start))
    assert ask(live, "judge-disqualification 0")["match"]["winner"] == 1
    disqualification = ask(live, "replay")
    assert disqualification["input"]["ending"] == {"disqualification": {"seat": {"n": 0}}}
    return {"live-duel-game-loss": (duel, ""), "live-team-game-loss": (team_game_loss, "-team"),
            "live-team-match-loss": (match_loss, "-team"), "live-duel-disqualification": (disqualification, "")}


def live_judge_corrections(live: Lean, setup: dict) -> dict:
    team = json.loads((ROOT / "data/replay/team-constructed-example.json").read_text(encoding="utf-8"))
    fixtures = {}
    for label, source, seats, config, suffix in (
        ("duel", "start-json", "01", {**setup, "winsRequired": 1}, ""),
        ("team", "start-team-json", "0123", team, "-team"),
    ):
        opened = keep(live, ask(live, f"{source} 71 {seats} {json.dumps(config)}"))
        target = opened["steps"][-1]
        assert "earlier checkpoint" in json.loads(live.ask(f"judge-rewind {target['i']}"))["error"]
        progressed = choose(live, opened, "pass")
        assert progressed["steps"][-1]["state"]["turn"] > target["state"]["turn"]
        rewound = ask(live, f"judge-rewind {target['i']}")
        row = rewound["steps"][0]
        assert row["judgeRewind"] == target["i"] and row["action"] is None and row["events"] == []
        assert {key: value for key, value in row["state"].items() if key != "new"} == {
            key: value for key, value in target["state"].items() if key != "new"
        }
        assert row["state"]["new"]

        def apply_shuffle(deck: str) -> None:
            before = row["state"]["zones"][f"p0.{deck}"]
            change = {"seat": {"n": 0}, "deck": deck, "positions": [0, 2],
                      "order": [{"n": before[2]}, {"n": before[0]}]}
            replacing = {**change, "order": [{"n": before[1]}, {"n": before[0]}]}
            assert "keep exactly the objects" in json.loads(live.ask(f"judge-shuffle {json.dumps(replacing)}"))["error"]
            duplicate = {**change, "positions": [0, 0]}
            assert "strictly increasing" in json.loads(live.ask(f"judge-shuffle {json.dumps(duplicate)}"))["error"]
            shuffled = ask(live, f"judge-shuffle {json.dumps(change)}")["steps"][0]
            assert shuffled["judgeShuffle"] == change and shuffled["action"] is None and shuffled["events"] == []
            after = shuffled["state"]["zones"][f"p0.{deck}"]
            assert after == [before[2], before[1], before[0], *before[3:]]
            assert "without crossing" in json.loads(live.ask(f"judge-rewind {target['i']}"))["error"]

        apply_shuffle("mainDeck")
        apply_shuffle("runeDeck")
        if suffix:
            assert ask(live, "judge-match-loss 3")["archiveAvailable"]
        else:
            assert ask(live, "judge-game-loss 1")["archiveAvailable"]
        fixtures[label] = (ask(live, "replay"), suffix, target["i"])
    return fixtures


def check_judge_corrections(folder: Path, command: Callable[..., str], fixtures: dict) -> None:
    for label, (archive, suffix, target) in fixtures.items():
        path = folder / f"judge-{label}-corrections-archive.json"
        path.write_text(json.dumps(archive), encoding="utf-8")
        assert json.loads(command("verify" + suffix, path))["exact"]
        trace_path = folder / f"judge-{label}-corrections-trace.json"
        command("view" + suffix, path, trace_path)
        steps = json.loads(trace_path.read_text(encoding="utf-8"))["games"][0]["steps"]
        rewind_step = next(step for step in steps if "judgeRewind" in step)
        witness = archive["games"][0]["checkpoints"]
        assert rewind_step["judgeRewind"] == target and witness[target]["state"] == witness[rewind_step["i"]]["state"]
        remedies = [step for step in steps if step.get("judgeShuffle")]
        assert [step["judgeShuffle"]["deck"] for step in remedies] == ["mainDeck", "runeDeck"]
        assert all(not row["events"] for row in remedies)


def live_private_rewinds(live: Lean, setup: dict) -> dict:
    team = json.loads((ROOT / "data/replay/team-constructed-example.json").read_text(encoding="utf-8"))
    fixtures = {}

    def obj(ident: int) -> dict:
        return {"n": ident}

    for label, source, humans, config, suffix in (
        ("duel", "start-json", "01", {**setup, "winsRequired": 1}, ""),
        ("team", "start-team-json", "0123", team, "-team"),
    ):
        started = ask(live, f"{source} 71 {humans} {json.dumps(config)}")
        ready = keep(live, started)
        target = ready["steps"][-1]
        catalog = {key: data["card"] for step in started["steps"] + ready["steps"]
                   for key, data in step["state"]["new"].items()}
        after = choose(live, ready, "pass")
        seat = after["steps"][-1]["state"]["active"]
        previous = target["state"]["zones"]
        deck, hand = (previous[f"p{seat}.{zone}"] for zone in ("mainDeck", "hand"))
        first_draw = next(event["new"] for step in after["steps"] for event in step["events"]
                          if event["t"] == "moved" and event["dst"] == f"p{seat}.hand" and event["old"] == deck[0])
        declared = {"target": target["i"], "returns": [
            {"drawn": obj(first_draw), "candidates": list(map(obj, [deck[0], hand[0]])), "returned": obj(hand[0])}
        ]}
        final_draw = deck[0]
        expected_deck = [hand[0], *deck[1:]]
        if not suffix:
            after = choose(live, choose(live, after, "pass"), "pass")
            second_draw = next(event["new"] for step in after["steps"] for event in step["events"]
                               if event["t"] == "moved" and event["dst"] == f"p{seat}.hand" and event["old"] == deck[1])
            declared["returns"].append({"drawn": obj(second_draw), "candidates": list(map(obj, deck[:2])),
                                        "returned": obj(deck[0])})
            recent = {"target": target["i"], "returns": declared["returns"][1:]}
            restored = ask(live, f"judge-private-rewind {json.dumps(recent)}")["steps"][0]["state"]["zones"]
            assert restored[f"p{seat}.mainDeck"] == [deck[1], deck[0], *deck[2:]]
            assert restored[f"p{seat}.hand"] == hand
            ask(live, "undo")
            # The first drawn card is already back in the deck after reversing the second draw.
            assert "candidates must be distinct" in json.loads(
                live.ask(f"judge-private-rewind {json.dumps(declared)}"))["error"]
            declared["returns"][0]["candidates"][0] = obj(deck[1])
            declared["shuffles"] = [{"seat": obj(seat), "deck": "mainDeck", "positions": [0, 2],
                                     "order": [obj(deck[2]), obj(hand[0])]}]
            final_draw = deck[1]
            expected_deck = [deck[2], deck[0], hand[0], *deck[3:]]

        illegal = {**declared, "returns": [{**declared["returns"][0], "drawn": obj(99999)}]}
        assert "distinct undone draw" in json.loads(live.ask(f"judge-private-rewind {json.dumps(illegal)}"))["error"]
        illegal = {**declared, "returns": [{**declared["returns"][0], "candidates": [obj(deck[3])]}]}
        assert "candidates must be distinct" in json.loads(live.ask(f"judge-private-rewind {json.dumps(illegal)}"))["error"]
        corrected = ask(live, f"judge-private-rewind {json.dumps(declared)}")
        row = corrected["steps"][0]
        assert row["judgeRewind"] == target["i"] and row["privateDrawReturns"] == len(declared["returns"])
        assert row["rewindShuffles"] == len(declared.get("shuffles", [])) and row["events"] == []
        assert row["state"]["turn"] == target["state"]["turn"]
        actual = row["state"]["zones"]
        fresh = row["state"]["new"]
        for zone, expected in (("mainDeck", expected_deck), ("hand", [final_draw, *hand[1:]])):
            assert [fresh[str(i)]["card"] for i in actual[f"p{seat}.{zone}"]] == [
                catalog[str(i)] for i in expected
            ]
        end = "judge-match-loss 3" if suffix else "judge-game-loss 1"
        assert ask(live, end)["archiveAvailable"]
        fixtures[label] = (ask(live, "replay"), suffix, row)
    return fixtures


def reach_captain_look(live: Lean, setup: dict) -> tuple[dict, dict, dict, dict, int]:
    first, second = setup["decks"]["constructed"]["decks"]
    main = [{"code": "RAD-129"} if card["code"] == "RAD-119" else card for card in first["deck"]["main"]]
    captain_deck = {**first, "deck": {**first["deck"], "main": main}}
    config = {**setup, "winsRequired": 1, "decks": {"constructed": {"decks": [captain_deck, second]}}}
    response = start(live, config)
    captain_cards = set()
    catalog = {}
    history = {}
    for _ in range(45):
        steps = response["steps"]
        for row in steps:
            history[row["i"]] = row
            catalog.update((int(ident), obj["card"]) for ident, obj in row["state"]["new"].items())
            captain_cards.update(int(ident) for ident, obj in row["state"]["new"].items()
                                 if obj["card"] == "RAD-129")
        if any(event["t"] == "looked_at" for row in steps for event in row["events"]):
            break
        actions = response["legal"]
        preferred = next((a for a in actions if a["a"]["kind"] == "playCard"
                          and a["a"]["card"] in captain_cards), None)
        preferred = preferred or next((a for a in actions if a["a"]["actor"] == "p0"
                                       and a["a"]["kind"] == "runeAbility" and a["a"].get("ability") == "exhaust"), None)
        if preferred:
            response = ask(live, f"act {preferred['k']}")
        elif any(a["a"]["kind"] == "mulliganDone" for a in actions):
            response = choose(live, response, "mulliganDone")
        else:
            response = choose(live, response, "pass")
    else:
        raise AssertionError("Trifarian Captain did not look at the deck")

    looked_row, look_index, looked = next(
        (row, index, event["card"]) for row in response["steps"]
        for index, event in enumerate(row["events"]) if event["t"] == "looked_at"
    )
    assert {"event": look_index, "onlyFor": 0, "cards": [catalog[looked]]} in looked_row["disclosures"]
    return response, catalog, history[looked_row["i"] - 1], looked_row, looked


def live_undrawn_deck_rewind(live: Lean, setup: dict) -> tuple[dict, str, dict]:
    _, _, target, looked_row, looked = reach_captain_look(live, setup)
    deck = target["state"]["zones"]["p0.mainDeck"]
    seen = [event["card"] for event in looked_row["events"] if event["t"] == "looked_at"]
    positions = [deck.index(card) for card in seen]
    assert seen[0] == looked and positions == [0, 1, 2, 3]
    assert looked_row["state"]["zones"]["p0.mainDeck"] == deck

    def shuffle(positions: list[int]) -> dict:
        return {"seat": {"n": 0}, "deck": "mainDeck", "positions": positions,
                "order": [{"n": deck[index]} for index in reversed(positions)]}

    def private(**remedy: object) -> str:
        return f"judge-private-rewind {json.dumps(dict(target=target['i'], returns=[], **remedy))}"

    missing = "must shuffle deck cards seen without drawing or channeling them"
    assert missing in json.loads(live.ask(f"judge-rewind {target['i']}"))["error"]
    assert missing in json.loads(live.ask(private(shuffles=[shuffle([1, 2])])))["error"]
    assert missing in json.loads(
        live.ask(private(shuffles=[shuffle([index]) for index in positions])))["error"]
    wrong_deck = {"seat": {"n": 1}, "deck": "mainDeck"}
    assert "must contain a card affected" in json.loads(
        live.ask(private(unshuffledDecks=[wrong_deck])))["error"]

    remedy = shuffle([*positions, 4])
    restored = ask(live, private(shuffles=[remedy]))["steps"][0]
    assert restored["rewindShuffles"] == 1 and restored["privateDrawReturns"] == 0
    assert restored["state"]["zones"]["p0.mainDeck"] == [*reversed(deck[:5]), *deck[5:]]

    def timeline(**additional: object) -> str:
        payload = dict(target=target["i"], rulings=[restored["i"]], **additional)
        return f"judge-timeline-rewind {json.dumps(payload)}"

    # Undoing the earlier correction restores the order the player learned on the abandoned line.
    assert missing in json.loads(live.ask(timeline()))["error"]
    row = ask(live, timeline(shuffles=[remedy]))["steps"][0]
    assert row["rewindRulings"] == 1 and row["state"]["zones"] == restored["state"]["zones"]
    assert ask(live, "judge-game-loss 1")["archiveAvailable"]
    return ask(live, "replay"), "", row


def live_revealed_draw_rewind(live: Lean, setup: dict) -> tuple[dict, str, dict]:
    response, catalog, _, _, _ = reach_captain_look(live, setup)
    target = response["steps"][-1]
    assert target["state"]["active"] == 0
    deck = target["state"]["zones"]["p0.mainDeck"]
    hand = target["state"]["zones"]["p0.hand"]
    yes = next(action for action in response["legal"] if action["a"].get("yes") is True)
    chosen = choose(live, ask(live, f"act {yes['k']}"), "choose", "p0")
    events = [event for row in chosen["steps"] for event in row["events"]]
    reveal_row, reveal_index, revealed = next(
        (row, index, event["card"]) for row in chosen["steps"]
        for index, event in enumerate(row["events"]) if event["t"] == "revealed"
    )
    assert {"event": reveal_index, "onlyFor": None, "cards": [catalog[revealed]]} in reveal_row["disclosures"]
    public_draw = next(event["new"] for event in events if event["t"] == "moved"
                       and event["old"] == revealed and event["dst"] == "p0.hand")
    unknown = chosen["steps"][-1]["state"]["zones"]["p0.mainDeck"][0]
    later = choose(live, choose(live, chosen, "pass", "p0"), "pass", "p1")
    hidden_draw = next(event["new"] for row in later["steps"] for event in row["events"]
                       if event["t"] == "moved" and event["old"] == unknown and event["dst"] == "p0.hand")

    def record(drawn: int, candidates: list[int], returned: int, checkpoint: int = target["i"]) -> str:
        payload = {"target": checkpoint, "returns": [{"drawn": {"n": drawn},
                   "candidates": [{"n": card} for card in candidates], "returned": {"n": returned}}]}
        return f"judge-private-rewind {json.dumps(payload)}"

    assert "publicly revealed" in json.loads(live.ask(record(public_draw, [hand[0]], hand[0])))["error"]
    assert "candidates must be distinct" in json.loads(live.ask(record(hidden_draw, [revealed], revealed)))["error"]
    earlier_public = record(hidden_draw, [public_draw], public_draw, chosen["steps"][-1]["i"])
    assert "candidates must be distinct" in json.loads(live.ask(earlier_public))["error"]
    row = ask(live, record(hidden_draw, [unknown, hand[0]], hand[0]))["steps"][0]
    restored = row["state"]["zones"]
    metadata = row["state"]["new"]
    assert restored["p0.mainDeck"][deck.index(revealed)] == revealed
    restored_top = restored["p0.mainDeck"][deck.index(unknown)]
    assert restored_top != unknown and metadata[str(restored_top)]["card"] == catalog[hand[0]]
    assert restored["p0.hand"][0] != hand[0]
    assert metadata[str(restored["p0.hand"][0])]["card"] == catalog[unknown]
    assert ask(live, "judge-game-loss 1")["archiveAvailable"]
    return ask(live, "replay"), "", row


def check_seat_disclosures(folder: Path, command: Callable[..., str], archive: Path,
                           suffix: str, seat: int, games: list[dict]) -> None:
    path = folder / f"{archive.stem}-seat-{seat}-disclosures.json"
    command("disclosures" + suffix, archive, str(seat), path)
    selected = []
    for game in games:
        steps = []
        for row in game["steps"]:
            visible = [{"cards": entry["cards"], "public": entry["onlyFor"] is None}
                       for entry in row.get("disclosures", []) if entry["onlyFor"] in (None, seat)]
            if visible:
                steps.append({"i": row["i"], "disclosures": visible})
        selected.append({"steps": steps})
    assert json.loads(path.read_text(encoding="utf-8")) == {"seat": seat, "exact": True, "games": selected}


def check_seat_view(folder: Path, command: Callable[..., str], archive: Path,
                    suffix: str, seat: int, games: list[dict]) -> dict:
    path = folder / f"{archive.stem}-seat-{seat}-view.json"
    command(f"view{suffix}-seat", archive, str(seat), path)
    view = json.loads(path.read_text(encoding="utf-8"))
    assert view["seat"] == seat and view["exact"]
    assert len(view["games"]) == len(games)
    for game, full_game in zip(view["games"], games, strict=True):
        for row, full_row in zip(game["steps"], full_game["steps"], strict=True):
            assert row["i"] == full_row["i"]
            assert row.get("judgeRewind") == full_row.get("judgeRewind")
            assert not {"action", "events", "judgeShuffle", "privateDrawReturns"} & row.keys()
            state, full_state = row["state"], full_row["state"]
            for field in ("turn", "phase", "active", "result", "points", "pools", "xp"):
                assert state[field] == full_state[field]
            assert state["departed"] == full_state.get("departed", [])
            assert not {"new", "pending"} & state.keys()
            for zone, cards in state["zones"].items():
                assert len(cards) == len(full_state["zones"].get(zone, []))
            known = [{"cards": entry["cards"], "public": entry["onlyFor"] is None}
                     for entry in full_row.get("disclosures", []) if entry["onlyFor"] in (None, seat)]
            assert row.get("disclosures", []) == known
    return view


def check_disclosure_observations(folder: Path, command: Callable[..., str], archive: dict,
                                  steps: list[dict], looked: int, revealed: int) -> None:
    source = folder / "disclosure-observations-input.json"
    output = folder / "disclosure-observations-archive.json"
    inputs = json.loads(json.dumps(archive["input"]))
    game = inputs["games"][0]
    observations = []
    for checkpoint, audience in ((looked, 0), (revealed, None)):
        evidence = [row for row in steps[checkpoint]["disclosures"] if row["onlyFor"] == audience]
        assert evidence and all(row["cards"] for row in evidence)
        disclosures = [{"onlyFor": None if audience is None else {"n": audience},
                        "cards": [{"code": code} for code in row["cards"]]}
                       for row in evidence]
        observations.append({"checkpoint": checkpoint - 1, "through": checkpoint,
                             "facts": [{"disclosuresInOrder": {"disclosures": disclosures}}]})
    game["observations"] = observations
    source.write_text(json.dumps(inputs), encoding="utf-8")
    summary = json.loads(command("record", source, output))
    assert summary["exact"] and json.loads(command("verify", output)) == summary
    assert json.loads(output.read_text(encoding="utf-8"))["games"][0]["checkpoints"] == (
        archive["games"][0]["checkpoints"])

    private = observations[0]["facts"][0]["disclosuresInOrder"]["disclosures"][0]
    private["onlyFor"] = {"n": 1}
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, output, error="card disclosures did not occur")
    private["onlyFor"] = None
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, output, error="card disclosures did not occur")


def check_private_rewinds(folder: Path, command: Callable[..., str], fixtures: dict) -> None:
    for label, (archive, suffix, live_row) in fixtures.items():
        path = folder / f"judge-{label}-private-rewind-archive.json"
        path.write_text(json.dumps(archive), encoding="utf-8")
        assert json.loads(command("verify" + suffix, path))["exact"]
        trace = folder / f"judge-{label}-private-rewind-trace.json"
        command("view" + suffix, path, trace)
        games = json.loads(trace.read_text(encoding="utf-8"))["games"]
        steps = games[0]["steps"]
        assert steps[live_row["i"]] == live_row
        if label == "revealed-draw":
            assert not live_row.get("disclosures")
            check_seat_disclosures(folder, command, path, suffix, 0, games)
            check_seat_disclosures(folder, command, path, suffix, 1, games)
            command("disclosures", path, "2", folder / "bad-seat.json", error="outside the game")
            command("view-seat", path, "2", folder / "bad-view-seat.json", error="outside the game")
            p0 = check_seat_view(folder, command, path, suffix, 0, games)["games"][0]["steps"]
            p1 = check_seat_view(folder, command, path, suffix, 1, games)["games"][0]["steps"]
            looked = next(row["i"] for row in steps if any(d["onlyFor"] == 0
                          for d in row.get("disclosures", [])))
            inspected = {card for d in p0[looked]["disclosures"] if not d["public"]
                         for card in d["cards"]}
            assert p0[looked]["state"]["zones"]["p0.mainDeck"][0]["card"] in inspected
            assert all(slot is None for slot in p1[looked]["state"]["zones"]["p0.mainDeck"])
            assert all(slot is None for slot in p1[looked]["state"]["zones"]["p0.hand"])
            revealed = next(row["i"] for row in steps if any(d["onlyFor"] is None
                            for d in row.get("disclosures", [])))
            published = {card for d in p1[revealed]["disclosures"] if d["public"] for card in d["cards"]}
            assert published and published <= inspected
            check_disclosure_observations(folder, command, archive, steps, looked, revealed)
            rewind = p1[live_row["i"]]
            assert rewind["judgeRewind"] < rewind["i"]
            assert all(slot is None for slot in rewind["state"]["zones"]["p0.hand"])
        if label == "undrawn-look":
            p0 = check_seat_view(folder, command, path, suffix, 0, games)["games"][0]["steps"]
            p1 = check_seat_view(folder, command, path, suffix, 1, games)["games"][0]["steps"]
            look = next(row["i"] for row in steps if any(d["onlyFor"] == 0 for d in row.get("disclosures", [])))
            assert p0[look]["disclosures"] and not p1[look].get("disclosures")
            for seat in (p0, p1):
                assert all(slot is None for slot in seat[live_row["i"]]["state"]["zones"]["p0.mainDeck"])
            corrupted = json.loads(json.dumps(archive["input"]))
            last_correction = corrupted["games"][0]["answers"][live_row["i"] - 1]
            last_correction["judgeTimelineRewind"]["rewind"]["shuffles"] = []
            input_path = folder / "undrawn-look-missing-shuffle.json"
            input_path.write_text(json.dumps(corrupted), encoding="utf-8")
            command("record", input_path, folder / "invalid-rewind.json",
                    error="must shuffle deck cards seen without drawing or channeling them")


def live_timeline_rewinds(live: Lean, setup: dict) -> dict:
    def rewind(payload: dict) -> str:
        return f"judge-timeline-rewind {json.dumps(payload)}"

    ready = keep(live, ask(live, f"start-json 71 01 {json.dumps({**setup, 'winsRequired': 1})}"))
    target = ready["steps"][-1]
    advanced = choose(live, ready, "pass")
    assert advanced["steps"][-1]["state"]["turn"] == 2
    assert "cannot add a time call" in json.loads(live.ask(rewind({"target": target["i"], "deadline": 4})))["error"]
    clock = ask(live, "clock")
    assert "final scheduled turn" in json.loads(live.ask(rewind({"target": target["i"]})))["error"]
    assert "precedes the restored turn" in json.loads(live.ask(rewind({"target": target["i"], "deadline": 0})))["error"]
    assert "without crossing" in json.loads(live.ask(f"judge-rewind {target['i']}"))["error"]

    deck_top = target["state"]["zones"]["p1.mainDeck"][0]
    other_hand = target["state"]["zones"]["p1.hand"][0]
    drawn = next(event["new"] for event in advanced["steps"][-1]["events"]
                 if event["t"] == "moved" and event["dst"] == "p1.hand" and event["old"] == deck_top)
    payload = {"target": target["i"], "deadline": 4, "returns": [
        {"drawn": {"n": drawn}, "candidates": [{"n": deck_top}, {"n": other_hand}], "returned": {"n": other_hand}}
    ]}
    current = ask(live, rewind(payload))
    swiss = current["steps"][0]
    assert swiss["rewindDeadline"] == 4 and swiss["privateDrawReturns"] == 1
    assert swiss["state"]["turn"] == target["state"]["turn"] and not current["external"]["clock"]
    for _ in range(12):
        if current["over"]:
            break
        current = choose(live, current, "pass")
    assert current["archiveAvailable"] and current["steps"][-1]["state"]["turn"] == 4
    assert not clock["external"]["clock"]
    duel = ask(live, "replay")
    assert duel["games"][0]["summary"]["timed"] and duel["summary"]["result"] == "draw"

    team = json.loads((ROOT / "data/replay/team-constructed-example.json").read_text(encoding="utf-8"))
    team["singleElimination"] = True
    ready = keep(live, ask(live, f"start-team-json 71 0123 {json.dumps(team)}"))
    target = ready["steps"][-1]
    origin = target["state"]["zones"]["p1.mainDeck"]
    shuffle = {"seat": {"n": 1}, "deck": "mainDeck", "positions": [0, 1], "order": [{"n": origin[1]}, {"n": origin[0]}]}
    current = ask(live, f"judge-shuffle {json.dumps(shuffle)}")
    sh = current["steps"][0]["i"]
    restored = ask(live, rewind({"target": target["i"], "rulings": [sh]}))
    assert restored["steps"][0]["state"]["zones"]["p1.mainDeck"] == origin
    assert restored["external"]["clock"] and "rewindDeadline" not in restored["steps"][0]
    ask(live, "undo")
    advanced = choose(live, current, "pass")["steps"][-1]
    clock = ask(live, "clock")["steps"][-1]
    first = ask(live, rewind({"target": advanced["i"], "deadline": 5}))["steps"][0]
    assert first["state"]["eliminationDeadline"] == 5
    assert "abandoned" in json.loads(live.ask(rewind({"target": clock["i"], "deadline": 5})))["error"]
    assert "each reversed ruling" in json.loads(live.ask(rewind({"target": target["i"], "deadline": 6})))["error"]
    assert "final scheduled turn" in json.loads(live.ask(rewind({"target": target["i"], "rulings": [first["i"], sh]})))["error"]
    current = ask(live, rewind({"target": target["i"], "deadline": 6, "rulings": [first["i"], sh]}))
    second = current["steps"][0]
    assert second["rewindRulings"] == 2 and second["state"]["eliminationDeadline"] == 6
    assert second["state"]["zones"]["p1.mainDeck"] == origin
    assert not current["external"]["clock"]
    assert ask(live, "judge-match-loss 3")["archiveAvailable"]
    archive = ask(live, "replay")
    assert archive["games"][0]["summary"]["timed"]
    return {"swiss": (duel, "", swiss), "elimination": (archive, "-team", second)}


def check_timeline_rewinds(folder: Path, command: Callable[..., str], fixtures: dict) -> None:
    for label, (archive, suffix, live_row) in fixtures.items():
        path = folder / f"judge-{label}-timeline-archive.json"
        path.write_text(json.dumps(archive), encoding="utf-8")
        assert json.loads(command("verify" + suffix, path))["exact"]
        trace = folder / f"judge-{label}-timeline-trace.json"
        command("view" + suffix, path, trace)
        steps = json.loads(trace.read_text(encoding="utf-8"))["games"][0]["steps"]
        assert steps[live_row["i"]] == live_row
        assert any((step.get("action") or {}).get("kind") == "timeCalled" for step in steps)


def check_judge_penalties(folder: Path, command: Callable[..., str], fixtures: dict) -> None:
    for label, (archive, suffix) in fixtures.items():
        path = folder / f"{label}-archive.json"
        path.write_text(json.dumps(archive), encoding="utf-8")
        assert json.loads(command("verify" + suffix, path))["exact"]
        trace = folder / f"{label}-trace.json"
        command("view" + suffix, path, trace)
        exported = json.loads(trace.read_text(encoding="utf-8"))
        if "game-loss" in label:
            assert all(game["steps"][-1]["gameLoss"] for game in exported["games"])
        else:
            assert exported["matchPenalty"] == archive["input"]["ending"]

    duel = fixtures["live-duel-game-loss"][0]["input"]
    previous = [answer for answer in duel["games"][0]["answers"]
                if isinstance(answer, dict) and "pick" in answer.get("observed", {}).get("action", {}).get("kind", {})]
    assert len(previous) == 2
    second = duel["games"][1]["answers"]
    picks = [index for index, answer in enumerate(second)
             if isinstance(answer, dict) and "pick" in answer.get("observed", {}).get("action", {}).get("kind", {})]
    for index, answer in zip(picks, previous, strict=True):
        second[index] = answer
    invalid = folder / "penalized-battlefield-reuse.json"
    invalid.write_text(json.dumps(duel), encoding="utf-8")
    command("record", invalid, folder / "invalid-penalty-archive.json", error="different Battlefield after a Game Loss")


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

    unfinished = {key: value for key, value in inputs.items() if key != "ending"}
    game["answers"] = tape[:2]
    inspection = inspect_game(folder, command, unfinished, 1)
    assert inspection["decision"]["bo1Initiative"] and inspection["decision"]["chooser"] == p0
    assert initiative in [choice["answer"] for choice in inspection["choices"]]
    game["answers"] = tape[:3]
    inspection = inspect_game(folder, command, unfinished, 1)
    assert inspection["decision"] == {"kind": "bo1Sideboard", "answer": "bo1Sideboard"}
    assert inspection["nextAnswer"] == 4

    game["answers"] = tape[:8]
    inspection = inspect_game(folder, command, unfinished, 1)
    code_choices = [choice for choice in inspection["choices"] if "answerByCode" in choice]
    by_code_pick = code_choices[0]["answerByCode"]
    code_choice = by_code_pick["observedCardPick"]["choice"]
    assert code_choice["seat"] == p1 and code_choice["kind"] == "mulligan"
    matching = [choice for choice in code_choices if choice["answerByCode"] == by_code_pick]
    game["answers"].append(matching[0]["answer"])
    by_id_pick = inspect_game(folder, command, unfinished, 1)
    game["answers"][-1] = by_code_pick
    with_code = inspect_game(folder, command, unfinished, 1)
    assert with_code["state"] == by_id_pick["state"]
    assert with_code["exactPrefix"] == (len(matching) == 1)
    ambiguous = [] if len(matching) == 1 else [{"answer": 9, "evidence": None}]
    assert with_code["inexactAnswers"] == ambiguous
    game["answers"][-1] = {"inferredCardPick": {"choice": code_choice, "evidence": "later shown"}}
    inferred_pick = inspect_game(folder, command, unfinished, 1)
    assert inferred_pick["state"] == by_id_pick["state"] and not inferred_pick["exactPrefix"]
    assert inferred_pick["inexactAnswers"] == [{"answer": 9, "evidence": "later shown"}]

    code_input = folder / "bo1-by-card-code.json"
    code_archive = folder / "bo1-by-card-code-archive.json"
    raw_archive = json.loads(archive.read_bytes())
    by_code = tape.copy()
    for index, registered_index in enumerate((1, 0)):
        card = originals[index]["deck"]["battlefields"][registered_index]
        by_code[index] = {"observedChance": {"outcome": {"battlefield": {"card": card}}}}
    game["answers"] = by_code
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", code_input, code_archive)) == summary
    assert json.loads(code_archive.read_bytes())["games"][0]["checkpoints"] == raw_archive["games"][0]["checkpoints"]

    for index in range(4, 8):
        ids = tape[index]["observed"]["action"]["kind"]["arrange"]["order"]
        cards = [{"code": sideboard["new"][str(obj["n"])]["card"]} for obj in ids]
        by_code[index] = {"observedChance": {"outcome": {"cardOrder": {"cards": cards}}}}
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    code_summary = {**summary, "exact": False}
    assert json.loads(command("record", code_input, code_archive)) == code_summary
    assert json.loads(command("verify", code_archive)) == code_summary
    assert json.loads(code_archive.read_bytes())["games"][0]["checkpoints"] == raw_archive["games"][0]["checkpoints"]
    command("view", code_archive, trace)
    from_codes = json.loads(trace.read_bytes())
    assert from_codes["games"][0]["steps"] == steps and not from_codes["exact"]
    coded_inspection = inspect_game(folder, command, inputs, 1)
    assert coded_inspection["inexactAnswers"] == [
        {"answer": index, "evidence": None} for index in range(5, 9)
    ]

    # A source that tracks the starting positions distinguishes even identical card codes.
    positioned = by_code.copy()
    for index in range(4, 8):
        game["answers"] = positioned[:index]
        unshuffled = inspect_game(folder, command, inputs, 1)["decision"]["cards"]
        candidates = {entry["object"]["n"]: entry for entry in unshuffled}
        assert [entry["position"] for entry in unshuffled] == list(range(len(unshuffled)))
        ids = tape[index]["observed"]["action"]["kind"]["arrange"]["order"]
        placement = [{"before": candidates[obj["n"]]["position"],
                      "card": candidates[obj["n"]]["card"]} for obj in ids]
        positioned[index] = {"observedChance": {"outcome": {"cardOrderByPosition": {"cards": placement}}}}
    game["answers"] = positioned
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", code_input, code_archive)) == summary
    assert json.loads(command("verify", code_archive)) == summary
    assert json.loads(code_archive.read_bytes())["games"][0]["checkpoints"] == raw_archive["games"][0]["checkpoints"]
    assert inspect_game(folder, command, inputs, 1)["inexactAnswers"] == []

    selection = positioned[4]["observedChance"]["outcome"]["cardOrderByPosition"]["cards"]
    original = selection[0].copy()
    selection[0]["before"] = selection[1]["before"]
    inspect_game(folder, command, inputs, 1, error="answer 5: the recorded card order repeats a source position")
    selection[0]["before"] = len(selection)
    inspect_game(folder, command, inputs, 1, error="answer 5: source position")
    selection[0] = {**original, "card": {"code": "wrong-card"}}
    inspect_game(folder, command, inputs, 1, error="does not hold the recorded card code")
    selection[0] = original

    outcome = by_code[0]["observedChance"]["outcome"]
    game["answers"] = [{"inferredChance": {"outcome": outcome, "evidence": "visible at first score"}}, *tape[1:]]
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", code_input, code_archive)) == code_summary
    game["answers"][0]["inferredChance"]["evidence"] = " "
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", code_input, code_archive, error="answer 1: an inferred answer needs an explanation")

    game["answers"] = by_code
    cards = by_code[4]["observedChance"]["outcome"]["cardOrder"]["cards"]
    omitted = cards.pop()
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", code_input, code_archive, error="answer 5: the card order has")
    cards.append(champion)
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", code_input, code_archive, error="answer 5: card order contains an unavailable copy")
    cards[-1] = omitted
    game["answers"] = [*by_code[:2], by_code[4], *by_code[3:]]
    code_input.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", code_input, code_archive, error="answer 3: no random card order is pending")

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


def check_revalidation(folder: Path, command: Callable[..., str], archive: Path, suffix: str,
                       summary: dict) -> None:
    original = archive.read_bytes()
    old = json.loads(original)
    old["rules"]["cards"] = "previous-table"
    stale = folder / f"{archive.stem}-old-cards.json"
    renewed = folder / f"{archive.stem}-revalidated.json"
    stale.write_text(json.dumps(old), encoding="utf-8")

    command("verify" + suffix, stale, error="card definitions differ")
    assert json.loads(command("revalidate" + suffix, stale, renewed)) == summary
    assert json.loads(renewed.read_bytes()) == json.loads(original)
    assert json.loads(command("verify" + suffix, renewed)) == summary
    assert archive.read_bytes() == original
    stale_data = stale.read_bytes()

    with TemporaryDirectory(dir=folder) as aliases:
        alias_dir = Path(aliases)
        symlink = alias_dir / "same-record.json"
        symlink.symlink_to(stale.resolve())
        message = "the replay output must be a different file from the input"
        command("revalidate" + suffix, stale, stale, error=message)
        command("revalidate" + suffix, stale, symlink, error=message)
        assert symlink.is_symlink() and stale.read_bytes() == stale_data

        hard_link = alias_dir / "updated-record.json"
        hard_link.hardlink_to(stale)
        assert json.loads(command("revalidate" + suffix, stale, hard_link)) == summary
        assert json.loads(hard_link.read_bytes()) == json.loads(original)
        assert stale.read_bytes() == stale_data
        assert not list(alias_dir.glob(".riftbound-replay-*"))

    if not suffix:
        legacy = json.loads(original)
        legacy["rules"]["schema"] = 1
        for game in legacy["games"]:
            for checkpoint in game["checkpoints"]:
                checkpoint.pop("playEnergy")
                checkpoint.pop("playPhysical")
                checkpoint.pop("playStamps")
                checkpoint.pop("buffAttributions")
        stale.write_text(json.dumps(legacy), encoding="utf-8")
        command("verify", stale, error="card definitions differ")
        assert json.loads(command("revalidate", stale, renewed)) == summary
        assert json.loads(renewed.read_bytes()) == json.loads(original)

        changed_payments = json.loads(original)
        checkpoint = changed_payments["games"][0]["checkpoints"][0]
        assert checkpoint["playEnergy"] == []
        checkpoint["playEnergy"] = [4]
        stale.write_text(json.dumps(changed_payments), encoding="utf-8")
        command("verify", stale, error="checkpoint 0: Spell Energy payments differ")

        changed_identities = json.loads(original)
        checkpoint = changed_identities["games"][0]["checkpoints"][0]
        assert checkpoint["playPhysical"] == []
        checkpoint["playPhysical"] = [17]
        stale.write_text(json.dumps(changed_identities), encoding="utf-8")
        command("verify", stale, error="checkpoint 0: finalized card identities differ")

        changed_stamps = json.loads(original)
        checkpoint = changed_stamps["games"][0]["checkpoints"][0]
        assert checkpoint["playStamps"] == []
        checkpoint["playStamps"] = [17]
        stale.write_text(json.dumps(changed_stamps), encoding="utf-8")
        command("verify", stale, error="checkpoint 0: play finalization timestamps differ")

        changed_buffs = json.loads(original)
        checkpoint = changed_buffs["games"][0]["checkpoints"][0]
        assert checkpoint["buffAttributions"] == []
        checkpoint["buffAttributions"] = [[0, {"n": 1}]]
        stale.write_text(json.dumps(changed_buffs), encoding="utf-8")
        command("verify", stale, error="checkpoint 0: buff responsibilities differ")

    game = old["game"] if suffix == "-ffa" else old["games"][0]
    index, checkpoint = next((index, checkpoint) for index, checkpoint in enumerate(game["checkpoints"])
                             if checkpoint["events"])
    checkpoint["events"] = []
    bad = folder / f"{archive.stem}-revalidate-rejected.json"
    stale.write_text(json.dumps(old), encoding="utf-8")
    command("revalidate" + suffix, stale, bad, error=f"checkpoint {index}: events differ")
    assert not bad.exists()
    if not suffix:
        old["rules"]["schema"] += 1
        stale.write_text(json.dumps(old), encoding="utf-8")
        command("revalidate", stale, bad, error="the replay format or rules editions differ")
        assert not bad.exists()
        old = json.loads(original)
        old["rules"]["cards"] = "previous-table"
        old["summary"]["wins"] = [0, 0]
        stale.write_text(json.dumps(old), encoding="utf-8")
        command("revalidate", stale, bad, error="the final match outcome differs")
        assert not bad.exists()


def check_duel_inspection(folder: Path, command: Callable[..., str], saved: dict, view: dict) -> None:
    inputs = deepcopy(saved["input"])
    first, second, _ = inputs["games"]
    first_answers = first["answers"]
    first["answers"] = []
    initial = inspect_game(folder, command, inputs, 1)
    assert initial["checkpoint"] == 0 and initial["nextAnswer"] == 1 and initial["exactPrefix"]
    assert initial["decision"]["kind"] == "cardOrder"
    initial_cards = initial["decision"]["cards"]
    shuffled_ids = first_answers[0]["observed"]["action"]["kind"]["arrange"]["order"]
    assert sorted(card["object"]["n"] for card in initial_cards) == sorted(obj["n"] for obj in shuffled_ids)
    assert all(card["card"]["code"] for card in initial_cards)
    inspect_game(folder, command, inputs, 2, error="game 1: the recorded answers do not finish the game")
    first["answers"] = first_answers

    turn_order_at = next(index for index, answer in enumerate(second["answers"])
                         if "arrangePlayers" in answer["observed"]["action"]["kind"])
    second["answers"][turn_order_at] = {"unknown": {"description": "camera cut"}}
    choice = inspect_game(folder, command, inputs, 2)
    assert choice["checkpoint"] == turn_order_at and choice["nextAnswer"] == turn_order_at + 1
    assert choice["exactPrefix"] and choice["missing"] == "camera cut"
    assert choice["decision"]["kind"] == "turnOrder"
    forced_first = saved["games"][0]["summary"]["turnOrder"][0]
    assert choice["decision"]["forcedFirst"] == forced_first
    orders = [option["answer"]["observed"]["action"]["kind"]["arrangePlayers"]["order"]
              for option in choice["choices"] if option["detail"]["kind"] == "arrangePlayers"]
    assert orders == [saved["games"][1]["summary"]["turnOrder"]]
    previous_board = view["games"][1]["steps"][turn_order_at]["state"]
    assert {**choice["state"], "new": previous_board["new"]} == previous_board

    first["answers"][0] = {"inferred": {"action": first_answers[0]["observed"]["action"],
                                        "evidence": "deck camera"}}
    inherited = inspect_game(folder, command, inputs, 2)
    assert not inherited["exactPrefix"]
    assert inherited["inexactEarlierGames"] == [1] and inherited["inexactAnswers"] == []
    first["answers"] = saved["input"]["games"][0]["answers"]
    finished = inspect_game(folder, command, inputs, 1)
    assert finished["nextAnswer"] is None and finished["decision"] is None and not finished["choices"]


def check_deck_order_observations(folder: Path, command: Callable[..., str], saved: dict, view: dict) -> None:
    inputs = deepcopy(saved["input"])
    opening = view["games"][0]["steps"][0]["state"]

    def order(seat: int, kind: str) -> list[dict]:
        return [{"code": opening["new"][str(obj)]["card"]}
                for obj in opening["zones"][f"p{seat}.{kind}"]]

    main = order(0, "mainDeck")
    runes = order(1, "runeDeck")
    whole = {"zone": {"player": {"p": {"n": 0}, "k": "mainDeck"}}, "cards": main, "offset": None}
    segment = {"zone": {"player": {"p": {"n": 1}, "k": "runeDeck"}},
               "cards": runes[2:6], "offset": 2}
    inputs["games"][0]["observations"] = [{"checkpoint": 0, "facts": [
        {"recordedDeckOrder": whole}, {"recordedDeckOrder": segment},
    ]}]
    source = folder / "deck-order-input.json"
    archive = folder / "deck-order-archive.json"
    source.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", source, archive)) == saved["summary"]
    assert json.loads(command("verify", archive)) == saved["summary"]
    assert inspect_game(folder, command, inputs, 1)["checkedObservations"] == 1

    other = next(index for index, card in enumerate(main) if card != main[0])
    main[0], main[other] = main[other], main[0]
    inspect_game(folder, command, inputs, 1, error="recorded deck order differs at position 1")
    main[0], main[other] = main[other], main[0]
    segment["offset"] = len(runes)
    inspect_game(folder, command, inputs, 1, error="recorded deck slice is outside the replayed deck")
    segment["offset"] = 2
    segment["zone"]["player"]["k"] = "hand"
    inspect_game(folder, command, inputs, 1, error="requires a Main Deck or Rune Deck")


def check_duel_observations(folder: Path, command: Callable[..., str], saved: dict, view: dict) -> None:
    inputs = deepcopy(saved["input"])
    game = inputs["games"][0]
    steps = view["games"][0]["steps"]
    scored = next(row for row in steps if any(row["state"]["points"]))
    index, state = scored["i"], scored["state"]
    p0 = {"n": 0}
    hand = {"player": {"p": p0, "k": "hand"}}
    base = {"player": {"p": p0, "k": "base"}}
    public = {obj: info["card"] for row in steps[:index + 1] for obj, info in row["state"]["new"].items()}
    base_cards = [{"code": public[str(obj)]} for obj in reversed(state["zones"]["p0.base"])]
    first_score = {"seat": p0, "points": state["points"][0]}
    hand_cards = [{"code": public[str(obj)]} for obj in state["zones"]["p0.hand"][:1]]
    assert base_cards and hand_cards and first_score["points"] > 0
    visible_hand = {"viewer": p0, "zone": hand, "cards": hand_cards}
    game["observations"] = [
        {"checkpoint": index, "source": "00:03:21", "facts": [
            {"score": first_score}, {"turn": {"number": state["turn"]}},
            {"phase": {"phase": state["phase"]}}, {"active": {"seat": {"n": state["active"]}}},
            {"clockCalled": {"called": False}}, {"result": {"result": None}},
            {"zoneCount": {"zone": hand, "count": len(state["zones"].get("p0.hand", []))}},
            {"zoneCards": {"zone": base, "cards": base_cards}},
            {"visibleZoneContains": visible_hand},
            {"zoneContains": {"zone": base, "cards": base_cards[:1]}},
        ]},
        {"checkpoint": 0, "facts": [{"turn": {"number": 0}}]},
    ]
    source = folder / "observations-input.json"
    archive = folder / "observations-archive.json"
    source.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", source, archive)) == saved["summary"]
    assert json.loads(command("verify", archive)) == saved["summary"]
    recorded = json.loads(archive.read_bytes())
    assert recorded["games"][0]["checkpoints"] == saved["games"][0]["checkpoints"]

    pending = deepcopy(inputs)
    pending["games"][0]["answers"] = [*game["answers"][:index - 1], {"unknown": {"description": "gap"}}]
    inspection = inspect_game(folder, command, pending, 1)
    assert inspection["checkedObservations"] == 1 and inspection["pendingObservations"] == 1
    assert inspection["missing"] == "gap" and inspection["nextAnswer"] == index
    inspection = inspect_game(folder, command, inputs, 1)
    assert inspection["checkedObservations"] == 2 and inspection["pendingObservations"] == 0

    ranged = deepcopy(inputs)
    observed = ranged["games"][0]["observations"]
    observed[0].update(checkpoint=index - 2, through=index + 1)
    observed.append({"checkpoint": index - 1, "facts": [{"score": {"seat": p0, "points": 0}}]})
    ranged_source = folder / "observation-window-input.json"
    ranged_archive = folder / "observation-window-archive.json"
    ranged_source.write_text(json.dumps(ranged), encoding="utf-8")
    assert json.loads(command("record", ranged_source, ranged_archive)) == saved["summary"]
    assert json.loads(command("verify", ranged_archive)) == saved["summary"]
    assert json.loads(ranged_archive.read_bytes())["games"][0]["checkpoints"] == recorded["games"][0]["checkpoints"]
    short = deepcopy(ranged)
    short["games"][0]["answers"] = game["answers"][:index - 1]
    progress = inspect_game(folder, command, short, 1)
    assert progress["checkedObservations"] == 2 and progress["pendingObservations"] == 1
    observed[0]["through"] = index - 1
    inspect_game(folder, command, ranged, 1, error=f"no match in checkpoints {index - 2} through {index - 1}")
    observed[0]["through"] = index - 3
    inspect_game(folder, command, ranged, 1, error="observation window ends before it starts")

    mismatch = f'game 1: checkpoint {index}: observation ("00:03:21"): seat 0 score'
    first_score["points"] += 1
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, archive, error=mismatch)
    inspect_game(folder, command, inputs, 1, error=mismatch)
    for game_input in (recorded["input"]["games"][0], recorded["games"][0]["input"]):
        game_input["observations"][0]["facts"][0]["score"]["points"] = first_score["points"]
    archive.write_text(json.dumps(recorded), encoding="utf-8")
    command("verify", archive, error=mismatch)
    command("revalidate", archive, folder / "bad-revalidated.json", error=mismatch)
    first_score["points"] -= 1

    visible_hand["viewer"] = {"n": 1}
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, archive, error="faces visible to seat 1")
    visible_hand["viewer"] = p0

    facts = game["observations"][0]["facts"]
    remembered = facts.pop()
    facts.append({"zoneContains": {"zone": base, "cards": [base_cards[0]] * (base_cards.count(base_cards[0]) + 1)}})
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, archive, error="expected at least")
    facts[-1] = {"zoneCards": {"zone": hand, "cards": []}}
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, archive, error="only the count can be observed here")
    facts[-1] = remembered
    game["observations"].append({"checkpoint": len(game["answers"]) + 1, "facts": [{"turn": {"number": 0}}]})
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, archive, error="observation is beyond the last answer")


def check_public_events(folder: Path, command: Callable[..., str], saved: dict, view: dict) -> None:
    inputs = deepcopy(saved["input"])
    game = inputs["games"][0]
    opening = next(step for step in view["games"][0]["steps"]
                   if sum(event["t"] == "drew" for event in step["events"]) == 8)
    draws = [event["player"] for event in opening["events"] if event["t"] == "drew"]
    first, second = draws[0], draws[-1]
    assert first != second and draws == [first] * 4 + [second] * 4
    observed_draws = [{"drew": {"seat": {"n": first}}}, {"drew": {"seat": {"n": second}}}]
    fact = {"eventsInOrder": {"events": observed_draws}}
    game["observations"] = [{"checkpoint": opening["i"], "facts": [fact]}]
    source = folder / "events-input.json"
    archive = folder / "events-archive.json"
    source.write_text(json.dumps(inputs), encoding="utf-8")
    assert json.loads(command("record", source, archive)) == saved["summary"]
    assert json.loads(command("verify", archive)) == saved["summary"]
    assert inspect_game(folder, command, inputs, 1)["checkedObservations"] == 1
    recorded = json.loads(archive.read_bytes())
    assert recorded["games"][0]["checkpoints"] == saved["games"][0]["checkpoints"]

    observed_draws.reverse()
    source.write_text(json.dumps(inputs), encoding="utf-8")
    mismatch = f'checkpoint {opening["i"]}: observation: public events: expected in order'
    command("record", source, archive, error=mismatch)
    inspect_game(folder, command, inputs, 1, error=mismatch)
    fact["eventsInOrder"]["events"] = [observed_draws[-1]] * 5
    source.write_text(json.dumps(inputs), encoding="utf-8")
    command("record", source, archive, error=mismatch)


def check_cli(folder: Path, saved: dict, setup: dict, group_move: dict, elimination: dict, bo1: dict,
              team_matches: dict[str, tuple[dict, list[int]]], penalties: dict, corrections: dict,
              private_rewinds: dict, timeline_rewinds: dict) -> None:
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
    check_revalidation(folder, command, archive, "", saved["summary"])
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
    check_duel_inspection(folder, command, saved, view)
    check_duel_observations(folder, command, saved, view)
    check_deck_order_observations(folder, command, saved, view)
    check_public_events(folder, command, saved, view)

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
    overtime_inputs = deepcopy(elimination["input"])
    overtime_inputs["games"][1]["answers"] = []
    overtime_inspection = inspect_game(folder, command, overtime_inputs, 2)
    assert overtime_inspection["checkpoint"] == 0 and overtime_inspection["clockCalled"]
    assert overtime_inspection["state"]["eliminationDeadline"] == 6
    overtime_inputs["games"].pop()
    overtime_inputs.pop("ending")
    assert inspect_game(folder, command, overtime_inputs, 1)["nextAnswer"] is None

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
    team_game["observations"] = [{"checkpoint": len(team_game["answers"]), "facts": [
        {"score": {"seat": p3, "points": 0}},
        {"result": {"result": {"won": {"winners": [p3, p2]}}}},
    ]}]
    team_record["winsRequired"] = 1
    team_input.write_text(json.dumps(team_record), encoding="utf-8")
    team_archive = folder / "team-archive.json"
    summary = json.loads(command("record-team", team_input, team_archive))
    assert summary["wins"] == [0, 1] and summary["exact"] and summary["cardsFullyChecked"]
    assert json.loads(command("verify-team", team_archive)) == summary
    actual_team = json.loads(team_archive.read_bytes())
    assert actual_team["games"][0]["input"]["observations"] == team_game["observations"]
    check_revalidation(folder, command, team_archive, "-team", summary)
    team_trace = folder / "team-trace.json"
    command("view-team", team_archive, team_trace)
    exported = json.loads(team_trace.read_text(encoding="utf-8"))
    assert exported["teams"] == [[0, 1], [2, 3]] and exported["winner"] == 1
    assert exported["games"][0]["players"] == 4 and exported["exact"]
    steps = exported["games"][0]["steps"]
    assert any((row["action"] or {}).get("kind") == "inviteTeammate" for row in steps)

    partial_game = {key: value for key, value in team_game.items()
                    if key not in ("ending", "points", "battlefields")}
    partial_game["answers"] = team_game["answers"][:8]
    partial = {key: value for key, value in team_record.items() if key != "ending"}
    partial["games"] = [partial_game]
    inspection = inspect_game(folder, command, partial, 1, "-team")
    decision = inspection["decision"]
    assert inspection["checkpoint"] == 8 and inspection["exactPrefix"]
    assert decision["kind"] == "battlefield" and decision["seat"] == p2
    assert decision["cards"][0]["card"] == team_game["battlefields"][0][1]
    partial_game["answers"].append(decision["cards"][0]["answerByCode"])
    assert inspect_game(folder, command, partial, 1, "-team")["decision"]["seat"] == p1

    order_input = folder / "team-opening-order.json"
    order_archive = folder / "team-opening-order-archive.json"
    order_trace = folder / "team-opening-order-trace.json"
    order_game = {**team_game, "openingOrderEvidence": {"inferred": {"evidence": "later turns show the order"}}}
    order_record = {**team_record, "games": [order_game]}
    order_inspection = inspect_game(folder, command, order_record, 1, "-team")
    assert not order_inspection["exactPrefix"]
    assert order_inspection["openingOrderEvidence"] == order_game["openingOrderEvidence"]
    assert order_inspection["inexactAnswers"] == [] and order_inspection["inexactEarlierGames"] == []
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
    assert not inferred_summary["exact"] and inferred_summary["cardsFullyChecked"]
    assert json.loads(command("verify-team", inferred_archive)) == inferred_summary
    check_limited_cli(folder, setup, command)
    check_war_concession_cli(folder, command)
    check_lux_spell_energy_cli(folder, command)
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
        if label == "live-team-tiebreaker":
            timed = deepcopy(team_archive["input"])
            last = timed["games"][1]
            for field in ("battlefields", "points", "ending", "timed"):
                last.pop(field)
            last["answers"] = []
            inspection = inspect_game(folder, command, timed, 2, "-team")
            assert inspection["checkpoint"] == 0 and inspection["clockCalled"]
            assert inspection["state"]["eliminationDeadline"] == 6
            assert inspection["turnOrder"] == last["order"]
        if label == "live-team":
            check_seat_disclosures(folder, command, archive, "-team", 2, exported["games"])
            seat_view = check_seat_view(folder, command, archive, "-team", 2, exported["games"])
            assert seat_view["teams"] == exported["teams"] and seat_view["wins"] == wins
            zones = seat_view["games"][0]["steps"][-1]["state"]["zones"]
            assert zones["p2.hand"] and all(card is not None for card in zones["p2.hand"])
            assert all(card is None for card in zones["p3.hand"])
    check_judge_penalties(folder, command, penalties)
    check_judge_corrections(folder, command, corrections)
    check_private_rewinds(folder, command, private_rewinds)
    check_timeline_rewinds(folder, command, timeline_rewinds)


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
        penalties = live_judge_penalties(live, setup)
        corrections = live_judge_corrections(live, setup)
        private_rewinds = live_private_rewinds(live, setup)
        private_rewinds["revealed-draw"] = live_revealed_draw_rewind(live, setup)
        private_rewinds["undrawn-look"] = live_undrawn_deck_rewind(live, setup)
        timeline_rewinds = live_timeline_rewinds(live, setup)
    finally:
        live.close()
        live.proc.wait()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        check_cli(args.output, saved, setup, group_move, elimination, bo1, team_matches, penalties,
                  corrections, private_rewinds, timeline_rewinds)
    else:
        with TemporaryDirectory() as folder:
            check_cli(Path(folder), saved, setup, group_move, elimination, bo1, team_matches, penalties,
                      corrections, private_rewinds, timeline_rewinds)
    print("replay smoke: OK")


if __name__ == "__main__":
    main()
