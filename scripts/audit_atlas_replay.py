"""Report what a local RiftAtlas History & Replays JSON exposes about its opening."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


CARD_CODE = re.compile(r"[A-Za-z][A-Za-z0-9]{1,7}-[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*")
DECK_LIST_FIELDS = ("deck", "submittedDeck", "registeredDeck")
OPENING_ZONES = {"hand": "hand", "mainDeck": "deck", "runeDeck": "runeDeck"}


class ReplayGraph:
    """Resolve one node at a time so shared or circular values are never expanded."""

    def __init__(self, raw: object):
        if not isinstance(raw, dict) or raw.get("format") != "riftatlas-replay":
            raise ValueError("expected a RiftAtlas replay JSON")
        self.nodes = raw.get("nodes")
        root = raw.get("root")
        if not isinstance(self.nodes, list) or not isinstance(root, dict) or set(root) != {"r"}:
            raise ValueError("expected the History & Replays JSON with nodes and root")
        self.version = raw.get("version")
        self.root = self.object(root)
        if self.root is None:
            raise ValueError("the replay root must be an object")

    def resolve(self, value: object) -> object:
        if not isinstance(value, dict) or set(value) != {"r"}:
            return value
        index = value["r"]
        if type(index) is not int or not 0 <= index < len(self.nodes):
            raise ValueError("an inspected field has an invalid replay node reference")
        node = self.nodes[index]
        if not isinstance(node, list) or len(node) != 2 or not isinstance(node[1], list):
            raise ValueError(f"invalid replay node {index}")
        tag, contents = node
        if tag == "a":
            return contents
        if tag == "o":
            fields = {}
            for pair in contents:
                if not isinstance(pair, list) or len(pair) != 2 or not isinstance(pair[0], str):
                    raise ValueError(f"invalid field in replay node {index}")
                key, field = pair
                if key in fields:
                    raise ValueError(f"duplicate field in replay node {index}")
                fields[key] = field
            return fields
        raise ValueError(f"invalid replay node type at {index}")

    def object(self, value: object) -> dict | None:
        result = self.resolve(value)
        return result if isinstance(result, dict) else None

    def array(self, value: object) -> list | None:
        result = self.resolve(value)
        return result if isinstance(result, list) else None


def has_list_text(player: dict, graph: ReplayGraph) -> bool:
    deck_lists = [player.get("decklistRaw")]
    for field in DECK_LIST_FIELDS:
        deck_lists.append((graph.object(player.get(field)) or {}).get("raw"))
    return any(isinstance(value, str) and value.strip() for value in deck_lists)


def zone_summary(graph: ReplayGraph, zone: object) -> dict | None:
    value = graph.resolve(zone)
    if isinstance(value, dict) and "id" in value:
        value = [value]
    if not isinstance(value, list):
        return None
    coded = 0
    for entry in value:
        card = graph.object(entry) or {}
        code = card.get("cardCode")
        if isinstance(code, str) and CARD_CODE.fullmatch(code):
            coded += 1
    return {"entries": len(value), "withCardCode": coded}


def seat_players(graph: ReplayGraph, state: dict) -> dict[int, dict]:
    result = {}
    for entry in graph.array(state.get("players")) or []:
        player = graph.object(entry) or {}
        seat = player.get("seat")
        if type(seat) is not int or seat < 0 or seat in result:
            raise ValueError("an inspected state has missing or duplicate seat numbers")
        result[seat] = player
    return result


def audit(raw: object) -> dict:
    graph = ReplayGraph(raw)
    frames = graph.array(graph.root.get("frames"))
    if not frames:
        raise ValueError("the replay has no source frames")
    opening = None
    first_play = None
    final = None
    with_state = 0
    for index, entry in enumerate(frames):
        frame = graph.object(entry) or {}
        state = graph.object(frame.get("state"))
        if state is None:
            continue
        with_state += 1
        final = state
        if state.get("phase") == "mulligan" and opening is None and first_play is None:
            opening = (index, state)
        if state.get("phase") == "in_game" and first_play is None:
            first_play = index
    if final is None:
        raise ValueError("the replay has no source frames with state")

    opening_players = seat_players(graph, opening[1]) if opening else {}
    final_players = seat_players(graph, final)
    seats = []
    for seat in sorted(opening_players.keys() | final_players.keys()):
        first = opening_players.get(seat, {})
        latest = final_players.get(seat, {})
        board = graph.object(first.get("board")) or {}
        seats.append({
            "seat": seat,
            "hasDeckListText": has_list_text(first, graph) or has_list_text(latest, graph),
            "mulliganZones": {name: zone_summary(graph, board.get(key)) for name, key in OPENING_ZONES.items()},
        })
    version = graph.version if type(graph.version) is int else None
    return {
        "sourceVersion": version,
        "sourceFrames": len(frames),
        "sourceFramesWithState": with_state,
        "firstMulliganFrame": opening[0] if opening else None,
        "firstInGameFrame": first_play,
        "hasFinalOutcome": bool(graph.object(final.get("gameOutcome"))),
        "seats": seats,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="local History & Replays JSON file")
    args = parser.parse_args()
    try:
        report = audit(json.loads(args.input.read_text(encoding="utf-8")))
    except (OSError, ValueError, RecursionError) as error:
        parser.exit(1, f"{error}\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
