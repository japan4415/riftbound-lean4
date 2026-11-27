"""Inspect a local RiftAtlas replay or extract observations at aligned checkpoints."""

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

    def frames(self) -> list:
        frames = self.array(self.root.get("frames"))
        if not frames:
            raise ValueError("the replay has no source frames")
        return frames


def has_list_text(player: dict, graph: ReplayGraph) -> bool:
    deck_lists = [player.get("decklistRaw")]
    for field in DECK_LIST_FIELDS:
        deck_lists.append((graph.object(player.get(field)) or {}).get("raw"))
    return any(isinstance(value, str) and value.strip() for value in deck_lists)


def zone_entries(graph: ReplayGraph, zone: object) -> list | None:
    value = graph.resolve(zone)
    if isinstance(value, dict) and "id" in value:
        return [value]
    return value if isinstance(value, list) else None


def has_card_code(card: dict) -> bool:
    code = card.get("cardCode")
    return isinstance(code, str) and CARD_CODE.fullmatch(code) is not None


def zone_summary(graph: ReplayGraph, zone: object) -> dict | None:
    entries = zone_entries(graph, zone)
    if entries is None:
        return None
    coded = sum(has_card_code(graph.object(entry) or {}) for entry in entries)
    return {"entries": len(entries), "withCardCode": coded}


def natural(value: object) -> bool:
    return type(value) is int and value >= 0


def seat_players(graph: ReplayGraph, state: dict) -> dict[int, dict]:
    result = {}
    for entry in graph.array(state.get("players")) or []:
        player = graph.object(entry) or {}
        seat = player.get("seat")
        if not natural(seat) or seat in result:
            raise ValueError("an inspected state has missing or duplicate seat numbers")
        result[seat] = player
    return result


def audit(raw: object) -> dict:
    graph = ReplayGraph(raw)
    frames = graph.frames()
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


def known_zone_count(graph: ReplayGraph, zone: object) -> int | None:
    """Empty and masked values are ambiguous in external snapshots."""
    entries = zone_entries(graph, zone)
    if not entries:
        return None
    seen = set()
    for entry in entries:
        card = graph.object(entry) or {}
        identity = card.get("id")
        if (not isinstance(identity, str) or not identity or identity.startswith("__")
                or identity in seen or not has_card_code(card)):
            return None
        seen.add(identity)
    return len(seen)


def source_seats(anchors: dict) -> dict[int, int]:
    entries = anchors.get("seats")
    if not isinstance(entries, list) or not entries:
        raise ValueError("the alignment needs at least one seat mapping")
    result = {}
    targets = set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("seat mappings need source and target seat numbers")
        source, target = entry.get("source"), entry.get("target")
        if not natural(source) or not natural(target):
            raise ValueError("seat mappings need nonnegative source and target seat numbers")
        if source in result or target in targets:
            raise ValueError("the seat mapping must be one-to-one")
        result[source] = target
        targets.add(target)
    return result


def frame_facts(graph: ReplayGraph, state: dict, seats: dict[int, int]) -> list[dict]:
    players = seat_players(graph, state)
    if seats.keys() - players.keys():
        raise ValueError("a mapped source seat is absent from the selected state")
    facts = []
    for source, target in seats.items():
        board = graph.object(players[source].get("board")) or {}
        seat = {"n": target}
        score = board.get("score")
        if len(players) == len(seats) == 2 and natural(score):
            facts.append({"score": {"seat": seat, "points": score}})
        for name, key in OPENING_ZONES.items():
            count = known_zone_count(graph, board.get(key))
            if count is not None:
                facts.append({"zoneCount": {"zone": {"player": {"p": seat, "k": name}}, "count": count}})
    return facts


def extract_observations(raw: object, anchors: object) -> dict:
    graph = ReplayGraph(raw)
    frames = graph.frames()
    if not isinstance(anchors, dict):
        raise ValueError("the alignment must be a JSON object")
    seats = source_seats(anchors)
    pairs = anchors.get("frames")
    if not isinstance(pairs, list) or not pairs:
        raise ValueError("the alignment needs at least one source frame")
    observations = []
    used_frames = set()
    for pair in pairs:
        if not isinstance(pair, dict):
            raise ValueError("frame mappings need a frame and a checkpoint")
        index, checkpoint, through = pair.get("frame"), pair.get("checkpoint"), pair.get("through")
        if not natural(index) or index >= len(frames):
            raise ValueError("a source frame number is outside the replay")
        if not natural(checkpoint) or (through is not None and (not natural(through) or through < checkpoint)):
            raise ValueError(f"source frame {index} needs a valid checkpoint or checkpoint range")
        if index in used_frames:
            raise ValueError(f"source frame {index} was mapped more than once")
        used_frames.add(index)
        frame = graph.object(frames[index]) or {}
        state = graph.object(frame.get("state"))
        if state is None:
            raise ValueError(f"source frame {index} has no state")
        try:
            facts = frame_facts(graph, state, seats)
        except ValueError as error:
            raise ValueError(f"source frame {index}: {error}") from error
        if not facts:
            raise ValueError(f"source frame {index} has no supported observations for the mapped seats")
        observation = {"checkpoint": checkpoint, "source": f"RiftAtlas frame {index}", "facts": facts}
        if through is not None:
            observation["through"] = through
        observations.append(observation)
    return {"observations": observations}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="local History & Replays JSON file")
    parser.add_argument("--observations", type=Path, metavar="ALIGNMENT.json",
                        help="extract observations using the given seat and checkpoint mapping")
    args = parser.parse_args()
    try:
        raw = json.loads(args.input.read_text(encoding="utf-8"))
        if args.observations is None:
            report = audit(raw)
        else:
            anchors = json.loads(args.observations.read_text(encoding="utf-8"))
            report = extract_observations(raw, anchors)
    except (OSError, ValueError, RecursionError) as error:
        parser.exit(1, f"{error}\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
