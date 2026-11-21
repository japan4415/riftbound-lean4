"""論理カードの一覧（data/cards/logical.json）から RiftboundCards/<Set>.lean を更新する。

    uv run --no-project python scripts/gen_lean.py            # 書き換える
    uv run --no-project python scripts/gen_lean.py --check    # 書き換えず、差分があれば失敗する

- 1 弾 1 ファイル（docs/card-data.md §4.1）。カードごとに、生成ブロック（`-- BEGIN GENERATED`
  〜 `-- END GENERATED`）と、その直後の手書きの部分を並べる。
- 生成ブロックだけを書き換える。手書きの部分、ファイルの先頭（ヘッダ）は触れない。
- 新しいカードには、生成ブロックと手書きの雛形を足す。
- 弾ごとのカード一覧（`cards`）と RiftboundCards/Registry.lean も生成する。
- 公式ギャラリーに無い supertype は空のまま。2 つのドメインを持つカードの Power の
  ドメインの割り当ては分からないので、任意のドメイン（`.any`）にして、印を付ける。
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CARDS_DIR = ROOT / "RiftboundCards"

SETS = [  # (コード, ファイル名と namespace の末尾, 名前)
    ("OGN", "Origins", "Origins"),
    ("OGS", "ProvingGrounds", "Proving Grounds"),
    ("SFD", "Spiritforged", "Spiritforged"),
    ("UNL", "Unleashed", "Unleashed"),
    ("VEN", "Vendetta", "Vendetta"),
    ("RAD", "Radiance", "Radiance"),
]

TYPES = {"unit": "unit", "gear": "gear", "spell": "spell", "rune": "rune",
         "battlefield": "battlefield", "legend": "legend"}
DOMAINS = {"fury", "calm", "mind", "body", "chaos", "order"}

# 印刷されたキーワード（Empowered は条件として使われるので含めない）
KEYWORDS = {
    "Accelerate": "accelerate", "Action": "action", "Assault": "assault",
    "Deathknell": "deathknell", "Deflect": "deflect", "Ganking": "ganking",
    "Hidden": "hidden", "Legion": "legion", "Reaction": "reaction", "Shield": "shield",
    "Tank": "tank", "Temporary": "temporary", "Vision": "vision", "Equip": "equip",
    "Quick-Draw": "quickDraw", "Repeat": "repeat_", "Weaponmaster": "weaponmaster",
    "Ambush": "ambush", "Hunt": "hunt", "Level": "level", "Unique": "unique",
    "Backline": "backline", "Empower": "empower", "Flow": "flow", "Deploy": "deploy",
    "Disarm": "disarm", "Show Off": "showOff",
}
AMOUNT_KW = {"Assault", "Shield", "Deflect", "Hunt", "Level", "Disarm"}
COST_KW = {"Equip", "Repeat", "Empower", "Flow"}

KW_RE = re.compile(r"\[([A-Za-z\- ]+?)(?: (\d+))?\]")
SYM_RE = re.compile(r":rb_(energy_(\d+)|rune_([a-z]+)):")


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def ident(card_id: str) -> str:
    return card_id.replace("-", "_")


def doc_safe(s: str) -> str:
    return s.replace("/-", "/ -").replace("-/", "- /")


def power_sym(d: str | None) -> str:
    return f".domain .{d}" if d else ".any"


def cost_expr(energy: int | None, power: int | None, domains: list[str]) -> tuple[str, bool]:
    """Lean の式と、Power のドメインが分からなかったか。"""
    if energy is None and power is None:
        return "none", False
    doms = [d for d in domains if d in DOMAINS]
    unknown = bool(power) and len(doms) != 1
    syms = [power_sym(doms[0] if len(doms) == 1 else None)] * (power or 0)
    return f"some ⟨{energy or 0}, [{', '.join(syms)}]⟩", unknown


def parse_cost(rest: str) -> str | None:
    """キーワードの直後の `:rb_energy_N::rb_rune_x:` の並びを Cost の式にする。"""
    energy, power, pos = 0, [], 0
    rest = rest.lstrip()
    while True:
        m = SYM_RE.match(rest, pos)
        if not m:
            break
        pos = m.end()
        if m.group(2) is not None:
            energy += int(m.group(2))
        else:
            d = m.group(3)
            power.append(f".domain .{d}" if d in DOMAINS else ".any")
    if pos == 0:
        return None
    return f"⟨{energy}, [{', '.join(power)}]⟩"


def keywords_of(lines: list[str]) -> tuple[list[str], int]:
    """各行の先頭に並ぶキーワードを集める。式のリストと、引数を読めなかった数。"""
    out, unparsed = [], 0
    for line in lines:
        pos = 0
        while True:
            m = KW_RE.match(line, pos)
            if not m or m.group(1) not in KEYWORDS:
                break
            name, n = m.group(1), m.group(2)
            ctor = KEYWORDS[name]
            pos = m.end()
            arg = ""
            if name in AMOUNT_KW:
                arg = f", arg := .amount {int(n) if n else 1}"
            elif name in COST_KW:
                c = parse_cost(line[pos:])
                if c is None:
                    unparsed += 1
                else:
                    arg = f", arg := .cost {c}"
            elif name == "Show Off":
                mo = re.match(r"\s*(.+?)(?:\.|\s\(|$)", line[pos:])
                if mo:
                    arg = f", arg := .object {lean_str(mo.group(1))}"
            out.append(f"{{ keyword := .{ctor}{arg} }}")
            nxt = re.match(r",?\s*(?=\[)", line[pos:])
            if not nxt or not nxt.group(0):
                break
            pos += nxt.end()
    return out, unparsed


def card_block(c: dict) -> str:
    cid = c["cardId"]
    types = [TYPES[t] for t in c["types"] if t in TYPES]
    doms = [d for d in c["domains"] if d in DOMAINS]
    cost, unknown_power = cost_expr(c["energy"], c["power"], c["domains"])
    kws, unparsed = keywords_of(c["text"])
    title = c["name"] + (f", {c['subtitle']}" if c["subtitle"] else "")
    kind = " ".join(t.capitalize() for t in c["types"]) or "Token"
    head = f"**{doc_safe(title)}** — {kind}"
    if c["domains"]:
        head += " · " + "/".join(d.capitalize() for d in c["domains"])
    if c["energy"] is not None or c["power"]:
        head += f" · Energy {c['energy'] or 0}" + (f" + Power {c['power']}" if c["power"] else "")
    if c["might"] is not None:
        head += f" · Might {c['might']}"
    lines = [f"-- BEGIN GENERATED {cid}", "/--", head,
             "Printings: " + ", ".join(c["printings"]), ""]
    for t in c["text"] or ["(no text)"]:
        lines += [f"> {w}" for w in textwrap.wrap(doc_safe(t), 94, break_long_words=False,
                                                  break_on_hyphens=False)]
    if c.get("effectText"):
        lines += ["", "Effect (given to the unit it is attached to):", ""]
        for t in c["effectText"]:
            lines += [f"> {w}" for w in textwrap.wrap(doc_safe(t), 94, break_long_words=False,
                                                      break_on_hyphens=False)]
    lines += ["-/", f"def {ident(cid)}.meta : CardDef :="]
    fields = [f"id := ⟨{lean_str(cid)}⟩", f"name := {lean_str(c['name'])}"]
    if c["subtitle"]:
        fields.append(f"subtitle := some {lean_str(c['subtitle'])}")
    fields.append(f"types := [{', '.join('.' + t for t in types)}]")
    if c["tags"]:
        fields.append("tags := [" + ", ".join(f"⟨{lean_str(t)}⟩" for t in c["tags"]) + "]")
    if doms:
        fields.append(f"domains := [{', '.join('.' + d for d in doms)}]")
    if cost != "none":
        fields.append(f"cost := {cost}")
    if c["might"] is not None:
        fields.append(f"might := some {c['might']}")
    if c["mightBonus"] is not None:
        fields.append(f"mightBonus := some {c['mightBonus']}")
    if kws:
        one = "keywords := [" + ",\n      ".join(kws) + "]"
        fields.append(one if max(len(x) for x in one.split("\n")) <= 90
                      else "keywords :=\n      [" + ",\n       ".join(kws) + "]")
    fields.append("sets := [" + ", ".join(f"⟨{lean_str(s)}⟩" for s in c["sets"]) + "]")
    body = "  { " + ",\n    ".join(fields) + " }"
    notes = []
    if unknown_power:
        notes.append("Power domains unknown")
    if unparsed:
        notes.append("keyword cost unread")
    if notes:
        body += "  -- " + "; ".join(notes)
    lines += [body, "-- END GENERATED"]
    return "\n".join(lines) + "\n"


def stub(c: dict) -> str:
    title = c["name"] + (f", {c['subtitle']}" if c["subtitle"] else "")
    return (f"\n/-- {doc_safe(title)}: the effect is not written yet. -/\n"
            f"def {ident(c['cardId'])} : CardDef := {ident(c['cardId'])}.meta\n")


def default_header(code: str, ns: str, name: str) -> str:
    return (f"module\n\npublic import Riftbound.Card.CardDef\n\n/-!\n# {name} ({code})\n\n"
            f"The cards first printed in {name}. Each card has a generated block (the official text and\n"
            f"the metadata) and, right after it, the part written by hand (the effect and the\n"
            f"implementation status). `scripts/gen_lean.py` rewrites the generated blocks only\n"
            f"(docs/card-data.md §4.1).\n-/\n\n@[expose] public section\n\n"
            f"namespace RiftboundCards.{ns}\n\nopen Riftbound\n\n")


def default_footer(ns: str) -> str:
    return f"\nend RiftboundCards.{ns}\n\nend\n"


BLOCK_RE = re.compile(
    r"-- BEGIN GENERATED (?P<id>[A-Z]+-[A-Za-z0-9]+)\n.*?-- END GENERATED\n(?P<hand>.*?)"
    r"(?=-- BEGIN GENERATED |\Z)", re.S)
LIST_RE = re.compile(r"-- BEGIN GENERATED LIST\n.*?-- END GENERATED LIST\n", re.S)


def render_set(code: str, ns: str, name: str, cards: list[dict], old: str | None) -> str:
    header = default_header(code, ns, name)
    footer = default_footer(ns)
    hands: dict[str, str] = {}
    if old:
        first = re.search(r"-- BEGIN GENERATED (?!LIST)", old)
        lst = LIST_RE.search(old)
        if first:
            header = old[:first.start()]
        elif lst:
            header = old[:lst.start()]
        if lst:
            footer = old[lst.end():]
        body = old[first.start():lst.start() if lst else len(old)] if first else ""
        for m in BLOCK_RE.finditer(body):
            hands[m.group("id")] = m.group("hand")
    ids = {c["cardId"] for c in cards}
    stale = [i for i in hands if i not in ids]
    if stale:
        print(f"warning: {name}: cards no longer in the data (kept out of the file): {stale}",
              file=sys.stderr)
    out = [header.rstrip("\n") + "\n\n"]
    for c in cards:
        out.append(card_block(c))
        out.append(hands.get(c["cardId"], stub(c)).rstrip("\n") + "\n\n")
    names = ",\n    ".join(ident(c["cardId"]) for c in cards)
    out.append("-- BEGIN GENERATED LIST\n/-- The cards first printed in " + name +
               ". -/\ndef cards : List CardDef :=\n  [" + names + "]\n-- END GENERATED LIST\n")
    out.append(footer)
    return "".join(out)


def render_registry() -> str:
    imports = "".join(f"public import RiftboundCards.{ns}\n" for _, ns, _ in SETS)
    imports += "public import RiftboundCards.Tokens\n"
    cards = " ++\n    ".join(f"RiftboundCards.{ns}.cards" for _, ns, _ in SETS)
    return ("module\n\npublic import Riftbound.Card.CardDB\n" + imports +
            "\n/-!\n# The card database\n\nAll the cards of all the sets. Generated by "
            "`scripts/gen_lean.py`.\n-/\n\n@[expose] public section\n\nnamespace RiftboundCards\n\n"
            "open Riftbound\n\n/-- Every card, set by set. -/\ndef allCards : List CardDef :=\n  "
            + cards + "\n\n/-- The card database: the cards of the sets, and the tokens. -/\n"
            "def db : CardDB := ⟨allCards ++ RiftboundCards.Tokens.cards⟩\n\n"
            "end RiftboundCards\n\nend\n")


def outputs(data: dict) -> dict[Path, str]:
    res: dict[Path, str] = {}
    for code, ns, name in SETS:
        cards = [c for c in data["cards"] if c["sets"][0] == code]
        path = CARDS_DIR / f"{ns}.lean"
        old = path.read_text(encoding="utf8") if path.exists() else None
        res[path] = render_set(code, ns, name, cards, old)
    res[CARDS_DIR / "Registry.lean"] = render_registry()
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="書き換えず、差分があれば失敗する")
    args = ap.parse_args()
    data = json.loads((ROOT / "data" / "cards" / "logical.json").read_text(encoding="utf8"))
    res = outputs(data)
    stale = [p for p, t in res.items() if not p.exists() or p.read_text(encoding="utf8") != t]
    if args.check:
        if stale:
            raise SystemExit("out of date: " + ", ".join(p.name for p in stale)
                             + ": run scripts/gen_lean.py")
        print(f"RiftboundCards is up to date ({data['count']} cards)", file=sys.stderr)
        return
    CARDS_DIR.mkdir(exist_ok=True)
    for p, t in res.items():
        p.write_text(t, encoding="utf8")
    print(f"wrote {len(res)} files ({data['count']} cards; {len(stale)} changed)", file=sys.stderr)


if __name__ == "__main__":
    main()
