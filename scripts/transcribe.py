"""カードの文面を、決まった型の文だけ IR の値に書き起こし、手書きの部分の雛形に入れる。

    uv run --no-project python scripts/transcribe.py --dry     # 何枚書けるかだけを出す
    uv run --no-project python scripts/transcribe.py           # 雛形のままのカードを書き換える

- 対象は、手書きの部分が雛形（`def X : CardDef := X.meta`）のままのカードだけ。手書きの転記は
  上書きしない。
- 文は、下の `SENTENCES` と `TRIGGERS` の型のどれかに合うときだけ書く。カードの文が 1 つでも
  合わなければ、そのカードは雛形のまま残す（一部だけの転記はしない）。
- キーワードだけの行は、生成ブロックの `keywords` に入っているので、効果には何も足さない。
- 書いた IR は、`CardDB.WF` の静的な検査（`Riftbound/Card/IR/Check.lean`）と、型のビルドで確かめる。
  文が意味どおりかは、型の読み方（このファイルの表）を人が確かめる。
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FILES = {"OGS": "ProvingGrounds", "OGN": "Origins", "UNL": "Unleashed", "VEN": "Vendetta",
         "RAD": "Radiance", "SFD": "Spiritforged"}

KW = (r"Accelerate|Action|Assault|Deathknell|Deflect|Ganking|Hidden|Legion|Reaction|Shield|Tank|"
      r"Temporary|Vision|Equip|Quick-Draw|Repeat|Weaponmaster|Ambush|Hunt|Level|Unique|Backline|"
      r"Empower|Flow|Deploy|Disarm|Show Off")
KW_LINE = re.compile(rf"^(\[({KW})( \d+)?\](\s*(:rb_[a-z_0-9]+:)+)?(,\s*|\s+)?)+\.?$")


def strip_reminder(s: str) -> str:
    return re.sub(r"\s*\([^)]*\)", "", s).strip()


# ---- 対象の名詞句 -------------------------------------------------------------------------
NP = re.compile(r"^(?P<q>an?|one) (?P<side>friendly |enemy )?unit(?P<place> at a battlefield| here)?$")


def np_choice(np: str):
    """名詞句を、対象の宣言（Choice）の式にする。合わなければ None。"""
    m = NP.match(np)
    if not m:
        return None
    side = {"friendly ": ".friendly", "enemy ": ".enemy", None: ".any"}[m.group("side")]
    place = {" at a battlefield": ".atBattlefield", " here": ".here", None: ".anywhere"}[m.group("place")]
    return f".targetOf .one {side} {place} [.ofType .unit]"


# ---- 文: (正規表現, 作り方) ---------------------------------------------------------------
# 作り方は、(正規表現の match, 次の対象枠の番号) を受け取り、(増える Choice の式の列, Effect の式) を返す。
def target_sentence(verb_fmt):
    def build(m, slot):
        ch = np_choice(m.group("np"))
        if ch is None:
            return None
        return [ch], verb_fmt(m, f".slot {slot}")
    return build


def all_units(m, damaged: bool = False) -> str:
    """`all (friendly |enemy )?units( here)?` の選択子。"""
    side = {"friendly ": ".friendly", "enemy ": ".enemy", None: ".any"}[m.group("side")]
    place = {" at a battlefield": ".atBattlefield", " here": ".here", None: ".anywhere"}[m.group("place")]
    fs = ".ofType .unit" + (", .damaged" if damaged else "")
    return f"Selector.all {side} {place} [{fs}]"


TOKENS = {"Recruit", "Mech", "Sprite", "Bird", "Sand Soldier", "Shadow Clone", "Tentacle", "Gold"}
COUNT = {"a": 1, "an": 1, "two": 2, "three": 3, "four": 4}
TOKEN_PLACE = {"": ".atBase", " to your base": ".atBase", " in your base": ".atBase",
               " at your base": ".atBase", " into your base": ".atBase", " here": ".here"}


def play_token(m, slot):
    """`Play a (ready) N :rb_might: Name unit token(s) (with [Keyword]) (place).` → create。"""
    name = m.group("name")
    place = TOKEN_PLACE.get(m.group("pos") or "")
    if name not in TOKENS or place is None:
        return None
    ready = "true" if m.group("ready") and not m.group("exh") else "false"
    return [], f'.prim (.create "{name}" (.const {COUNT[m.group("cnt")]}) {place} {ready})'


def add_power(m, slot):
    """`[Add] :rb_rune_x:` 1 つか 2 つ（同じ領域のもの）→ Power を足す。"""
    syms = re.findall(r":rb_rune_([a-z]+):", m.group("syms"))
    if len(set(syms)) != 1:
        return None
    d = syms[0]
    dom = "none" if d == "rainbow" else (f"(some .{d})" if d in DOMAINS else None)
    if dom is None:
        return None
    return [], f".prim (.addPower .you (.const {len(syms)}) {dom} none)"


SENTENCES = [
    (re.compile(r"^Play (?P<cnt>an?|two|three|four) (?P<ready>ready )?(?:\d+ :rb_might: )?"
                r"(?P<name>[A-Z][A-Za-z]*(?: [A-Z][a-z]+)?) (?:unit|gear) tokens?(?: with \[[A-Za-z]+\])?"
                r"(?P<exh> exhausted)?(?P<pos> to your base| in your base| at your base| into your base| here)?\.$"),
     play_token),
    (re.compile(r"^Deal (?P<n>\d+) to (?P<np>.+)\.$"),
     target_sentence(lambda m, s: f".prim (.deal ({s}) (.const {m.group('n')}))")),
    (re.compile(r"^Deal (?P<n>\d+) to all (?P<side>friendly |enemy )?units(?P<place> at a battlefield| here)?\.$"),
     lambda m, slot: ([], f".prim (.deal ({all_units(m)}) (.const {m.group('n')}))")),
    (re.compile(r"^Kill all (?P<dmg>damaged )?(?P<side>friendly |enemy )?units(?P<place> at a battlefield| here)?\.$"),
     lambda m, slot: ([], f".prim (.kill ({all_units(m, damaged=bool(m.group('dmg')))}))")),
    (re.compile(r"^Kill (?P<np>.+)\.$"), target_sentence(lambda m, s: f".prim (.kill ({s}))")),
    (re.compile(r"^Ready (?P<np>.+)\.$"), target_sentence(lambda m, s: f".prim (.ready ({s}))")),
    (re.compile(r"^\[Stun\] (?P<np>.+)\.$"), target_sentence(lambda m, s: f".prim (.stun ({s}))")),
    (re.compile(r"^\[Add\] :rb_energy_(?P<n>\d+):\.$"),
     lambda m, slot: ([], f".prim (.addEnergy .you (.const {m.group('n')}) none)")),
    (re.compile(r"^\[Add\] (?P<syms>(?::rb_rune_[a-z]+:)+)\.$"), add_power),
    (re.compile(r"^Kill this\.$"), lambda m, slot: ([], ".prim (.kill .self)")),
    (re.compile(r"^Move me to your base\.$"), lambda m, slot: ([], ".prim (.move .self .base)")),
    (re.compile(r"^Move (?P<np>.+) to your base\.$"),
     target_sentence(lambda m, s: f".prim (.move ({s}) .base)")),
    (re.compile(r"^Buff me\.$"), lambda m, slot: ([], ".prim (.buff .self)")),
    (re.compile(r"^Buff (?P<np>.+)\.$"), target_sentence(lambda m, s: f".prim (.buff ({s}))")),
    (re.compile(r"^Gain (?P<n>\d+) XP\.$"),
     lambda m, slot: ([], f".prim (.gainXP .you (.const {m.group('n')}))")),
    (re.compile(r"^Give (?P<np>.+) \+(?P<n>\d+) :rb_might: this turn\.$"),
     target_sentence(lambda m, s:
                     f".grant ({s}) (.mightPlus .it (.const {m.group('n')})) .thisTurn")),
    (re.compile(r"^Give (?P<np>.+) -(?P<n>\d+) :rb_might: this turn\.$"),
     target_sentence(lambda m, s:
                     f".grant ({s}) (.mightMinus .it (.const {m.group('n')})) .thisTurn")),
    (re.compile(r"^Give me \+(?P<n>\d+) :rb_might: this turn\.$"),
     lambda m, slot: ([], f".grant .self (.mightPlus .it (.const {m.group('n')})) .thisTurn")),
    (re.compile(r"^Draw (?P<n>\d+)\.$"),
     lambda m, slot: ([], f".prim (.draw .you (.const {m.group('n')}))")),
    (re.compile(r"^Channel (?P<n>\d+) runes? exhausted\.$"),
     lambda m, slot: ([], f".prim (.channel .you (.const 0) (.const {m.group('n')}))")),
    (re.compile(r"^Channel (?P<n>\d+) runes?\.$"),
     lambda m, slot: ([], f".prim (.channel .you (.const {m.group('n')}) (.const 0))")),
    (re.compile(r"^Discard (?P<n>\d+)\.$"),
     lambda m, slot: ([], f".prim (.discard .you (.const {m.group('n')}))")),
    (re.compile(r"^Return a (?P<t>spell|unit|gear) from your trash to your hand\.$"),
     lambda m, slot: ([], ".prim (.returnToHand (.one .friendly .inTrash "
                          f"[.ofType .{m.group('t')}]))")),
]


def parse_effect(text: str, slot: int = 0):
    """文の列を (Choice の式の列, Effect の式) にする。合わなければ None。"""
    # "A, then b." is the two sentences "A." and "B." in this order
    text = re.sub(r", then ([a-z])", lambda m: ". " + m.group(1).upper(), text)
    text = re.sub(r"(exhausted) and draw (\d+)\.", r"\1. Draw \2.", text)
    sentences = [s for s in re.split(r"(?<=\.) ", text) if s]
    choices: list[str] = []
    effects: list[str] = []
    for s in sentences:
        may = False
        if s.startswith("You may "):
            may, s = True, s[len("You may "):]
            s = s[0].upper() + s[1:]
        for rx, build in SENTENCES:
            m = rx.match(s)
            if m:
                r = build(m, slot + len(choices))
                if r is None:
                    return None
                ch, e = r
                choices += ch
                effects.append(f".may ({e})" if may else e)
                break
        else:
            return None
    if not effects:
        return None
    return choices, effects


def fmt_effect_def(choices: list[str], effects: list[str], pad: str) -> str:
    """EffectDef.of の式を、1 行が 100 字に収まるように行を分けて書く。"""
    ch = "[" + (",\n" + pad + "  ").join(choices) + "]"
    if len(effects) == 1:
        body = f"({effects[0]})"
    else:
        body = "(.seqOf [" + (",\n" + pad + "  ").join(effects) + "])"
    return f"(.of {ch}\n{pad}{body})"


# ---- 誘発 ---------------------------------------------------------------------------------
TRIGGERS = [
    (re.compile(r"^When you play me, (?P<rest>.+)$"), [".play"]),
    (re.compile(r"^When I attack, (?P<rest>.+)$"), [".attack"]),
    (re.compile(r"^When I defend, (?P<rest>.+)$"), [".defend"]),
    (re.compile(r"^When I attack or defend, (?P<rest>.+)$"), [".attack", ".defend"]),
    (re.compile(r"^When I move, (?P<rest>.+)$"), [".move"]),
    (re.compile(r"^When I conquer, (?P<rest>.+)$"), [".conquer"]),
    (re.compile(r"^When I hold, (?P<rest>.+)$"), [".hold"]),
    (re.compile(r"^\[Deathknell\](?:\[>\]| —) (?P<rest>.+)$"), [".die"]),
    (re.compile(r"^At the end of your turn, (?P<rest>.+)$"), ["END"]),
]


# 発動に条件がある誘発（Legion、追加コストを払ったなら）。他の誘発より先に試す。
COND_TRIGGERS = [
    (re.compile(r"^\[Legion\](?:\[>\]| —) When you play me, (?P<rest>.+)$"), [".play"], ".legion"),
    (re.compile(r"^When you play me, if you paid the additional cost, (?P<rest>.+)$"),
     [".play"], ".paid"),
]

DOMAINS = {"fury", "calm", "mind", "body", "chaos", "order"}
ACTIVATED = re.compile(r"^(?P<speed>\[Reaction\]\[>\] |\[Action\]\[>\] )?"
                       r"(?P<cost>:rb_[a-z_0-9]+:(?:(?::rb_[a-z_0-9]+:|, )*:rb_[a-z_0-9]+:)?): "
                       r"(?P<rest>.+)$")


def parse_cost(text: str):
    """`:rb_energy_1::rb_rune_fury:, :rb_exhaust:` → 費用の式の列。書けなければ None。"""
    costs: list[str] = []
    pay: tuple[int, list[str]] | None = None
    for group in text.split(", "):
        syms = re.findall(r":rb_([a-z_0-9]+):", group)
        if "".join(f":rb_{x}:" for x in syms) != group:
            return None
        if syms == ["exhaust"]:
            costs.append(".exhaustSelf")
            continue
        if pay is not None:
            return None
        energy, power = 0, []
        for x in syms:
            if x.startswith("energy_"):
                energy += int(x[len("energy_"):])
            elif x == "rune_rainbow":
                power.append(".any")
            elif x.startswith("rune_") and x[len("rune_"):] in DOMAINS:
                power.append(f".domain .{x[len('rune_'):]}")
            else:
                return None
        pay = (energy, power)
    if pay is not None:
        costs.append(f".pay ⟨{pay[0]}, [{', '.join(pay[1])}]⟩")
    return costs


def parse_activated(s: str):
    """起動型能力の 1 行を、能力の式にする。書けなければ None。"""
    m = ACTIVATED.match(s)
    if not m:
        return None
    costs = parse_cost(m.group("cost"))
    if not costs:
        return None
    rest = m.group("rest")
    speed = {"[Reaction][>] ": ".reaction", "[Action][>] ": ".action", None: ".normal"}[m.group("speed")]
    if rest.startswith("[Reaction] — "):
        rest, speed = rest[len("[Reaction] — "):], ".reaction"
    r = parse_effect(rest)
    if r is None:
        return None
    choices, effects = r
    return (f".activated [{', '.join(costs)}] {speed}\n        "
            f"{fmt_effect_def(choices, effects, '        ')} .unlimited")


def parse_line(line: str, is_spell: bool):
    """1 行を (種類, 式) にする。種類は 'spell' か 'ability' か 'keyword'。合わなければ None。"""
    s = strip_reminder(line)
    if not s or KW_LINE.match(s):
        return "keyword", None
    if is_spell:
        r = parse_effect(s)
        return ("spell", r) if r else None
    m = re.match(r"^You may pay (?P<c>(?::rb_[a-z_0-9]+:)+) as an additional cost to play me\.$", s)
    if m:
        energy, power = 0, []
        for x in re.findall(r":rb_([a-z_0-9]+):", m.group("c")):
            if x.startswith("energy_"):
                energy += int(x[len("energy_"):])
            elif x == "rune_rainbow":
                power.append(".any")
            elif x.startswith("rune_") and x[len("rune_"):] in DOMAINS:
                power.append(f".domain .{x[len('rune_'):]}")
            else:
                return None
        return "extra", f"some ⟨{energy}, [{', '.join(power)}]⟩"
    act = parse_activated(s)
    if act:
        return "ability", [act]
    m = re.match(r"^\[Level (\d+)\]\[>\] I have \+(\d+) :rb_might:\.$", s)
    if m:
        return "ability", [f".passive (.cmp .ge .xp (.const {m.group(1)}))"
                           f" [.mightPlus .self (.const {m.group(2)})]"]
    if s == "I enter ready.":
        return "ability", [".passive .always [.entersReady .self]"]
    m = re.match(r"^\[Empowered\]\[>\] I have \+(\d+) :rb_might:\.$", s)
    if m:
        return "ability", [f".passive (.empowered .self) [.mightPlus .self (.const {m.group(1)})]"]
    for rx, events, cond in COND_TRIGGERS + [(r, e, None) for r, e in TRIGGERS]:
        m = rx.match(s)
        if m:
            rest = m.group("rest")
            may = False
            if rest.startswith("you may "):
                may, rest = True, rest[len("you may "):]
            rest = rest[0].upper() + rest[1:]
            r = parse_effect(rest if rest.endswith(".") else rest + ".")
            if not r:
                return None
            choices, effects = r
            if may:
                effects = [f".may ({' '.join(effects)})"] if len(effects) == 1 else None
                if effects is None:
                    return None
            abil = []
            for ev in events:
                trig = ("{ event := .at_ .endOfTurn, condition := .yourTurn }" if ev == "END"
                        else f"{{ Trigger.onSelf {ev} with condition := {cond} }}" if cond
                        else f"(.onSelf {ev})")
                abil.append(f".triggered {trig}\n        "
                            f"{fmt_effect_def(choices, effects, '        ')} .unlimited")
            return "ability", abil
    return None


GRANT_KW = {"Tank": "tank", "Shield": "shield", "Ganking": "ganking", "Assault": "assault",
            "Deflect": "deflect"}


def parse_grant_line(line: str):
    """装備が付けた Unit に与える文を、能力の式の列にする。書けなければ None。"""
    s = strip_reminder(line)
    m = re.match(r"^\[(?P<k>[A-Za-z]+)(?: (?P<n>\d+))?\]$", s)
    if m and m.group("k") in GRANT_KW:
        arg = f", arg := .amount {m.group('n')}" if m.group("n") else ""
        return [f".passive .always [.keyword .self {{ keyword := .{GRANT_KW[m.group('k')]}{arg} }}]"]
    r = parse_line(line, False)
    if r is None or r[0] != "ability":
        return None
    return r[1]


def transcribe(card: dict):
    """カードを、手書きの部分の欄（Lean の式の文字列）にする。書けなければ None。"""
    grants: list[str] = []
    if card.get("effectText"):
        if card["types"] != ["gear"]:
            return None  # 付けた Unit に与える文を持つのは、Equipment だけ
        for line in card["effectText"]:
            g = parse_grant_line(line)
            if g is None:
                return None
            grants += g
    is_spell = card["types"] == ["spell"]
    spell_parts: list[str] = []
    abilities: list[str] = []
    extra = None
    for line in card["text"]:
        r = parse_line(line, is_spell)
        if r is None:
            return None
        kind, val = r
        if kind == "spell":
            spell_parts.append(val)
        elif kind == "ability":
            abilities += val
        elif kind == "extra":
            extra = val
    fields = []
    if spell_parts:
        # 文を 1 つの効果に束ねる: 対象枠は、行の順に番号を振り直す
        text = " ".join(strip_reminder(l) for l in card["text"]
                        if not KW_LINE.match(strip_reminder(l)))
        r = parse_effect(text)
        if r is None:
            return None
        choices, effects = r
        fields.append("spellEffect := some " + fmt_effect_def(choices, effects, "      "))
    if extra:
        fields.append(f"additionalCost := {extra}")
    if abilities:
        fields.append("abilities := [" + ",\n      ".join(abilities) + "]")
    if grants:
        fields.append("grants := [" + ",\n      ".join(grants) + "]")
    return fields


STUB = r"\n/-- ([^\n]*?): the effect is not written yet\. -/\ndef {ident} : CardDef := {ident}\.meta\n"


def apply(cards: list[dict], dry: bool) -> tuple[int, int]:
    done = skipped = 0
    by_file: dict[str, list[tuple[dict, list[str]]]] = {}
    for c in cards:
        r = transcribe(c)
        if r is None:
            skipped += 1
            continue
        by_file.setdefault(c["cardId"].split("-")[0], []).append((c, r))
    for code, items in by_file.items():
        p = ROOT / "RiftboundCards" / f"{FILES[code]}.lean"
        t = p.read_text(encoding="utf8")
        for c, fields in items:
            ident = c["cardId"].replace("-", "_")
            m = re.search(STUB.format(ident=ident), t)
            if not m:
                continue  # 手書きの転記がある
            title = m.group(1)
            body = ",\n    ".join(fields + ["status := .drafted"])
            new = (f"\n/-- {title}. -/\ndef {ident} : CardDef :=\n"
                   f"  {{ {ident}.meta with\n    {body} }}\n")
            t = t[:m.start()] + new + t[m.end():]
            done += 1
        if not dry:
            p.write_text(t, encoding="utf8")
    return done, skipped


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry", action="store_true")
    args = ap.parse_args()
    data = json.loads((ROOT / "data" / "cards" / "logical.json").read_text(encoding="utf8"))
    done, skipped = apply(data["cards"], args.dry)
    print(f"{'would write' if args.dry else 'wrote'} {done} cards; {skipped} not writable",
          file=sys.stderr)


if __name__ == "__main__":
    main()
