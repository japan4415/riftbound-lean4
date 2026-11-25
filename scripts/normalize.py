"""スナップショットを正規化し、論理カードの一覧 data/cards/logical.json を作る。

    uv run --no-project python scripts/normalize.py [snapshot.json]   # 省略時は最新のスナップショット

- 論理カードのキーは「名前 + subtitle」（docs/card-data.md §3）。印刷違いは 1 枚に束ねる。
- `cardId` は最初の印刷の公開コードから、通し番号の分母を除いたもの（例: OGN-029）。
- 型は、公式ギャラリーの欄が空か食い違うとき、代替テキスト（"Riftbound Unit: ..."）で補う。
- 装備品の `effect` 欄（付けた Unit に与える文）は、`text` と別に `effectText` として持つ。
- supertype（Champion / Signature）は公式ギャラリーに無いので、ここでは埋めない。
"""
from __future__ import annotations

import argparse
import html
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# 同じ発売日のときの順序（docs/card-data.md §1 の表の上から）。LGC は予告で、まだ無い。
SET_ORDER = ["OGN", "OGS", "SFD", "UNL", "VEN", "RAD", "LGC"]
TYPE_IDS = {"unit", "spell", "gear", "legend", "battlefield", "rune"}

# https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/
# https://playriftbound.com/en-us/news/announcements/radiance-errata-updates/
TEXT_ERRATA = {
    "VEN-034": {
        "[Reaction] (Play on your turn or in showdowns.)":
            "[Reaction] (Play any time, even before spells and abilities resolve.)",
    },
    "VEN-044": {
        "your next card costs": "the next card you play this turn costs",
    },
    "VEN-086": {
        "return me to hand, give me +3 :rb_might: instead.":
            "return me to hand, give me +3 :rb_might: this turn instead.",
    },
    "RAD-010": {
        "Banish this.": "Then banish this.",
    },
    "RAD-081": {
        "give another friendly unit": "give a friendly unit",
    },
    "RAD-154": {
        "play this turn (even from face down) can":
            "play this turn, even from face down, can",
    },
    "RAD-167": {
        "choose 3 different legends": "choose up to 3 different legends",
        "one of those legends": "one of those Legends",
    },
}

# The gallery omits or mislabels these fields. Checked against its card images.
RADIANCE_PRINT_METADATA = {
    "RAD-002": {"tags": []},
    "RAD-003": {"domains": ["fury"], "tags": ["Bilgewater"]},
    "RAD-006": {"domains": ["fury"]},
    "RAD-008": {"tags": ["Demacia", "Yordle"]},
    "RAD-009": {"domains": ["fury"], "tags": ["Bandle City", "Yordle", "Mech"]},
    "RAD-022": {"domains": ["fury"]},
    "RAD-026": {"domains": ["calm"], "tags": ["Freljord"]},
    "RAD-041": {"domains": ["calm"]},
    "RAD-047": {"domains": ["mind"]},
    "RAD-049": {"domains": ["mind"], "tags": ["Zaun"]},
    "RAD-050": {"tags": ["Shurima"]},
    "RAD-054": {"tags": ["Bandle City", "Yordle"]},
    "RAD-055": {"tags": ["Piltover", "Mech"]},
    "RAD-058": {"tags": ["Bilgewater"]},
    "RAD-059": {"domains": ["mind"]},
    "RAD-071": {"domains": ["body"], "tags": ["Equipment"]},
    "RAD-077": {"tags": ["Freljord", "Spirit"]},
    "RAD-088": {"tags": ["Freljord"]},
    "RAD-093": {"domains": ["chaos"], "tags": ["Bandle City", "Yordle"]},
    "RAD-097": {"tags": ["Bilgewater"]},
    "RAD-104": {"domains": ["chaos"], "tags": ["Shadow Isles", "Cat"]},
    "RAD-118": {"tags": ["Shurima"]},
    "RAD-121": {"domains": ["order"]},
    "RAD-123": {"domains": ["order"], "tags": ["Equipment"]},
    "RAD-128": {"tags": ["Demacia"]},
    "RAD-134": {"domains": ["order"]},
}


def latest_snapshot() -> Path:
    files = sorted((ROOT / "data" / "snapshots").glob("gallery-*.json"))
    if not files:
        raise SystemExit("no snapshot: run scripts/fetch.py first")
    return files[-1]


def card_id(code: str) -> str:
    """OGN-029/298 -> OGN-029、OGN-029a/298 -> OGN-029、UNL-T04 -> UNL-T04。"""
    head = code.split("/")[0]
    return re.sub(r"[a-z*]+$", "", head)


def print_key(p: dict) -> tuple:
    """最初の印刷を決める順序: 弾の順、通し番号。発売日は弾の順で代用する。"""
    s = SET_ORDER.index(p["set"]) if p["set"] in SET_ORDER else len(SET_ORDER)
    return (s, p["num"], p["code"])


def alt_types(alt: str) -> list[str]:
    m = re.match(r"Riftbound ([^:]*):", alt)
    if not m:
        return []
    return [t.strip().lower() for t in m.group(1).split(",") if t.strip()]


def fixed_types(p: dict) -> tuple[list[str], str | None]:
    """型と、補正したときの理由。"""
    given = p["types"]
    alt = [t for t in alt_types(p["alt"]) if t in TYPE_IDS]
    if not alt:
        return given, None
    if sorted(given) == sorted(alt):
        return given, None
    return alt, "empty" if not given else "mismatch"


def plain(body: str | None) -> list[str]:
    """HTML の文面を、段落ごとの行にする。キーワードの [ ] はそのまま残す。"""
    if not body:
        return []
    s = re.sub(r"<br\s*/?>", "\n", body)
    s = re.sub(r"</p>\s*<p>", "\n", s)
    s = re.sub(r"<[^>]+>", "", s)
    return [line.strip() for line in html.unescape(s).split("\n") if line.strip()]


def rules_text(p: dict) -> tuple[str, ...]:
    """比較用の文面: 注釈文（括弧の中）と「文面なし」の印を除く。"""
    lines = plain(p["text"]) + plain(p["effect"])
    lines = [re.sub(r"\s*\([^)]*\)", "", line).strip() for line in lines]
    return tuple(line for line in lines if line and line != "[NO TEXT]")


def normalize(snap: dict) -> dict:
    groups: dict[tuple, list[dict]] = {}
    for p in snap["items"]:
        groups.setdefault((p["name"], p["subtitle"]), []).append(p)

    cards = []
    fixes = []
    for (name, subtitle), ps in groups.items():
        ps.sort(key=print_key)
        first = ps[0]
        types, why = fixed_types(first)
        if why:
            fixes.append({"code": first["code"], "name": name, "reason": why,
                          "given": first["types"], "used": types})
        ident = card_id(first["code"])
        text = plain(first["text"])
        for printed, corrected in TEXT_ERRATA.get(ident, {}).items():
            text = [line.replace(printed, corrected) for line in text]
        if ident == "RAD-071":
            text = [line.replace("Equip :rb_energy_1:", "[Equip] :rb_energy_1:", 1) for line in text]
        effect_text = plain(first["effect"])
        variants = sorted({rules_text(p) for p in ps} - {()})
        cards.append({
            "cardId": ident,
            "name": name,
            "subtitle": subtitle,
            "types": types,
            "domains": first["domains"],
            "tags": first["tags"],
            "energy": first["energy"],
            "power": first["power"],
            "might": first["might"],
            "mightBonus": first["mightBonus"],
            "text": text,
            "effectText": effect_text,
            "textVariants": max(len(variants), 1),
            "sets": sorted({p["set"] for p in ps}, key=SET_ORDER.index),
            "printings": [p["code"] for p in ps],
            **RADIANCE_PRINT_METADATA.get(ident, {}),
        })
    cards.sort(key=lambda c: (SET_ORDER.index(c["sets"][0]), c["cardId"]))
    ids = [c["cardId"] for c in cards]
    dup = sorted({i for i in ids if ids.count(i) > 1})
    if dup:
        raise SystemExit(f"cardId collision: {dup}")
    return {"snapshot": snap["fetched"], "count": len(cards), "typeFixes": fixes, "cards": cards}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("snapshot", nargs="?")
    ap.add_argument("--out", default=str(ROOT / "data" / "cards" / "logical.json"))
    ap.add_argument("--check", action="store_true", help="書き換えず、差分があれば失敗する")
    args = ap.parse_args()
    path = Path(args.snapshot) if args.snapshot else latest_snapshot()
    result = normalize(json.loads(path.read_text(encoding="utf8")))
    out = Path(args.out)
    text = json.dumps(result, ensure_ascii=False, indent=1, sort_keys=True) + "\n"
    if args.check:
        if not out.exists() or out.read_text(encoding="utf8") != text:
            raise SystemExit(f"{out} is out of date: run scripts/normalize.py")
        print(f"{out} is up to date ({result['count']} logical cards)", file=sys.stderr)
        return
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text, encoding="utf8")
    print(f"wrote {out}: {result['count']} logical cards, {len(result['typeFixes'])} type fixes",
          file=sys.stderr)


if __name__ == "__main__":
    main()
