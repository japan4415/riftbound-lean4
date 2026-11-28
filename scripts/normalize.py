"""スナップショットを正規化し、論理カードの一覧 data/cards/logical.json を作る。

    uv run --no-project python scripts/normalize.py [snapshot.json]   # 省略時は最新のスナップショット

- 論理カードのキーは「名前 + subtitle」（docs/card-data.md §3）。印刷違いは 1 枚に束ねる。
- `cardId` は最初の印刷の公開コードから、通し番号の分母を除いたもの（例: OGN-029）。
- 型は、公式ギャラリーの欄が空か食い違うとき、代替テキスト（"Riftbound Unit: ..."）で補う。
- 装備品の `effect` 欄（付けた Unit に与える文）は、`text` と別に `effectText` として持つ。
- 公式ギャラリーの欄とカード画像が異なる場合は、画像で確認できた値を補う。
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

# https://playriftbound.com/en-us/news/rules-and-releases/riftbound-origins-card-errata/
# https://playriftbound.com/en-us/news/rules-and-releases/riftbound-spiritforged-errata/
# https://playriftbound.com/en-us/news/rules-and-releases/unleashed-errata-updates/
# https://playriftbound.com/en-us/news/announcements/vendetta-errata-updates/
# https://playriftbound.com/en-us/news/announcements/radiance-errata-updates/
TEXT_ERRATA = {
    "OGN-077": {
        "The next time a friendly unit would die, kill this instead. Recall that unit exhausted.":
            "If a friendly unit would die, kill this instead. Heal that unit, exhaust it, and recall it.",
    },
    "OGN-287": {
        "When you conquer here, recycle one of your runes.":
            "When you conquer here, you must recycle one of your runes. (This doesn't choose anything.)",
    },
    "OGN-289": {"ready 2 runes at the end of this turn": "ready up to 2 runes at the end of this turn"},
    "OGN-296": {
        "Spells and abilities affecting units here each deal 1 Bonus Damage. (Each instance of damage the spell deals is increased by 1.)":
            "Spells and abilities deal 1 Bonus Damage to units here. (Each instance of damage the spell deals to a unit here is increased by 1.)",
    },
    "SFD-020": {
        "When I attack or defend, you may pay :rb_rune_fury:. If you do, give me":
            "When I attack or defend, you may pay :rb_rune_fury: to give me",
    },
    "SFD-053": {
        "then move an enemy unit from here to its base.":
            "then move up to one enemy unit from here to its base.",
    },
    "SFD-140": {
        "ignoring its Energy cost. Recycle that spell after you play it.":
            "ignoring its Energy cost. Then recycle it.",
    },
    "SFD-163": {
        "Kill a friendly unit to give +:rb_might: equal to its Might to another friendly unit this turn. Draw 1.":
            "Kill a friendly unit. If you do, give +:rb_might: equal to its Might to another friendly unit this turn.\nDraw 1.",
    },
    "SFD-207": {
        "to its owner's hand. If you do, play a 2": "to its owner's hand to play a 2",
    },
    "UNL-079": {
        "When a showdown begins here, you may pay :rb_energy_1:. If you do, [Predict]":
            "When a showdown begins here, you may pay :rb_energy_1: to [Predict]",
    },
    "UNL-081": {
        "tokens here. They become copies of me.":
            "tokens here. Then do this: They become copies of me.",
    },
    "UNL-166": {
        "You may play me to its battlefield (even if you don't have other units there).":
            "You may [Ambush] me to its battlefield, even if you don't have other units there.",
    },
    "UNL-199": {
        "token there. It becomes a copy": "token there. Then do this: It becomes a copy",
    },
    "UNL-200": {
        "to your base. It becomes a copy": "to your base. Then do this: It becomes a copy",
    },
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
    "RAD-127": {
        "base instead.disa": "base instead.",
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

# The gallery omits some printed supertypes and split-domain Power symbols.
# https://playriftbound.com/en-us/news/announcements/from-garen-to-annie-rq-houstons-top-decks/
# https://cmsassets.rgpub.io/sanity/images/dsfx7636/game_data_live/57f646b0393b58b657cfabf66357d9fc4a34e046-744x1039.png
ORIGINS_PRINT_METADATA = {
    "OGN-151": {"supertypes": ["champion"]},
    "OGN-238": {"supertypes": ["champion"]},
    "OGN-254": {"supertypes": ["signature"], "powerOwn": True},
}

# Signature marks and split-domain Power symbols on Riot's Proving Grounds card images.
PROVING_GROUNDS_PRINT_METADATA = {
    "OGS-004": {"supertypes": ["champion"]},
    "OGS-009": {"supertypes": ["champion"]},
    "OGS-018": {"supertypes": ["signature"], "powerOwn": True},
    "OGS-020": {"supertypes": ["signature"]},
    "OGS-022": {"supertypes": ["signature"]},
    "OGS-024": {"supertypes": ["signature"], "powerOwn": True},
}

# The gallery omits or mislabels these fields. Checked against its card images.
UNLEASHED_PRINT_METADATA = {
    "UNL-059": {"supertypes": ["champion"]},
    "UNL-086": {"supertypes": ["champion"]},
    "UNL-090": {"supertypes": ["champion"]},
    "UNL-113": {"supertypes": ["champion"]},
    "UNL-172": {"supertypes": ["champion"]},
    "UNL-192": {"supertypes": ["signature"], "powerOwn": True},
    "UNL-200": {"supertypes": ["signature"], "powerOwn": True},
}

# Riot lists the six chosen Champion options for the Vi and Vex decks.
# https://playriftbound.com/en-us/news/announcements/vi--vex-champion-decks/
# The printed Shadow and Hextech Gauntlets in the official gallery carry Signature.
CHAMPION_DECK_PRINT_METADATA = {
    "OGN-036": {"supertypes": ["champion"]},
    "SFD-146": {"supertypes": ["champion"]},
    "UNL-030": {"supertypes": ["champion"]},
    "UNL-055": {"supertypes": ["champion"]},
    "UNL-150": {"supertypes": ["champion"]},
    "UNL-176": {"supertypes": ["champion"]},
    "UNL-188": {"supertypes": ["signature"]},
    "UNL-194": {"supertypes": ["signature"]},
}

RADIANCE_PRINT_METADATA = {
    "RAD-001": {"domains": ["fury"], "tags": ["Bandle City", "Yordle"]},
    "RAD-002": {"tags": []},
    "RAD-003": {"domains": ["fury"], "tags": ["Bilgewater"]},
    "RAD-004": {"domains": ["fury"]},
    "RAD-005": {"tags": ["Shadow Isles", "Spirit"]},
    "RAD-006": {"domains": ["fury"]},
    "RAD-008": {"tags": ["Demacia", "Yordle"]},
    "RAD-009": {"domains": ["fury"], "tags": ["Bandle City", "Yordle", "Mech"]},
    "RAD-011": {"tags": ["Piltover", "Mech"]},
    "RAD-014": {"tags": ["Bilgewater"]},
    "RAD-016": {"domains": ["fury"], "tags": ["Shurima"]},
    "RAD-017": {"domains": ["fury"], "tags": []},
    "RAD-018": {"tags": ["Noxus"]},
    "RAD-019": {"tags": ["Freljord"]},
    "RAD-021": {"supertypes": ["champion"], "tags": ["Ekko", "Zaun"]},
    "RAD-022": {"domains": ["fury"]},
    "RAD-023": {"supertypes": ["champion"], "tags": ["Ziggs", "Zaun", "Yordle"]},
    "RAD-024": {"domains": ["calm"], "tags": []},
    "RAD-026": {"domains": ["calm"], "tags": ["Freljord"]},
    "RAD-027": {"tags": ["Ixtal", "Bird"]},
    "RAD-030": {"tags": ["Shurima"]},
    "RAD-031": {"tags": ["Bilgewater", "Sentinel"]},
    "RAD-035": {"domains": ["calm"], "tags": []},
    "RAD-036": {"tags": ["Freljord", "Bird"]},
    "RAD-037": {"tags": ["Piltover"]},
    "RAD-040": {"tags": ["Shadow Isles", "Spirit"]},
    "RAD-041": {"domains": ["calm"]},
    "RAD-042": {"supertypes": ["champion"], "tags": ["Orianna", "Piltover"]},
    "RAD-043": {"supertypes": ["champion"], "tags": ["Riven", "Noxus"]},
    "RAD-044": {"tags": []},
    "RAD-045": {"supertypes": ["champion"], "tags": ["K'Sante", "Shurima"]},
    "RAD-047": {"domains": ["mind"]},
    "RAD-049": {"domains": ["mind"], "tags": ["Zaun"]},
    "RAD-050": {"tags": ["Shurima"]},
    "RAD-052": {"tags": []},
    "RAD-053": {"tags": ["Freljord", "Bird"]},
    "RAD-054": {"tags": ["Bandle City", "Yordle"]},
    "RAD-055": {"tags": ["Piltover", "Mech"]},
    "RAD-057": {"tags": ["Piltover", "Mech"]},
    "RAD-058": {"tags": ["Bilgewater"]},
    "RAD-059": {"domains": ["mind"]},
    "RAD-060": {"tags": ["Ionia", "Dragon"]},
    "RAD-061": {"supertypes": ["champion"], "tags": ["Ekko", "Zaun"]},
    "RAD-062": {"domains": ["mind"], "tags": []},
    "RAD-065": {"supertypes": ["champion"], "tags": ["Seraphine", "Piltover"]},
    "RAD-066": {"tags": ["Freljord", "Spirit"]},
    "RAD-067": {"domains": ["mind"], "tags": ["Shurima"]},
    "RAD-071": {"domains": ["body"], "tags": ["Equipment"]},
    "RAD-072": {"tags": ["Bandle City", "Yordle"]},
    "RAD-073": {"domains": ["body"], "tags": []},
    "RAD-074": {"tags": ["Freljord"]},
    "RAD-075": {"tags": ["Demacia", "Elite", "Bird"]},
    "RAD-077": {"tags": ["Freljord", "Spirit"]},
    "RAD-078": {"tags": ["Noxus"]},
    "RAD-080": {"tags": ["Shurima"]},
    "RAD-081": {"domains": ["body"], "tags": ["Freljord"]},
    "RAD-083": {"tags": ["Mount Targon"]},
    "RAD-085": {"supertypes": ["champion"]},
    "RAD-086": {"supertypes": ["champion"], "tags": ["K'Sante", "Shurima"]},
    "RAD-087": {"tags": []},
    "RAD-088": {"tags": ["Freljord"]},
    "RAD-090": {"supertypes": ["champion"], "tags": ["Evelynn", "Demon"]},
    "RAD-092": {"tags": ["Mount Targon", "Dragon"]},
    "RAD-093": {"domains": ["chaos"], "tags": ["Bandle City", "Yordle"]},
    "RAD-094": {"tags": ["Zaun"]},
    "RAD-095": {"tags": ["Shadow Isles", "Demon"]},
    "RAD-097": {"tags": ["Bilgewater"]},
    "RAD-099": {"tags": ["Bilgewater", "Demon"]},
    "RAD-103": {"tags": ["Zaun"]},
    "RAD-104": {"domains": ["chaos"], "tags": ["Shadow Isles", "Cat"]},
    "RAD-105": {"tags": ["Piltover"]},
    "RAD-106": {"domains": ["chaos"], "tags": []},
    "RAD-107": {"tags": ["Shadow Isles", "Demon"]},
    "RAD-108": {"domains": ["chaos"], "tags": []},
    "RAD-110": {"supertypes": ["champion"], "tags": ["Lulu", "Bandle City", "Yordle"]},
    "RAD-111": {"domains": ["chaos"], "tags": []},
    "RAD-112": {"supertypes": ["champion"], "tags": ["Ziggs", "Zaun", "Yordle"]},
    "RAD-113": {"tags": ["Bilgewater", "Dragon"]},
    "RAD-114": {"supertypes": ["champion"], "tags": ["Riven", "Noxus"]},
    "RAD-115": {"tags": ["Bilgewater"]},
    "RAD-116": {"tags": []},
    "RAD-118": {"tags": ["Shurima"]},
    "RAD-119": {"tags": ["Demacia", "Dog"]},
    "RAD-120": {"tags": ["Piltover"]},
    "RAD-121": {"domains": ["order"]},
    "RAD-122": {"tags": ["Zaun"]},
    "RAD-123": {"domains": ["order"], "tags": ["Equipment"]},
    "RAD-124": {"domains": ["order"], "power": 1},
    "RAD-125": {"tags": ["The Void"]},
    "RAD-126": {"tags": ["Shadow Isles", "Spirit"]},
    "RAD-128": {"tags": ["Demacia"]},
    "RAD-129": {"tags": ["Noxus", "Trifarian"]},
    "RAD-130": {"tags": ["Demacia"]},
    "RAD-131": {"tags": ["Demacia"]},
    "RAD-133": {"supertypes": ["champion"], "tags": ["Jarvan IV", "Demacia"]},
    "RAD-134": {"domains": ["order"]},
    "RAD-136": {"tags": []},
    "RAD-137": {"supertypes": ["champion"], "tags": ["Mordekaiser", "Noxus", "Spirit"]},
    "RAD-141": {"tags": ["Ziggs"]},
    "RAD-142": {"supertypes": ["signature"], "powerOwn": True},
    "RAD-144": {"supertypes": ["signature"], "powerOwn": True},
    "RAD-146": {"supertypes": ["signature"], "tags": ["Orianna"], "powerOwn": True},
    "RAD-148": {"supertypes": ["signature"], "powerOwn": True},
    "RAD-150": {"supertypes": ["signature"], "powerOwn": True},
    "RAD-152": {"supertypes": ["signature"], "powerOwn": True},
    "RAD-156": {"supertypes": ["signature"], "tags": ["Jarvan IV"], "powerOwn": True},
    "RAD-SP3": {"supertypes": ["champion"], "tags": ["Evelynn", "Demon"]},
    "RAD-SP4": {"supertypes": ["champion"], "tags": ["Kai'Sa", "The Void"]},
    "RAD-SP5": {"supertypes": ["champion"], "tags": ["Seraphine", "Piltover"]},
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
            text = [paragraph for line in text for paragraph in line.replace(printed, corrected).splitlines()]
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
            **ORIGINS_PRINT_METADATA.get(ident, {}),
            **PROVING_GROUNDS_PRINT_METADATA.get(ident, {}),
            **UNLEASHED_PRINT_METADATA.get(ident, {}),
            **CHAMPION_DECK_PRINT_METADATA.get(ident, {}),
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
