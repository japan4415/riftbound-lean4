"""カードの実装状況の表（docs/coverage.md）を、RiftboundCards/*.lean から作る。

    uv run --no-project python scripts/coverage.py            # docs/coverage.md を書く
    uv run --no-project python scripts/coverage.py --check    # 書き換えず、古ければ失敗する

数えるのは、手書きの部分の `status := .<状態>`（無ければ todo）と、効果の欄（`spellEffect`・
`abilities`）の有無、`custom` の使用。docs/card-data.md §6 の表。
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SETS = [("OGN", "Origins", "Origins"), ("OGS", "ProvingGrounds", "Proving Grounds"),
        ("SFD", "Spiritforged", "Spiritforged"), ("UNL", "Unleashed", "Unleashed"),
        ("VEN", "Vendetta", "Vendetta"), ("RAD", "Radiance", "Radiance")]
STATES = ["todo", "drafted", "partial", "full"]

BLOCK = re.compile(r"-- END GENERATED\n(?P<hand>.*?)(?=-- BEGIN GENERATED |\Z)", re.S)


def analyse(path: Path) -> dict:
    text = path.read_text(encoding="utf8")
    # 弾ごとの一覧の生成ブロックより前だけを見る
    text = text.split("-- BEGIN GENERATED LIST")[0]
    n = {s: 0 for s in STATES}
    n.update(total=0, withEffect=0, keywordOnly=0, custom=0)
    for m in BLOCK.finditer(text):
        hand = m.group("hand")
        if "def " not in hand:
            continue
        n["total"] += 1
        s = re.search(r"status := \.(\w+)", hand)
        state = s.group(1) if s else "todo"
        n[state] += 1
        if state != "todo":
            if "spellEffect :=" in hand or "abilities :=" in hand:
                n["withEffect"] += 1
            else:
                n["keywordOnly"] += 1
        n["custom"] += hand.count(".custom")
    return n


def pct(a: int, b: int) -> str:
    return f"{100 * a / b:.1f}%" if b else "-"


def render() -> str:
    rows = [(name, analyse(ROOT / "RiftboundCards" / f"{ns}.lean")) for _, ns, name in SETS]
    tot = {k: sum(r[k] for _, r in rows) for k in rows[0][1]}
    out = ["# カードの実装状況", "",
           "`scripts/coverage.py` が `RiftboundCards/*.lean` から作る。手で編集しない。",
           "「IR で書けた」は、`drafted` 以上（効果を IR の値として書いた、または書く効果が無い）。",
           "意味を与えて検査した（`full`）カードは、解釈器ができるまで無い。", "",
           "| 弾 | 全部 | todo | drafted | partial | full | IR で書けた割合 | 効果あり | キーワードだけ | custom |",
           "|---|---|---|---|---|---|---|---|---|---|"]
    for name, r in rows + [("**合計**", tot)]:
        done = r["drafted"] + r["partial"] + r["full"]
        out.append(f"| {name} | {r['total']} | {r['todo']} | {r['drafted']} | {r['partial']} | "
                   f"{r['full']} | {pct(done, r['total'])} | {r['withEffect']} | "
                   f"{r['keywordOnly']} | {r['custom']} |")
    out += ["", "- 「効果あり」は `spellEffect` か `abilities` を書いたカード、「キーワードだけ」は、"
            "印刷されたキーワードだけで、書く効果が無いカード。",
            "- 書けなかった文の一覧と、IR を直した記録は [ir-gaps.md](ir-gaps.md)。", ""]
    return "\n".join(out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text = render()
    out = ROOT / "docs" / "coverage.md"
    if args.check:
        if not out.exists() or out.read_text(encoding="utf8") != text:
            raise SystemExit(f"{out} is out of date: run scripts/coverage.py")
        print(f"{out.name} is up to date", file=sys.stderr)
        return
    out.write_text(text, encoding="utf8")
    print(text)


if __name__ == "__main__":
    main()
