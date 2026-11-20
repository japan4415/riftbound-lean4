"""Riftbound/ と RiftboundCards/ の Lean ファイルから、規則番号の引用を抽出して検査する。

引用の形式は `(CR 323.4)` / `(TR 402.1)`、複数のときは `(CR 323.4, 142.4.b)`
（docs/lean-guidelines.md §4.3）。この形式を外れた `CR 323.4` / `TR 402.1` は誤りとして報告する。

使い方:
    uv run --no-project python scripts/cr_citations.py            # 検査と要約
    uv run --no-project python scripts/cr_citations.py --table    # 規則ごとの表（Markdown）を出力
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIRS = ["Riftbound", "RiftboundCards"]

NUM = r"\d+(?:\.[0-9a-z]+)*"
ITEM = rf"{NUM}(?:-{NUM})?"  # 単独の番号か、範囲（805-832、601.2-3）
CITATION = re.compile(rf"\((CR|TR) ({ITEM}(?:, ?{ITEM})*)\)")
BARE = re.compile(r"\b(?:CR|TR) \d")


def lean_files() -> list[Path]:
    files: list[Path] = []
    for d in SOURCE_DIRS:
        files += sorted((ROOT / d).rglob("*.lean"))
    return files


def scan(path: Path) -> tuple[list[tuple[int, str, str]], list[tuple[int, str]]]:
    """(引用: 行番号, 文書, 規則番号) と (誤り: 行番号, 行) を返す。"""
    cites: list[tuple[int, str, str]] = []
    bad: list[tuple[int, str]] = []
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        for m in CITATION.finditer(line):
            for rule in re.split(r", ?", m.group(2)):
                cites.append((lineno, m.group(1), rule))
        if BARE.search(CITATION.sub("", line)):
            bad.append((lineno, line.strip()))
    return cites, bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--table", action="store_true", help="規則ごとの引用箇所の表を Markdown で出力する")
    args = ap.parse_args()

    by_rule: dict[tuple[str, str], list[str]] = defaultdict(list)
    problems = 0
    files = lean_files()
    for f in files:
        cites, bad = scan(f)
        rel = f.relative_to(ROOT)
        for lineno, doc, rule in cites:
            by_rule[(doc, rule)].append(f"{rel}:{lineno}")
        for lineno, line in bad:
            print(f"BAD CITATION {rel}:{lineno}: {line}", file=sys.stderr)
            problems += 1

    if args.table:
        print("| 規則 | 引用箇所 |")
        print("|---|---|")
        for (doc, rule), places in sorted(by_rule.items()):
            print(f"| {doc} {rule} | {', '.join(places)} |")
    else:
        total = sum(len(v) for v in by_rule.values())
        print(f"files: {len(files)}, citations: {total}, distinct rules: {len(by_rule)}, malformed: {problems}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
