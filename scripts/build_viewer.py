"""トレースの JSON を viewer/index.html に埋め込み、単体で開ける HTML を書き出す。

    uv run --no-project python scripts/build_viewer.py trace.json out.html
    lake exe riftbound-trace 1 4 | uv run --no-project python scripts/build_viewer.py - out.html

トレースを埋め込まない HTML は viewer/index.html のまま開き、JSON を選んで読み込む。
"""
import json
import sys
from pathlib import Path

PLACEHOLDER = "/*__TRACE__*/null"


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    src, dst = sys.argv[1], Path(sys.argv[2])
    raw = sys.stdin.read() if src == "-" else Path(src).read_text(encoding="utf-8")
    trace = json.loads(raw)  # 壊れた JSON はここで止める
    template = (Path(__file__).resolve().parent.parent / "viewer" / "index.html").read_text(encoding="utf-8")
    if template.count(PLACEHOLDER) != 1:
        print("viewer/index.html のプレースホルダが 1 つではない", file=sys.stderr)
        return 1
    # </script> で HTML が途切れないようにする
    body = json.dumps(trace, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    dst.write_text(template.replace(PLACEHOLDER, body), encoding="utf-8")
    print(f"wrote {dst} ({len(trace['steps'])} steps)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
