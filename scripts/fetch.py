"""公式カードギャラリーから取得し、日付つきのスナップショット JSON を作る。

    uv run --no-project python scripts/fetch.py                  # 取得して data/snapshots/ に書く
    uv run --no-project python scripts/fetch.py --from-html F    # 保存済みの HTML から作る（取得しない）

標準ライブラリだけで動く。画像・アイコン・イラストレーターは残さない（文面と数値だけ）。
User-Agent に個人の連絡先は入れない（docs/card-data.md §3）。
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import sys
import urllib.request
from pathlib import Path

URL = "https://playriftbound.com/en-us/card-gallery/"
USER_AGENT = "riftbound-lean4/0.1 (non-commercial research)"
ROOT = Path(__file__).resolve().parent.parent


def next_data(html: str) -> dict:
    m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.S)
    if not m:
        raise SystemExit("__NEXT_DATA__ not found: the page layout may have changed")
    return json.loads(m.group(1))


def gallery_blade(data: dict) -> dict:
    blades = data["props"]["pageProps"]["page"]["blades"]
    found = [b for b in blades if b.get("type") == "riftboundCardGallery"]
    if len(found) != 1:
        raise SystemExit(f"expected one riftboundCardGallery blade, found {len(found)}")
    return found[0]


def num(field: dict | None) -> int | None:
    if not field:
        return None
    v = field["value"]["id"]
    return v if isinstance(v, int) else int(v)


def html_body(field: dict | None) -> str | None:
    if not field:
        return None
    return field["richText"]["body"]


def trim(item: dict) -> dict:
    """文面と数値だけを残す。"""
    out = {
        "code": item["publicCode"],
        "id": item["id"],
        "num": item["collectorNumber"],
        "name": item["name"],
        "subtitle": item.get("subtitle"),
        "set": item["set"]["value"]["id"],
        "types": [t["id"] for t in item["cardType"]["type"]],
        "rarity": item["rarity"]["value"]["id"],
        "domains": [d["id"] for d in item["domain"]["values"]],
        "tags": item.get("tags", {}).get("tags", []),
        "energy": num(item.get("energy")),
        "power": num(item.get("power")),
        "might": num(item.get("might")),
        "mightBonus": num(item.get("mightBonus")),
        "text": html_body(item.get("text")),
        "effect": html_body(item.get("effect")),
        "orientation": item["orientation"],
        "alt": item["cardImage"].get("accessibilityText", ""),
    }
    return out


def snapshot(html: str, fetched: str) -> dict:
    blade = gallery_blade(next_data(html))
    items = [trim(i) for i in blade["cards"]["items"]]
    items.sort(key=lambda i: i["code"])
    reported = blade["cards"]["async"]["metadata"]["totalItems"]
    return {
        "source": URL,
        "fetched": fetched,
        "reportedTotal": reported,
        "count": len(items),
        "items": items,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--from-html", help="取得せず、保存済みの HTML から作る")
    ap.add_argument("--out", default=str(ROOT / "data" / "snapshots"))
    args = ap.parse_args()

    if args.from_html:
        html = Path(args.from_html).read_text(encoding="utf8")
    else:
        req = urllib.request.Request(URL, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=60) as r:
            html = r.read().decode("utf8")

    today = datetime.date.today().isoformat()
    snap = snapshot(html, today)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    path = out / f"gallery-{today}.json"
    path.write_text(json.dumps(snap, ensure_ascii=False, indent=1, sort_keys=True) + "\n",
                    encoding="utf8")
    print(f"wrote {path} ({snap['count']} of {snap['reportedTotal']} printings)", file=sys.stderr)


if __name__ == "__main__":
    main()
