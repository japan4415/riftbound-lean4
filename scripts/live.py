"""ビューアのライブ操作: ローカルの橋渡し。

    lake build riftbound-live
    uv run --no-project python scripts/live.py [--port 8765]

http://127.0.0.1:8765/ を開くと、viewer/index.html が出る。画面のボタンで答えを選ぶと、この橋渡しが
Lean の実行ファイル（riftbound-live）に 1 行のコマンドを送り、返ってきた JSON をそのまま画面へ返す。
ルールは Lean だけにあり、この橋渡しも画面も、規則を持たない。

- 127.0.0.1 だけで待ち受ける。Host と Origin を確かめ、POST は JSON だけを受ける。
- ゲームは 1 つだけ（Lean の子プロセスが持つ）。「新しいゲーム」で作り直す。
"""
import argparse
import json
import re
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parent.parent
CARD_ID = re.compile(r"[A-Za-z0-9_-]{1,24}")


class Lean:
    """riftbound-live を子プロセスとして持ち、1 行送って 1 行受け取る。"""

    def __init__(self, exe: Path) -> None:
        self.proc = subprocess.Popen([str(exe)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, encoding="utf-8", bufsize=1)
        self.lock = threading.Lock()

    def ask(self, line: str) -> str:
        with self.lock:
            assert self.proc.stdin and self.proc.stdout
            self.proc.stdin.write(line + "\n")
            self.proc.stdin.flush()
            out = self.proc.stdout.readline()
            if not out:
                raise RuntimeError("riftbound-live が終了した")
            return out

    def close(self) -> None:
        try:
            if self.proc.stdin:
                self.proc.stdin.write("quit\n")
                self.proc.stdin.flush()
        except OSError:
            pass
        self.proc.terminate()


def make_handler(lean: Lean, port: int):
    page_path = ROOT / "viewer" / "index.html"
    hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):  # 静かに
            pass

        def _send(self, code: int, body: bytes, ctype: str) -> None:
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _json(self, code: int, obj) -> None:
            self._send(code, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                       "application/json; charset=utf-8")

        def _allowed(self) -> bool:
            if self.headers.get("Host", "") not in hosts:
                return False
            origin = self.headers.get("Origin")
            return origin is None or urlparse(origin).netloc in hosts

        def do_GET(self) -> None:
            if not self._allowed():
                return self._json(403, {"error": "forbidden"})
            path = urlparse(self.path).path
            if path in ("/", "/index.html"):
                return self._send(200, page_path.read_bytes(), "text/html; charset=utf-8")
            if path == "/api/ping":
                return self._json(200, {"live": True})
            if path == "/art.json":
                art = ROOT / "viewer" / "art.json"
                body = art.read_bytes() if art.is_file() else b"{}"
                return self._send(200, body, "application/json; charset=utf-8")
            self._json(404, {"error": "not found"})

        def do_POST(self) -> None:
            if not self._allowed():
                return self._json(403, {"error": "forbidden"})
            if not self.headers.get("Content-Type", "").startswith("application/json"):
                return self._json(415, {"error": "JSON only"})
            try:
                n = int(self.headers.get("Content-Length", "0"))
                req = json.loads(self.rfile.read(n) or b"{}")
                path = urlparse(self.path).path
                if path == "/api/start":
                    seed = int(req.get("seed", 1))
                    humans = str(req.get("humans", "0"))
                    kind = str(req.get("kind", "core"))
                    match = str(req.get("match", "single"))
                    if (seed < 0 or humans not in ("0", "1", "01")
                            or kind not in ("core", "constructed", "sealed", "draft")
                            or match not in ("single", "bo1", "bo3")):
                        return self._json(400, {"error": "bad start"})
                    line = f"start {seed} {humans} {kind} {match}"
                elif path in ("/api/register-start", "/api/register-team-start"):
                    team = path == "/api/register-team-start"
                    seed = int(req.get("seed", 1))
                    humans = str(req.get("humans", "0123" if team else "01"))
                    valid_humans = (bool(humans) and set(humans) <= set("0123") and len(set(humans)) == len(humans)
                                    if team else humans in ("0", "1", "01"))
                    if seed < 0 or not valid_humans:
                        return self._json(400, {"error": "bad start"})
                    start = "start-team-json" if team else "start-json"
                    line = f"{start} {seed} {humans} {json.dumps(req['setup'], ensure_ascii=True)}"
                elif path == "/api/clock":
                    line = "clock"
                elif path == "/api/time-between-games":
                    line = "time-between-games"
                elif path == "/api/replay":
                    line = "replay"
                elif path == "/api/register":
                    seat = int(req["seat"])
                    if seat not in (0, 1, 2, 3):
                        return self._json(400, {"error": "bad seat"})
                    line = f"register {seat} {json.dumps(req['registration'], ensure_ascii=True)}"
                elif path == "/api/concede-match":
                    seat = int(req["seat"])
                    if seat not in (0, 1, 2, 3):
                        return self._json(400, {"error": "bad seat"})
                    line = f"concede-match {seat}"
                elif path == "/api/agree-match-draw":
                    line = "agree-match-draw"
                elif path == "/api/judge":
                    line = "judge"
                elif path == "/api/undo":
                    line = "undo"
                elif path == "/api/bo1-first":
                    choice = req.get("choice")
                    if choice not in ("first", "second"):
                        return self._json(400, {"error": "bad choice"})
                    line = f"bo1-first {choice}"
                elif path == "/api/bo1-sideboard":
                    line = "bo1-sideboard"
                elif path == "/api/swap":
                    out, inn = str(req.get("out", "")), str(req.get("in", ""))
                    if not (CARD_ID.fullmatch(out) and CARD_ID.fullmatch(inn)):
                        return self._json(400, {"error": "bad card"})
                    line = f"swap {out} {inn}"
                    if "seat" in req:
                        seat = int(req["seat"])
                        if seat not in (0, 1, 2, 3):
                            return self._json(400, {"error": "bad seat"})
                        line += f" {seat}"
                elif path == "/api/next":
                    choice = req.get("choice")
                    if choice not in (None, "first", "second"):
                        return self._json(400, {"error": "bad choice"})
                    line = "next" + (f" {choice}" if choice else "")
                elif path == "/api/team-next":
                    order = req.get("order")
                    if order is not None and (not isinstance(order, list) or len(order) != 4
                                              or not all(type(seat) is int and 0 <= seat < 4 for seat in order)
                                              or len(set(order)) != 4):
                        return self._json(400, {"error": "bad team order"})
                    digits = "".join(map(str, order)) if order is not None else "-"
                    line = f"team-next {digits}"
                    if "decks" in req:
                        line += " " + json.dumps(req["decks"], ensure_ascii=True)
                elif path == "/api/act":
                    k = int(req["k"])
                    if k < 0:
                        return self._json(400, {"error": "bad answer"})
                    line = f"act {k}"
                else:
                    return self._json(404, {"error": "not found"})
                out = lean.ask(line)
                self._send(200, out.encode("utf-8"), "application/json; charset=utf-8")
            except (ValueError, KeyError, TypeError) as e:
                self._json(400, {"error": f"bad request: {e}"})
            except RuntimeError as e:
                self._json(500, {"error": str(e)})

    return Handler


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--exe", default=str(ROOT / ".lake" / "build" / "bin" / "riftbound-live"))
    args = ap.parse_args()
    exe = Path(args.exe)
    if not exe.exists():
        print(f"{exe} が無い。先に `lake build riftbound-live`", file=sys.stderr)
        return 1
    lean = Lean(exe)
    server = ThreadingHTTPServer(("127.0.0.1", args.port), make_handler(lean, args.port))
    print(f"http://127.0.0.1:{args.port}/ を開く（止めるには Ctrl+C）")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        lean.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
