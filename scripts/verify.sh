#!/usr/bin/env bash
# 全体の検証。main へマージする前に通す（docs/lean-guidelines.md §7.2）。
# 1 つでも失敗したら、そこで止まる。
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n==> %s\n' "$*"; }

step "1/5 build (--wfail)"
lake build Riftbound RiftboundCards RiftboundDriver RiftboundTest riftbound-trace riftbound-replay riftbound-live --wfail

step "2/5 test"
lake test
uv run --no-project python -B -m unittest discover -s scripts -p test_audit_atlas_replay.py
uv run --no-project python -B scripts/replay_smoke.py

step "3/5 axiom audit (lake check)"
# サンドボックスは Linux でしか動かない。自分のコードを自分のマシンで検査するので外す。
# 対象は defaultTargets（検証コア Riftbound だけ）。
lake check --inadvisably-no-sandbox

step "4/5 card data staleness"
uv run --no-project python scripts/normalize.py --check
uv run --no-project python scripts/gen_lean.py --check
uv run --no-project python scripts/coverage.py --check

step "5/5 rule citations"
uv run --no-project python scripts/cr_citations.py

printf '\nverify: OK\n'
