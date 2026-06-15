#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

M_START="${1:-1387000001}"
M_END="${2:-1420000000}"
WORKERS="${3:-4}"
OUT_DIR="${4:-/tmp/eq171_sweep_${M_START}_${M_END}}"

python3 run_parallel_sweep.py \
  --m-start "$M_START" \
  --m-end "$M_END" \
  --workers "$WORKERS" \
  --out-dir "$OUT_DIR"

python3 verify_solutions.py --file "$OUT_DIR/merged_hits.json"
