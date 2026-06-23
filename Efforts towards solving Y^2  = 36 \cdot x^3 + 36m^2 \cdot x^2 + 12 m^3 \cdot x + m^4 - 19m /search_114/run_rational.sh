#!/bin/bash
set -euo pipefail

# Charity Engine parameters:
#   FAMILY  : 0 = integer K (modulus M30)
#             1..24 = rational K with denominator M30_PRIME[FAMILY-1]
#   P_START : start of p range (signed integer)
#   P_END   : end of p range   (signed integer)
#   OUTPUT  : output file path (optional, default /output/results_*.csv)

FAMILY="${FAMILY:-0}"
P_START="${P_START:--10000000000}"
P_END="${P_END:-10000000000}"

mkdir -p /output
OUTPUT="${OUTPUT:-/output/results_f${FAMILY}_${P_START}_${P_END}.csv}"

echo "search114_rational: FAMILY=${FAMILY} p=[${P_START},${P_END}]"
FAMILY=$FAMILY P_START=$P_START P_END=$P_END OUTPUT=$OUTPUT \
    /app/search114_rational

echo "Done. Output: $OUTPUT"
