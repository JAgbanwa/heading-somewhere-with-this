#!/bin/bash
# Parallel exhaustive sweep for y^2 = (36n^3-19-12mn)^2 - (2m)^3
# Finds ALL integer solutions with |m| in [LO, HI], n unbounded.
#
# Usage:   ./run_sweep.sh LO HI NCORES
# Example: ./run_sweep.sh 2814000000 10000000000 8
#
# Compile first:
#   gcc -O3 -march=native -funroll-loops -o divisor_sweep divisor_sweep.c -lm
# On Mac if -march=native causes issues:
#   gcc -O3 -funroll-loops -o divisor_sweep divisor_sweep.c -lm

set -e
LO=${1:?Usage: $0 LO HI NCORES}
HI=${2:?Usage: $0 LO HI NCORES}
NC=${3:?Usage: $0 LO HI NCORES}

if [ ! -x ./divisor_sweep ]; then
    echo "ERROR: ./divisor_sweep not found. Compile with:"
    echo "  gcc -O3 -march=native -funroll-loops -o divisor_sweep divisor_sweep.c -lm"
    exit 1
fi

RANGE=$(( HI - LO ))
W=$(( (RANGE + NC - 1) / NC ))

echo "Sweeping |m| in [$LO, $HI] on $NC cores (chunk size ~$W)"
echo "Started: $(date)"

PIDS=()
OUTFILES=()
for ((i=0; i<NC; i++)); do
    A=$(( LO + i*W ))
    B=$(( LO + (i+1)*W - 1 ))
    [ $B -gt $HI ] && B=$HI
    [ $A -gt $HI ] && break
    OUT="sweep_${A}_${B}.txt"
    OUTFILES+=("$OUT")
    echo "  Core $i: |m| in [$A, $B] -> $OUT"
    ./divisor_sweep "$A" "$B" "$OUT" > "sweep_${A}_${B}.log" 2>&1 &
    PIDS+=($!)
done

echo "All $NC chunks running... (check sweep_*.log for progress)"
echo ""

FAILED=0
for i in "${!PIDS[@]}"; do
    wait "${PIDS[$i]}" || { echo "WARNING: chunk $i failed"; FAILED=1; }
    echo "  Chunk $i done"
done

sort -u "${OUTFILES[@]}" 2>/dev/null > all_hits.txt

echo ""
echo "Finished: $(date)"
echo "Total hits in all_hits.txt: $(wc -l < all_hits.txt)"
echo ""
echo "Run: python3 verify_solutions.py < all_hits.txt"

[ $FAILED -eq 0 ] && echo "All chunks completed successfully." \
                   || echo "WARNING: some chunks failed - check sweep_*.log"
