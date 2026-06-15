# Eq 1.71 extended solution search (June 2026)

Search for integer triples `(n, m, |y|)` solving

`y² = (36n³ − 19 − 12mn)² − (2m)³`,  `m ≠ 0`

beyond the 47 known rows in `eqref{1.71}`.

## Completed searches (no new triples)

| Search | Range / method | New hits |
|--------|----------------|----------|
| Torsion-translate closure | all 47 known rows | 0 |
| Small-cofactor stratum | `d ≤ 64`, `|m| ≤ 10¹⁰` | 0 |
| Small-cofactor stratum | `d ≤ 65 536`, `|m| ≤ 5×10¹²` | 0 |
| Small-cofactor stratum | `d ≤ 262 144`, `|m| ≤ 10¹³` | 0 |
| Rank-2 fiber exploration | EC multiples / `aP+bQ`, `|k| ≤ 20 000` | 0 |
| Fiber direct scan | 15 fibers, `|X| ≤ 5×10⁸` (`|m| ≤ 2.5×10⁸`) | 0 |
| New-fiber discovery | `n ∈ [27 950, 60 000] ∪ [−60 000, −29 318]`, `|X| ≤ 300 000` (62 734 fibers) | 0 |

All completed scans agree with the paper’s stratified completeness claims in the tested regimes.

## In progress

Parallel divisor-pair sweep:

```bash
python3 run_parallel_sweep.py \
  --m-start 1387000001 --m-end 1420000000 \
  --workers 4 --out-dir /tmp/eq171_sweep_1387_1420
```

This extends Theorem completeness from `|m| ≤ 1.387×10⁹` toward `1.42×10⁹`. At ~250–300 `m`/s per worker, the full window needs roughly 8–9 core-hours. No hits reported through `m ≈ 1.389×10⁹` (partial run).

## How to continue

```bash
cd "Potential directions with specific equations/eq171_search"

# Next m-window beyond prior certification
python3 run_parallel_sweep.py --m-start 1420000001 --m-end 1500000000 --workers 4

# Larger small-cofactor stratum
python3 divisor_sweep.py --mode small-cofactor --m-abs-max 10000000000000 --d-max 1048576

# New fibers with modest integral points
python3 fiber_search.py --n-values "70000,80000,90000" --x-abs-max 1000000

# Verify any JSON output
python3 verify_solutions.py --file /tmp/merged_hits.json
```

## Interpretation

No 48th row was found in any completed search. The most plausible remaining sources (per the paper’s remark) are:

1. **Large `|m|` via divisor sweep** beyond `1.387×10⁹` (especially negative `m` on rank ≥ 1 fibers).
2. **Second generators** on rank-2 fibers (`n = 93, −4741, −6561, 16531, 17309, 27949, …`) at heights beyond `|X| ≈ 5×10⁸`; these likely need PARI/Magma integral-point machinery rather than naive scanning.
3. **Torsion translates** of any future in-window hit on one of the six pairing fibers (`n = 1, −54, 798, 909, 14709, −29317`).
