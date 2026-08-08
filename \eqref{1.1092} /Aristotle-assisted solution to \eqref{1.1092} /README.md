# Summary of changes for run 352b8bd0-b483-496b-99b8-b8ff034a35c9
**Answer: for each of k = 390, 627, 633, 732, 921, 975 there are no integer solutions (x, r) with r ≠ 0.** All six cases are now proved in Lean.
Everything stays in the single file `RequestProject/QuadraticIntegerSolutions.lean`, which builds with no `sorry` and uses only the standard axioms.
New results:
- `not_satisfiesEq_390`, `not_satisfiesEq_627`, `not_satisfiesEq_633`, `not_satisfiesEq_732`, `not_satisfiesEq_921`, `not_satisfiesEq_975` — for each of these `k`, no integers `x, r` with `r ≠ 0` satisfy the equation.
- `satisfiesEq_390_solutionSet`, …, `satisfiesEq_975_solutionSet` — the corresponding set statements `{p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 k} = ∅`.
- `not_satisfiesEq_of_mem_list` — the combined statement for all six values at once.
- `disc_not_square_large` — the shared supporting lemma, and one small-range lemma per `k`.
The argument is uniform. By the previously established factorized form, a solution forces `r = 6s` with `s ≠ 0` and, writing `d = x + 6s`,
`6s·d² − (k − 216s³ + 108s²)·d + 216s³ + 6s² = 0`.
Multiplying by `24s` and completing the square, `y = 12s·d − (k − 216s³ + 108s²)` must satisfy
`y² = Δ(s, k) = 46656s⁶ − 46656s⁵ + 6480s⁴ − (432k + 144)s³ + 216k·s² + k²`.
With `P(s, k) = 216s³ − 108s² − 12s − k − 6` one has the exact identities
`Δ − P² = −144s³ − 1440s² − (24k + 144)s − 12k − 36` and
`Δ − (P − 1)² = 288s³ − 1656s² − (24k + 168)s − 14k − 49`.
Hence for any `k` with `390 ≤ k ≤ 975`: if `s ≥ 13` then `(P − 1)² < Δ < P²` with `P − 1 ≥ 0`, and if `s ≤ −7` then `P² < Δ < (P − 1)²` with `−P ≥ 0`. In both cases `Δ` is trapped strictly between the squares of two consecutive nonnegative integers, so it cannot be a square. This single lemma covers all six values of `k` simultaneously. The remaining eighteen values `s ∈ {−6,…,−1, 1,…,12}` are checked individually for each `k` (108 cases in total), again by exhibiting the integer `m` with `m² < Δ < (m + 1)²`.
The file header was updated to point to the new theorems; the earlier results (parametrization, the explicit lists for `r = ±6`, the `k = 114` case, infinitude) are unchanged. All work is committed and pushed.
# Summary of changes for run 64278920-6d2f-45d7-b81f-4a5fe6437160
**Answer: for k = 114 there are no integer solutions at all — the solution set is empty.**
Everything remains in the single file `RequestProject/QuadraticIntegerSolutions.lean`, which builds with no `sorry` and uses only the standard axioms.
New results added:
- `not_satisfiesEq_114` : for all integers `x, r` with `r ≠ 0`, `¬ SatisfiesEq x r 114`.
- `satisfiesEq_114_solutionSet` : `{p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 114} = ∅`.
- `no_int_sq_strictly_between` : the supporting fact that no integer square lies strictly between `m²` and `(m+1)²` for `m ≥ 0`.
The argument: by the previously established factorized form, a solution requires `r = 6s` with `s ≠ 0` and, writing `d = x + 6s`,
`(x + 6s)(114 − 6sx − 216s³ + 72s²) = 6s²(36s + 1)`, which after dividing by 6 is
`s·d² + (36s³ − 18s² − 19)·d + s²(36s + 1) = 0`.
Multiplying by `4s` and completing the square, `y = 2sd + 36s³ − 18s² − 19` would have to satisfy
`y² = Δ(s) = 1296s⁶ − 1296s⁵ + 180s⁴ − 1372s³ + 684s² + 361`.
For `s ≥ 3`, `Δ(s)` lies strictly between `(36s³ − 18s² − 2s − 21)²` and `(36s³ − 18s² − 2s − 20)²`, and for `s ≤ −8` strictly between the same two squares in the opposite order; in each case `Δ(s)` is trapped strictly between the squares of two consecutive nonnegative integers, so it is not a square. The nine remaining values `s ∈ {−7,…,−1, 1, 2}` (i.e. `r ∈ {−42,…,−6, 6, 12}`) are settled individually: `Δ(1) = −147 < 0`, and each of the other `Δ(s)` lies strictly between two consecutive squares (e.g. `Δ(2) = 36473`, with `190² = 36100 < 36473 < 36481 = 191²`).
The file header now also points to these two theorems. All work is committed and pushed.
# Summary of changes for run b0aad392-6518-45a4-be23-4b8f81c1232a
All results remain in the single file `RequestProject/QuadraticIntegerSolutions.lean`, which builds with no `sorry` and uses only the standard axioms.
**Comprehensive description of the integer solutions.** Writing `SatisfiesEq x r k` for the equation (read in ℚ, with `r ≠ 0`), the new theorem `satisfiesEq_iff_param` gives the complete list: `(x, r, k)` is a solution **iff** there are integers `s ≠ 0` and `d, e` with
  `d · e = 6s²(36s + 1)`,  `r = 6s`,  `x = d − 6s`,  `k = 6s(d − 6s) + 216s³ − 72s² + e`.
Equivalently (`satisfiesEq_iff_factorization`), the equation is the single factorization identity `(x + 6s)·(k − 6sx − 216s³ + 72s²) = 6s²(36s + 1)` with `r = 6s`. So `r` must be a nonzero multiple of 6, and for each such `r = 6s` the solutions correspond exactly to the divisors `d` (positive and negative) of `6s²(36s + 1)`; there are finitely many for each `r` (`satisfiesEq_finite`) and infinitely many overall.
**Explicit lists for the two smallest admissible values of `r`:**
- `r = 6` (`satisfiesEq_six_iff`, `satisfiesEq_six_ncard`: exactly 16 solutions), as pairs `(x, k)`:
 (−5, 336), (−4, 231), (−3, 200), (0, 181), (31, 336), (68, 555), (105, 776), (216, 1441), (−7, −120), (−8, −15), (−9, 16), (−12, 35), (−43, −120), (−80, −339), (−117, −560), (−228, −1225).
- `r = −6` (`satisfiesEq_neg_six_iff`, `satisfiesEq_neg_six_ncard`: exactly 32 solutions), as pairs `(x, k)`:
 (7, −540), (8, −441), (9, −412), (11, −396), (12, −395), (13, −396), (16, −405), (20, −423), (21, −428), (27, −460), (36, −511), (41, −540), (48, −581), (76, −747), (111, −956), (216, −1585), (5, −108), (4, −207), (3, −236), (1, −252), (0, −253), (−1, −252), (−4, −243), (−8, −225), (−9, −220), (−15, −188), (−24, −137), (−29, −108), (−36, −67), (−64, 99), (−99, 308), (−204, 937).
Both lists are proved as if-and-only-if characterizations (and also stated as set equalities, `satisfiesEq_six_solutionSet` / `satisfiesEq_neg_six_solutionSet`, with cardinalities 16 and 32). In addition, `satisfiesEq_six_k_ne_zero` and `satisfiesEq_neg_six_k_ne_zero` show every solution in these two lists automatically has `k ≠ 0`, so all of them meet the original nonzero-parameter requirement. The earlier results (denominator clearing, `6 ∣ r`, the divisibility criterion, the infinite family, infinitude) are unchanged. Everything is committed and pushed.
# Summary of changes for run 917e9291-10d5-49c4-b2ca-38c131dba1c1
**Answer: integer solutions do exist — infinitely many — and they can be described completely.**
All results are in one file, `RequestProject/QuadraticIntegerSolutions.lean`, which builds with no `sorry` and uses only the standard axioms.
Setup: `SatisfiesEq x r k` states the equation `x² − ((r² − r³ + k)/r)·x + (−6r² + 6(r³ − k) + r)/6 = 0` for integers `x, r, k`, evaluated in ℚ (so the divisions are exact), with `r ≠ 0` and `k ≠ 0` carried as hypotheses.
What is proved:
1. `satisfiesEq_iff` — clearing denominators, for `r ≠ 0` the equation is equivalent to the integer identity `6k(x + r) = 6rx² − 6r²x + 6r³x − 6r³ + 6r⁴ + r²`.
2. `six_dvd_of_satisfiesEq` — every term above except `r²` is divisible by 6, so `6 ∣ r²` and hence `6 ∣ r`: `r` must be a multiple of 6.
3. `satisfiesEq_iff_exists` — the full characterization: the equation holds iff `r = 6s` for some `s ≠ 0` and `k(x + 6s) = 6sx² − 36s²x + 216s³x − 216s³ + 1296s⁴ + 6s²`.
4. `dvd_of_satisfiesEq` — since the right-hand side above equals `(x + 6s)(6sx + 216s³ − 72s²) + 6s²(36s + 1)`, any solution satisfies the divisibility condition `(x + 6s) ∣ 6s²(36s + 1)`; this pins `x` down to finitely many values for each `s`.
5. `exists_k_of_dvd` — the converse: that divisibility (plus the right-hand side being nonzero, which is exactly the requirement `k ≠ 0`) yields a nonzero `k` solving the equation.
6. `satisfiesEq_example` — a concrete solution: `x = −5`, `r = 6`, `k = 336`.
7. `satisfiesEq_family` — for every `s ≠ 0`, `(x, r, k) = (1 − 6s, 6s, 432s³ − 102s² + 6s)` is a solution with `r ≠ 0` and `k ≠ 0`.
8. `satisfiesEq_infinite` — consequently the set of integer solutions `(x, r, k)` with `r ≠ 0`, `k ≠ 0` is infinite.
The work is committed and pushed.
