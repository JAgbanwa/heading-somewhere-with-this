# heading-somewhere-with-this

This repository is a working notebook, not a polished library: it is the accumulated Magma, SageMath/Python, PARI/GP, C, LaTeX, and Lean 4 debris of an ongoing computational-number-theory investigation. The throughline connecting almost everything here is a single shape of problem — take a Diophantine equation that has been algebraically massaged into a *Mordell-type* elliptic curve `y² = x³ + Ax² + Bx + C` (or a close cousin), then throw every available tool at it: minimal models, rank/Mordell–Weil computations, divisor-pair congruence sieves, brute-force point searches, and eventually machine-checked Lean proofs of the number-theoretic lemmas the search relies on. Several threads feed the author's long-running attempt at `x³ + y³ + z³ = 114` (the sum-of-three-cubes problem); others chase the more classical curve `y² = x³ − 1729` and a family of "6.0 / 5.909" congruence equations that recur throughout.

Below, every loose file at the repository root is described, followed by a description of each top-level folder and, per the request, every subfolder nested inside it.

---

## Root-level scratch files

These are ungrouped, individually-run scripts — mostly Magma (`.m`-style syntax, no extension) and SageMath/Python snippets — saved directly at the repo root as the investigation progressed. They're grouped here by theme for readability; every file is listed.

### The "equation 6.0 / 5.909" divisor-sweep family
A single Magma template — build the plane curve `36x³ − 19 − d²y − 2dy² − 12dxy = 0` for a window of integer parameters `d`, compute its genus, and run `PointSearch` up to a height bound — copy-pasted and re-windowed across the integers repeatedly to cover ever-larger ranges of `d` in the search for rational/integer points:
- `equation \eqref{5.909} for the first 100 values of d` — sweeps `d = 1..100`.
- `equation \eqref{5.909} 100 to 200 = d` — sweeps `d = 100..200`.
- `equation \eqref{5.909} b/n d = 200 and 300` — sweeps `d = 200..300`.
- `equation \eqref{6.0} not 5.909 between 200 and 300` — a second pass over `d = 200..300` under the "6.0" labeling.
- `eqref 6.0 from 300 to 400` — sweeps `d = 300..400`.
- `eqref 6.0 between 400 and 500` — sweeps `d = 400..500`.
- `eqref 6.0 between 700 and 1000` — sweeps `d = 700..1000`.
- `d = 1300 to 1400` — sweeps `d = 1300..1400`.
- `d = 1400 to 1500` — sweeps `d = 1400..1500`.
- `\eqref{6.0} between 1100 and 1183 = d` — sweeps `d = 1100..1183`.
- `\eqref 6.0 between 1183 and 1200` — sweeps `d = 1183..1200`.
- `\eqref{6.0} between 1200 to 1300` — sweeps `d = 1200..1300`.

Together these thirteen files form a manual, un-automated "checkpointed" search: each one is the same 15-line template with the range and search bound edited by hand, a low-tech precursor to the parallel sweepers built later in `Potential directions with specific equations/eq171_search/` and `s3c_sweep/`.

### Equation 7.11 / eqn 1.1 — minimal models over the function field `Q(m)`
Scripts that treat the family's parameter `m` as an indeterminate and work over the rational function field `K = Q(m)`, computing global minimal Weierstrass models symbolically (valid for every specialization of `m` at once):
- `A Magma code to solve eqn 7.11` — builds `E: y² = (36/m)x³ + 36x² + 12mx + (m² − 19/m)` over `Q(m)` and computes `MinimalModel(E)`.
- `Magma code yielding discriminant for equation 7.11` — rebuilds the same curve and extracts its minimal discriminant `Δ` and conductor divisor.
- `properly magma code on global minimal model` — makes the cubic monic by hand before constructing the curve, then takes the minimal model (a cleaned-up rerun of the eqn 7.11 computation).
- `Another correct Magma code determining the global minimal model of eqn 1.1` — the analogous computation for "eqn 1.1", first attempted with a partial Weierstrass tuple, then corrected to the full `[0, 36, 12m, (m³−19)/m, 36/m]` model.
- `A Magma code calculating the global minimal model` (inside the `Efforts towards solving…` folder, described below) is the sibling of this pair for the `m⁴ − 19m` variant of the equation.
- `Magma code for the already solved case of 51` — specializes the family to the already-resolved parameter value 51, builds the corresponding monic cubic over `Q(m)`, and takes its minimal model as a sanity check against known results.

### Rank and Mordell–Weil computations across the `m`-family
- `Magma code for E with either rank 0 or geq 1` — loops `m = 1..220` (in stages, with the raw Magma transcript pasted in as a comment block) over `E: y² = x³ + mx² + (m²/3)x + (m³−19)/36`, flags every `m` for which `Rank(Emin) ≥ 1`, and later patches in `SetClassGroupBounds("GRH")` to silence Magma's expensive unconditional class-group warning.
- `determining the rank of E` — takes one specific member of the family, `E = [0, 36, 0, 204, 4894/17]` (the `α = 17` specialization), and runs the full battery: minimal model, rank bound, exact rank, generators, regulator, torsion.
- `sagemath code generating values for m for which E has rank 0 or 1` — the SageMath counterpart: builds `E` from `y² = (36/m)n³ + 36n² + 12mn + m² − 19/m` symbolically, completes the cube to reach short Weierstrass form, and prepares it for a rank/torsion scan over `m`.
- `Magma code determining global minimal model of E` — feeds in one giant, already-expanded quartic of Weierstrass coefficients (70-digit integers `A, B, C, D`) and reduces it to a global minimal model.
- `finding rank and generator of an interesting elliptic curve` — the SageMath version of the same giant-coefficient curve: shifts `x` to kill the quadratic term, builds the short Weierstrass curve, and calls `E.rank()` / `E.gens()`.
- `trying to compute the rank of wild one` — a near-duplicate of the previous file with extra defensive code (GCD-scaling the coefficients, `try/except` fallbacks to `rank_bound()`) for the same "wild" giant curve.
- `generated infinitely many more points to the interesting elliptic curve eqn of this repo.` — takes two explicit rational generators `P1, P2` found on that giant curve and prints every small integer combination `n1·P1 + n2·P2`, demonstrating (via the group law) that infinitely many rational points follow from just the two generators.
- `generating 2P,3P,4P,...,9P with SageMath` — implements the elliptic-curve chord-and-tangent group law *by hand* (point addition and doubling formulas, double-and-add scalar multiplication, plus a redundant projective-coordinates cross-check) to compute `2P` through `9P` for a specific rational point, watching how fast the numerator/denominator digit counts explode.
- `multiples of EllipticCurve([0,0,0,0,-1729])` — the simplest version of the same idea on the classical curve `y² = x³ − 1729`: takes the point `(2305, 110664)` and prints `P, 2P, 3P, 4P`.
- `n \equiv 1(mod17)` — repeats the "print low multiples of a point" exercise for three different curves/points arising from the `n ≡ 1 (mod 17)` residue class (the cases `n = 1`, `n = 18`, `n = 35`).

### The `x³ − y² = 1729` / Hardy–Ramanujan thread
- `x^3 - y^2 = 1729 rational points sage code` — two-pronged solver for `x³ − y² = 1729`: a direct brute-force scan over `|x| ≤ 10⁵`, followed by converting to the elliptic curve `y² = x³ − 1729` and asking Sage for `integral_points()` directly.
- `SageMath code for x^3 - y^2 = 1729z^3 from z = 131 to 200`, `SageMath code for x^3 - y^2 = 1729z^3 between z = 200 and 300.`, `SageMath for x^3 - y^2 = 1729z^3 between z = 300 to 400`, `SageMath x^3 - y^2 = 1728z^3 between z = 400 to z = 500.` — four large, self-contained sweep scripts (despite the last filename saying "1728", it also solves the `1729` equation) that, for each window of `z`, separate out perfect-square `z` values, then run an increasingly tuned "efficient/optimized solution finder" heuristic to hunt for integer `(x, y)` solving `x³ − y² = 1729z³` for non-square `z`.
- `solving x^3 - y^2 = 1729z^3` (Magma) — the tidy, closed-form version: loops `z = 1..50`, builds the Mordell curve `y² = x³ − 1729z³` for each, and calls `IntegralPoints`.
- `correct code for rationals` (Magma) — a coprime-pair brute-force search: for `a/b` in lowest terms up to a height bound, tests whether `(( (a/b)³ + 1729) / (3·a/b))` is a rational square, collecting `(x, y)` solutions to the reduced 1729 curve.
- `finding rational points to a reduced elliptic curve problem, 1729.` (Magma) — works with the homogeneous plane cubic `3X²Y − Y³ − 1729Z³ = 0`, takes its Jacobian to get a genuine elliptic curve, and computes rank/generators/bounded rational points on it.
- `magma code for y^2 = D*x^3 - B` — investigates the reparametrization `y² = D·x³ − B` of `Y² = X³ − 1729D³` for an explicit large `D`, verifies the algebraic substitution `B = 1729D`, builds `y² = x³ − 1729D³` as an elliptic curve, and searches for points that descend to integer solutions on the reparametrized curve.
- `An old Sage code I'm keeping here` — an earlier, more manual SageMath attempt at "directly search for rational points" on the same giant-coefficient curve seen in the rank-computation files above, converting it to Weierstrass form by completing the cube before searching.

### The sum-of-three-cubes `α`-parameter family (`x³+y³+z³ = α`-adjacent curves)
- `Magma verification when \alpha = 17` — builds the plane cubic for `α = 17`, passes it through `EllipticCurve`, `MinimalModel`, and `MordellWeilShaInformation`, then maps any point found back down to the original cubic (the pasted-in transcript records a 2-descent/4-descent bounding `0 ≤ Rank(E) ≤ 1`, with no rational point recovered at the searched height).
- `rational points for sums of three cubes problem when \alpha = 19` — the identical pipeline specialized to `α = 19`.
- `*keeping this here for now` — clears denominators in the `α = 19` plane cubic by hand, rebuilds it as `19y² = 36x³ + 684x² + 4332x + 6840`, converts to an elliptic curve, lifts a previously found rational point `(xP, yP)` onto it, verifies membership, takes the minimal model, and prints its first ten multiples both on the minimal model and mapped back to the original curve.
- `rational points for n \equiv 4(mod5)` — the same `EllipticCurve`/`MinimalModel`/`MordellWeilShaInformation` pipeline applied to the `n = 9` representative of the `n ≡ 4 (mod 5)` residue class.
- `solving an elliptic curve problem for arbitrary cases` — runs the pipeline three more times back-to-back for the representatives `n = 1`, `n = 18`, and `n = 35`.
- `As a test case for 51, I ran this, and still running` — the same pipeline for the "case 51" plane cubic, annotated as still running at the time it was saved (no output was captured).
- `Magma code verifying the rational solutions` and `Magma verification` — two standalone checks that plug an explicit huge rational triple `(a, b, c)` into `a³ + b³ + c³` and print the resulting `value`/`expr`, verifying (or refuting) a candidate solution by direct substitution.
- `Magma code t find rational points to a giant curve!` — takes the enormous single-coefficient curve `y² = x³ − 2525830172961041971790515187823418026564152076350226869064138887440125x` and computes its rank, generators, torsion subgroup, and rational points up to a `10⁶` height bound.
- `finding coefficients to an elliptic curve expression of the sums of three cubes` — symbolically expands `(19 + 6u)² + (36u³ − 19)/19` for `u = Ax + B` (explicit large `A, B`) in Sage and extracts the resulting cubic's coefficients `a, b, c, d`, i.e. mechanizes the "put the sum-of-three-cubes identity into `y² = ax³+bx²+cx+d` form" step.
- `finding rational points to this curve` (Magma) — torsion, rank bounds, generators, and a bounded rational-point search on the specific curve `[0, 36/19, 36, 228, 360]` (the cleaned-up `α = 19` Weierstrass model).
- `code which yielded promising n \equiv a mod p` — a CRT-based search: combines ~20 hand-collected prime/residue constraints on `n` via the Chinese Remainder Theorem, generates every consistent combined residue class, and scans each class for candidate `n` satisfying further modular filters — the file that produced several of the "promising" congruence classes referenced elsewhere in the repo.

### Miscellaneous
- `a piece of paper MO` — the largest scratch file in the repo (772 lines): a running LaTeX-fragment "scratch pad" of algebraic manipulations, tracing the chain of substitutions from `Y² = k₁³ − 1729·D³` down through the difference-of-squares identity `X² − Y² = a`, divisor parametrizations of equation `(6.0)`, several numbered tables of small solutions `(c, x′, y′)`, and closing with a short list of open questions about equations `(6.221)` and `(6.743)`. This is effectively the informal derivation log that several of the "clean" Magma/Sage scripts above were distilled from.
- `31 \\` — a stray one-line placeholder/test file (contents: `jgvkg`), evidently left over from testing file creation rather than carrying mathematical content.

---

## Folders

### `Efforts towards solving Y^2 = 36·x^3 + 36m^2·x^2 + 12m^3·x + m^4 - 19m /`
The main workspace for one specific member of the curve family (the `m⁴ − 19m` variant), spanning symbolic reduction, a full LaTeX/Lean-verified congruence paper, and a from-scratch C/Docker search pipeline. Directly inside this folder:
- `A Magma code calculating the global minimal model` — builds `E` via a-invariants `[0, m², 0, m³/3, (m⁴−19m)/36]` over `Q(m)` and reduces to a global minimal model.
- `Magma code for expanding 36A^3 - 19` — substitutes the explicit linear form `A = (huge constant)·k + (huge constant)` and fully expands `36A³ − 19` into a quartic in `k`, printing each coefficient separately (this is the polynomial that the congruence paper below analyzes).

Its subfolders:
- **`Mordell-type equation of this problem/`** — contains a single `.tex document` titled *"The Mordell-Type Weierstrass Curve Associated to the Given Equation."* It takes the compressed equation `y² = (12x+7+L₁k+L₀)² + P(k)/(12x+7)` with explicit ~60-digit constants, shows both linear coefficients are divisible by 6, and derives the associated Mordell-type Weierstrass curve.
- **`integer_congruences_complete_note/`** — a paired LaTeX note and Lean 4 formalization proving the *exact* necessary-and-sufficient integer conditions (not just congruence filters) for `y² = (x+6n)² + N/x`, `N = 36n³−19`. Contains a `.tex doc` (the write-up, with theorems on the divisor-square criterion, difference-of-squares factorization, the necessary congruence filter, and a complete filtered criterion) and a `LEAN file` machine-checking those same theorems (`CFE.divisor_square_criterion`, `CFE.difference_of_squares`, `CFE.necessary_congruences`, `CFE.complete_filtered_criterion`) against Mathlib.
- **`s3c.folder/`** — the companion congruence paper for the general `(36n³−19)/m` divisibility problem, together with its Lean formalization and a compiled PDF. Contains:
  - `README.md` — a changelog explaining that the paper *"Congruences for the integrality of (36n³−19)/m"* was fully formalized in Lean 4 with no `sorry`s, listing which theorems were proved (forbidden primes 2/3/9, the special role of 19, a cubic-residue solvability criterion via `ZMod p`, the complete CRT characterization, and eleven explicit large-modulus congruence pairs reconstructed by CRT after the source PDF text was found to be truncated).
  - `.tex file` — the paper itself: characterizes every pair `(m, n)` with `m ∣ 36n³ − 19` via prime-by-prime cubic-residue solvability, up to an explicit 107-digit-modulus congruence pair.
  - `Lean formalisation of .tex doc` — the corresponding Lean 4 proof file (`namespace Congruences36n3`) mechanizing the forbidden-prime propositions, the cubic-residue criterion, and the CRT-based complete characterization.
  - `congruences.pdf` — the typeset, compiled version of the `.tex file` above.
- **`search_114/`** — the computational search engine aimed squarely at `x³+y³+z³ = 114`, packaged to run on Charity Engine's distributed grid. Contains:
  - `search114_rational.c` — a GMP-based C search implementing a "Booker-style" parametrized search over rational `K = (n−n₀)/M₃₀`, covering 31 sub-families (one per divisor structure of the 30-prime CRT modulus `M₃₀`) so that a dense mesh of astronomically large `n` (up to roughly `10^54`) is reachable; for each candidate it checks whether `y² = (α+6n)² + (36n³−19)/α` is a perfect square, restricting `α ≡ 7 (mod 12)` so that `X = (α−7)/12` is automatically an integer.
  - `run_rational.sh` — the Charity Engine entry-point script that reads the `FAMILY`, `P_START`, `P_END` environment variables, builds the output path, and invokes the compiled `search114_rational` binary.
  - `Dockerfile` — an Ubuntu 24.04 image that installs GMP, compiles `search114_rational.c` with `-O3`, and sets `run_rational.sh` as its entrypoint, i.e. the exact container shipped out to grid workers.

### `Observing key fractions/`
A single-file folder containing `.tex doc`, a computational search report titled *"Large-`n` Integer Solutions to `21n³+19=(12x+7)k`."* It searches the region `n ≥ 10²⁰` for a small window of `x` (`0 ≤ x ≤ 500`), gives a complete congruence classification of solutions in that regime, and tabulates the 330 explicit triples found in the finite window `10²⁰ ≤ n < 10²⁰+1000`.

### `Potential directions with specific equations/`
The most actively developed research thread: the equation `y² = (36n³−19−12mn)² − (2m)³`, its published results, and two independent, parallelized search implementations (Python and C). Directly inside this folder:
- `README.md` — a running lab notebook of two "wave" sweeps of the C searcher across all 8 cores of the author's M1 Pro, pasting in live terminal output (`sweep_*.txt` file sizes and hit contents) as new integer triples were discovered in real time.
- `Mordell weil addendum` — a short LaTeX addendum tabulating exact Mordell–Weil ranks (computed via PARI/GP's `ellrank`) for the elliptic fibration `Eₙ: Y² = X³+36n²X²+12ncX+c²` underlying the equation, proving the tautological point `T=(0,c)` is an order-3 torsion section on every fiber, and flagging fibers whose second generator is still unfound.
- `eqref{1.71}` — the main LaTeX paper, *"Integer Solutions of `y²=(36n³−19−12mn)²−(2m)³`: Complete Results to `|m|≤10¹¹`, the Torsion-Translate Correspondence, and the Mordell–Weil Structure of the Fibration"* (with computational assistance credited to Claude), reporting 62 total solution triples (up from 29 known previously) after an exhaustive divisor-pair search, an `m ≤ 24n²` bound for positive `m`, and exact ranks for 22 fibers including one of rank 3.

Its subfolders:
- **`eq171_search/`** — the Python/multiprocessing implementation of the ongoing search extending the `eqref{1.71}` paper beyond its published range. Contains:
  - `known_solutions.py` — the canonical list of the 50 known `(n, m, |y|)` triples as of June 2026, used by every other script here to filter out already-known hits.
  - `divisor_sweep.py` — the core divisor-pair search routine (factorization + solution verification) for a given `m`.
  - `fiber_search.py` — searches for further integral points on a single fixed-`n` fiber curve by taking multiples/combinations of already-known points on it.
  - `run_parallel_sweep.py` — a `multiprocessing`-based driver that splits an `m`-range across worker processes and merges their hits.
  - `run_sweep.sh` — a thin shell wrapper that runs `run_parallel_sweep.py` over a default (resumable) `m`-window and then pipes the results into `verify_solutions.py`.
  - `verify_solutions.py` — re-verifies every claimed triple (from `known_solutions.py` or a supplied JSON file) by direct substitution back into the defining equation.
  - `SEARCH_RESULTS.md` — the search log itself: records three newly-merged triples (extending certification to `|m| ≤ 2.067×10⁹`), a table of completed zero-hit scans (torsion-translate closure, small-cofactor strata, rank-2 fiber exploration, new-fiber discovery), the in-progress sweep window, and next-step suggestions for finding a 51st triple.
- **`s3c_sweep/`** — the earlier, C-based implementation of the same exhaustive divisor-pair search, optimized for raw throughput. Contains:
  - `divisor_sweep.c` — a segmented-sieve, `__int128`-arithmetic C program that exhaustively factors `2m³` into divisor pairs `(t,s)` for every `m` in a range, filters candidates by a mod-12 congruence, and checks the resulting cubic root condition — this is the program whose 8-core M1 Pro runs are logged live in the folder's parent `README.md`.
  - `run_sweep.sh` — splits a requested `[LO, HI]` range of `|m|` evenly across a chosen number of CPU cores, launches one `divisor_sweep` process per core, waits for all of them, and merges their output files into a single sorted `all_hits.txt`.
  - `verify_solutions.py` — hard-codes the table of (at the time) 50 known `(n, m, |y|)` triples and exactly re-verifies each one, plus any new hits piped in via stdin, against the equation.

### `new CE files /files-3 /`
A second, independently-built Charity Engine toolkit — this time for the equation `y² = (6n+x)² + (36n³−19)/x` directly (rather than the `m`-parametrized recasting) — combining a SageMath integral-points solver, a PARI/GP rank scanner, and a bare-metal C congruence sieve so the same search can be cross-checked across three different computer-algebra backends. Contains:
- `README.md` — currently empty (a placeholder for run logs, mirroring the pattern of the root `README.md` before this rewrite).
- `ec_search.sage` — for each small "fiber" parameter `x` (and, symmetrically, `u = y−x−6n`), builds the associated elliptic curve, asks Sage's `integral_points()` for *every* integral point (relying on Siegel's theorem to guarantee finiteness), and back-substitutes to recover integer `(x, n, y)` solutions of any size — including solutions with `n` in the astronomical `10²⁰`–`10⁴⁰` windows.
- `rank_scan.gp` — the PARI/GP analogue: for a range of `x`- or `u`-fiber indices it calls `ellrank` (with a timeout guard) to get exact or bounded ranks and generators, then enumerates small integer combinations of the generators (plus torsion) looking for one that decodes to an integer solution — explicitly noting that rank-0 fibers with trivial torsion can be eliminated outright.
- `sieve.c` — a GMP-based congruence sieve exploiting the factorization identity `x·u·v = N` (`N = 36n³−19`) to guarantee, for each finished chunk of the `n`-range, that *every* solution with a small `x` or a small `u = y−x−6n` will be found, via cube-root-mod-prime residue classes, Hensel lifting, and CRT — built to run either standalone (`--selftest`, explicit `--n0/--len/--xmax/--umax` windows) or sharded across many machines (`--shard I --nshards T`) for a Charity Engine-style grid deployment.
