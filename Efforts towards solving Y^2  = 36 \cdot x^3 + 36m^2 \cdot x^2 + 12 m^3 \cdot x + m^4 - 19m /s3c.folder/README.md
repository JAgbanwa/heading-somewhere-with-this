# Summary of changes for run d24b1fff-69fb-4a46-ab1d-3d59d406873f
Formalized the paper *Congruences for the integrality of (36n³−19)/m* (J. Agbanwa) in Lean 4, in `RequestProject/Main.lean` (namespace `Congruences36n3`). The project builds cleanly with no `sorry` and uses only allowed axioms.
What was formalized and proved:
Section 1 — Forbidden primes (Proposition 1.1):
- `not_two_dvd`, `not_three_dvd`, `not_nine_dvd`: 2, 3, and 9 never divide 36n³−19 (it is ≡1 mod 2, ≡2 mod 3, ≡8 mod 9).
Section 1 — The prime 19 (Proposition 1.2):
- `nineteen_dvd_iff`: 19 ∣ 36n³−19 ⟺ 19 ∣ n.
- `not_threesixtyone_dvd`: 19²=361 never divides 36n³−19.
Section 2 — Cubic residue criterion (Theorem 2.1), working in `ZMod p`:
- `cube_bijective_of_two_mod_three`: for prime p ≡ 2 (mod 3) the cubing map is a bijection.
- `cube_root_formula`: the explicit inverse cube root c^((2p−1)/3).
- `exists_unique_of_two_mod_three`: for p ≥ 5, p ≡ 2 (mod 3), 36n³ = 19 has a unique solution.
- `solvable_iff_one_mod_three`: for p ≥ 5, p ≠ 19, p ≡ 1 (mod 3), 36n³ = 19 is solvable iff the cubic-residue condition (19·36⁻¹)^((p−1)/3) = 1 holds.
- `cube_roots_card_of_one_mod_three`: when that condition holds there are exactly three solutions.
  (Note: I added the hypothesis p ≠ 19 to the two p ≡ 1 (mod 3) statements; this matches the paper's Theorem 2.1 header "p ≥ 5, p ≠ 19" and is genuinely needed since the statement is false at p = 19.)
Section 3 — Complete characterisation (Theorem 3.1):
- `complete_characterisation`: m ∣ 36n³−19 ⟺ m is odd, 3 ∤ m, 361 ∤ m, and every prime power p^{v_p(m)} divides 36n³−19 (the CRT reduction together with the forbidden-prime constraints).
Section 5 — Explicit congruence pairs (1)–(11):
- `cong_5`, `cong_11`, `cong_14`, `cong_19`, `cong_20a/b/c`, `cong_25`, `cong_30`, `cong_40`, `cong_49`, each verifying M ∣ 36n³−19 by computation. The 49-prime (107-digit) values had been truncated in the source PDF text; I reconstructed the correct full values via CRT from the paper's prime sets and roots and verified they match the paper's printed prefixes.
Section 7 — Structural results:
- `moduli_unbounded` (Proposition 7.1): for any bound B there is a pair (M, n) with M > B and M ∣ 36n³−19 (via Dirichlet's theorem for primes ≡ 2 (mod 3)).
- `hard_obstruction` (Proposition 7.2): 2, 3, 361 never divide 36n³−19.
Every result is machine-checked.


Credits to Aristotle.
