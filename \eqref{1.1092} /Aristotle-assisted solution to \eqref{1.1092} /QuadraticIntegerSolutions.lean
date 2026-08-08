/-
# The equation `x² - ((r² - r³ + k)/r)·x + (-6r² + 6(r³ - k) + r)/6 = 0`
We look for integer solutions `(x, r, k)` of
  `x² - ((r² - r³ + k)/r)·x + (−6r² + 6(r³ − k) + r)/6 = 0`,
where the equation is read in `ℚ`, `r ≠ 0` (so that the division by `r` makes sense)
and `k ≠ 0`.
**Answer.** Integer solutions do exist (in fact infinitely many), and they are completely
described as follows.  Clearing denominators, the equation is equivalent to
  `6k(x + r) = 6r x² − 6r² x + 6r³ x − 6r³ + 6r⁴ + r²`.        (†)
Since every term of (†) except `r²` is divisible by `6`, we get `6 ∣ r²`, hence `6 ∣ r`.
Writing `r = 6s` (`s ≠ 0`), (†) becomes
  `k(x + 6s) = 6s x² − 36s² x + 216s³ x − 216s³ + 1296s⁴ + 6s²`.   (‡)
The right-hand side of (‡) equals `(x + 6s)(6s x + 216s³ − 72s²) + 6s²(36s + 1)`, so a
solution forces `(x + 6s) ∣ 6s²(36s + 1)`; conversely that divisibility (together with the
right-hand side of (‡) being nonzero, which is exactly what `k ≠ 0` means) produces a
solution.  For instance `s = 1`, i.e. `r = 6`, `x = -5`, `k = 336` is a solution, and
`(x, r, k) = (1 − 6s, 6s, 432s³ − 102s² + 6s)` is a solution for every `s ≠ 0`.
**Comprehensive list.**  Equivalently (see `satisfiesEq_iff_param`), the integer solutions are
exactly the triples
  `r = 6s`,  `x = d − 6s`,  `k = 6s(d − 6s) + 216s³ − 72s² + e`,
where `s ≠ 0` and `d·e = 6s²(36s + 1)` is an arbitrary factorization.  So for each admissible
`r = 6s` the solutions correspond to the (positive and negative) divisors `d` of
`6s²(36s + 1)`, and there are only finitely many of them (`satisfiesEq_finite`).  The two
smallest cases are spelled out completely in `satisfiesEq_six_iff` (`r = 6`: 16 solutions) and
`satisfiesEq_neg_six_iff` (`r = -6`: 32 solutions).
**The case `k = 114`.**  For this particular value of `k` there is *no* integer solution at all:
see `not_satisfiesEq_114` and `satisfiesEq_114_solutionSet`.
**The cases `k = 390, 627, 633, 732, 921, 975`.**  For each of these six values there is likewise
*no* integer solution `(x, r)` with `r ≠ 0`: see `not_satisfiesEq_390`, `not_satisfiesEq_627`,
`not_satisfiesEq_633`, `not_satisfiesEq_732`, `not_satisfiesEq_921`, `not_satisfiesEq_975`,
their solution-set forms `satisfiesEq_390_solutionSet`, …, `satisfiesEq_975_solutionSet`, and the
combined statement `not_satisfiesEq_of_mem_list`.
-/
import Mathlib
namespace QuadraticIntegerSolutions
/-- The equation under consideration, for integers `x`, `r`, `k`, read inside `ℚ`. -/
def SatisfiesEq (x r k : ℤ) : Prop :=
  (x : ℚ) ^ 2 - (((r : ℚ) ^ 2 - (r : ℚ) ^ 3 + (k : ℚ)) / (r : ℚ)) * (x : ℚ)
    + (-6 * (r : ℚ) ^ 2 + 6 * ((r : ℚ) ^ 3 - (k : ℚ)) + (r : ℚ)) / 6 = 0
/-- Clearing denominators: for `r ≠ 0` the equation is equivalent to a polynomial identity
over `ℤ`. -/
theorem satisfiesEq_iff (x r k : ℤ) (hr : r ≠ 0) :
    SatisfiesEq x r k ↔
      6 * k * (x + r) = 6 * r * x ^ 2 - 6 * r ^ 2 * x + 6 * r ^ 3 * x - 6 * r ^ 3
        + 6 * r ^ 4 + r ^ 2 := by
  have hr' : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  rw [SatisfiesEq, show (6 * k * (x + r) = 6 * r * x ^ 2 - 6 * r ^ 2 * x + 6 * r ^ 3 * x
        - 6 * r ^ 3 + 6 * r ^ 4 + r ^ 2)
      ↔ ((6 * k * (x + r) : ℤ) : ℚ)
        = ((6 * r * x ^ 2 - 6 * r ^ 2 * x + 6 * r ^ 3 * x - 6 * r ^ 3 + 6 * r ^ 4 + r ^ 2 : ℤ) : ℚ)
      from (Int.cast_injective.eq_iff).symm]
  push_cast
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith
/-- Any solution forces `r` to be a multiple of `6`. -/
theorem six_dvd_of_satisfiesEq {x r k : ℤ} (hr : r ≠ 0) (h : SatisfiesEq x r k) : (6 : ℤ) ∣ r := by
  rw [satisfiesEq_iff x r k hr] at h
  have h6 : (6 : ℤ) ∣ r ^ 2 := ⟨k * (x + r) - r * x ^ 2 + r ^ 2 * x - r ^ 3 * x + r ^ 3 - r ^ 4, by
    linarith⟩
  have h2 : (2 : ℤ) ∣ r := by
    have : (2 : ℤ) ∣ r ^ 2 := dvd_trans ⟨3, by norm_num⟩ h6
    exact (Int.Prime.dvd_pow' (by norm_num) this)
  have h3 : (3 : ℤ) ∣ r := by
    have : (3 : ℤ) ∣ r ^ 2 := dvd_trans ⟨2, by norm_num⟩ h6
    exact (Int.Prime.dvd_pow' (by norm_num) this)
  have hcop : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by ring⟩
  simpa using hcop.mul_dvd h2 h3
/-- The characterization of the solutions, after writing `r = 6s`. -/
theorem satisfiesEq_iff_exists (x r k : ℤ) (hr : r ≠ 0) :
    SatisfiesEq x r k ↔
      ∃ s : ℤ, s ≠ 0 ∧ r = 6 * s ∧
        k * (x + 6 * s) =
          6 * s * x ^ 2 - 36 * s ^ 2 * x + 216 * s ^ 3 * x - 216 * s ^ 3 + 1296 * s ^ 4
            + 6 * s ^ 2 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := six_dvd_of_satisfiesEq hr h
    refine ⟨s, ?_, hs, ?_⟩
    · rintro rfl; exact hr (by simpa using hs)
    · rw [satisfiesEq_iff x r k hr, hs] at h
      linarith
  · rintro ⟨s, -, rfl, h⟩
    rw [satisfiesEq_iff x _ k hr]
    linarith
/-- Necessary condition on `x`: `x + 6s` divides `6s²(36s + 1)`. -/
theorem dvd_of_satisfiesEq {x s k : ℤ} (hs : s ≠ 0) (h : SatisfiesEq x (6 * s) k) :
    (x + 6 * s) ∣ 6 * s ^ 2 * (36 * s + 1) := by
  have hr : (6 : ℤ) * s ≠ 0 := by simpa using hs
  rw [satisfiesEq_iff x _ k hr] at h
  exact ⟨k - 6 * s * x - 216 * s ^ 3 + 72 * s ^ 2, by linarith⟩
/-- Conversely, whenever `x + 6s` divides `6s²(36s + 1)` and the right-hand side of (‡) is
nonzero, there is a (necessarily nonzero) `k` making the equation hold. -/
theorem exists_k_of_dvd {x s : ℤ} (hs : s ≠ 0)
    (hdvd : (x + 6 * s) ∣ 6 * s ^ 2 * (36 * s + 1))
    (hne : 6 * s * x ^ 2 - 36 * s ^ 2 * x + 216 * s ^ 3 * x - 216 * s ^ 3 + 1296 * s ^ 4
      + 6 * s ^ 2 ≠ 0) :
    ∃ k : ℤ, k ≠ 0 ∧ SatisfiesEq x (6 * s) k := by
  have hr : (6 : ℤ) * s ≠ 0 := by simpa using hs
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c + 6 * s * x + 216 * s ^ 3 - 72 * s ^ 2, ?_, ?_⟩
  · rintro h0
    exact hne (by linear_combination (x + 6 * s) * h0 + hc)
  · rw [satisfiesEq_iff x _ _ hr]
    linear_combination (-6 : ℤ) * hc
/-- A concrete solution: `x = -5`, `r = 6`, `k = 336`. -/
theorem satisfiesEq_example : SatisfiesEq (-5) 6 336 := by
  rw [satisfiesEq_iff _ _ _ (by norm_num)]
  norm_num
/-- An infinite family of solutions: for every `s ≠ 0`,
`(x, r, k) = (1 - 6s, 6s, 432s³ - 102s² + 6s)` is a solution with `r ≠ 0` and `k ≠ 0`. -/
theorem satisfiesEq_family (s : ℤ) (hs : s ≠ 0) :
    (6 * s ≠ 0) ∧ (432 * s ^ 3 - 102 * s ^ 2 + 6 * s ≠ 0) ∧
      SatisfiesEq (1 - 6 * s) (6 * s) (432 * s ^ 3 - 102 * s ^ 2 + 6 * s) := by
  have hr : (6 : ℤ) * s ≠ 0 := by simpa using hs
  refine ⟨hr, ?_, ?_⟩
  · have hq : 72 * s ^ 2 - 17 * s + 1 ≠ 0 := by
      rcases lt_or_gt_of_ne hs with h | h
      · have : s ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ s := by omega
        nlinarith
    intro h0
    exact hq (by
      have : 6 * s * (72 * s ^ 2 - 17 * s + 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hr
      · exact h)
  · rw [satisfiesEq_iff _ _ _ hr]; ring
/-- There are infinitely many integer solutions `(x, r, k)` with `r ≠ 0` and `k ≠ 0`. -/
theorem satisfiesEq_infinite :
    {p : ℤ × ℤ × ℤ | p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ SatisfiesEq p.1 p.2.1 p.2.2}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((1 - 6 * ((n : ℤ) + 1), 6 * ((n : ℤ) + 1),
      432 * ((n : ℤ) + 1) ^ 3 - 102 * ((n : ℤ) + 1) ^ 2 + 6 * ((n : ℤ) + 1)) : ℤ × ℤ × ℤ))
    ?_ ?_
  · intro a b hab
    have : (6 : ℤ) * ((a : ℤ) + 1) = 6 * ((b : ℤ) + 1) := congrArg (fun p => p.2.1) hab
    have : (a : ℤ) = (b : ℤ) := by linarith
    exact_mod_cast this
  · intro n
    exact satisfiesEq_family ((n : ℤ) + 1) (by positivity)
/-!
## A comprehensive list of the integer solutions
The results below turn the analysis above into a complete, explicit description of the
solution set:
* `satisfiesEq_iff_factorization` — the equation is equivalent to a single factorization
  identity `(x + 6s)·(k − 6sx − 216s³ + 72s²) = 6s²(36s + 1)` with `r = 6s`;
* `satisfiesEq_iff_param` — hence the solutions are exactly the triples obtained by choosing
  `s ≠ 0` and a factorization `d·e = 6s²(36s + 1)`, and setting
  `r = 6s`, `x = d − 6s`, `k = 6s(d − 6s) + 216s³ − 72s² + e`;
* `satisfiesEq_finite` — for each fixed `r` there are only finitely many `(x, k)`;
* `satisfiesEq_six_iff` and `satisfiesEq_neg_six_iff` — the resulting explicit lists for the
  two smallest admissible values `r = 6` and `r = −6` (16 and 32 solutions respectively).
-/
/-- The equation in factorized form: for `r ≠ 0` it holds iff `r = 6s` with `s ≠ 0` and
`(x + 6s)·(k − 6sx − 216s³ + 72s²) = 6s²(36s + 1)`. -/
theorem satisfiesEq_iff_factorization (x r k : ℤ) (hr : r ≠ 0) :
    SatisfiesEq x r k ↔
      ∃ s : ℤ, s ≠ 0 ∧ r = 6 * s ∧
        (x + 6 * s) * (k - 6 * s * x - 216 * s ^ 3 + 72 * s ^ 2) = 6 * s ^ 2 * (36 * s + 1) := by
  rw [satisfiesEq_iff_exists x r k hr]
  constructor
  · rintro ⟨s, hs, rfl, h⟩
    exact ⟨s, hs, rfl, by linear_combination h⟩
  · rintro ⟨s, hs, rfl, h⟩
    exact ⟨s, hs, rfl, by linear_combination h⟩
/-- **Complete parametrization of the integer solutions.**  For `r ≠ 0`, the triple `(x, r, k)`
solves the equation exactly when there are integers `s ≠ 0` and `d`, `e` with
`d · e = 6s²(36s + 1)` such that
`r = 6s`,  `x = d − 6s`,  `k = 6s(d − 6s) + 216s³ − 72s² + e`.
So the solutions are listed by picking a nonzero `s` and a factorization of `6s²(36s + 1)`. -/
theorem satisfiesEq_iff_param (x r k : ℤ) (hr : r ≠ 0) :
    SatisfiesEq x r k ↔
      ∃ s d e : ℤ, s ≠ 0 ∧ d * e = 6 * s ^ 2 * (36 * s + 1) ∧
        r = 6 * s ∧ x = d - 6 * s ∧ k = 6 * s * (d - 6 * s) + 216 * s ^ 3 - 72 * s ^ 2 + e := by
  rw [satisfiesEq_iff_factorization x r k hr]
  constructor
  · rintro ⟨s, hs, rfl, h⟩
    exact ⟨s, x + 6 * s, k - 6 * s * x - 216 * s ^ 3 + 72 * s ^ 2, hs, h, rfl, by ring, by ring⟩
  · rintro ⟨s, d, e, hs, h, rfl, rfl, rfl⟩
    exact ⟨s, hs, rfl, by linear_combination h⟩
/-- For each fixed `r`, only finitely many pairs `(x, k)` solve the equation. -/
theorem satisfiesEq_finite (r : ℤ) (hr : r ≠ 0) :
    {p : ℤ × ℤ | SatisfiesEq p.1 r p.2}.Finite := by
  by_cases h6 : (6 : ℤ) ∣ r
  · obtain ⟨s, rfl⟩ := h6
    have hs : s ≠ 0 := by rintro rfl; simp at hr
    set N : ℤ := 6 * s ^ 2 * (36 * s + 1) with hNdef
    have hN : N ≠ 0 := by
      have h1 : (36 : ℤ) * s + 1 ≠ 0 := by omega
      simp [hNdef, hs, h1, pow_eq_zero_iff]
    have key : ∀ p : ℤ × ℤ, SatisfiesEq p.1 (6 * s) p.2 →
        (p.1 + 6 * s) * (p.2 - 6 * s * p.1 - 216 * s ^ 3 + 72 * s ^ 2) = N := by
      intro p hp
      obtain ⟨t, -, ht, h⟩ := (satisfiesEq_iff_factorization p.1 (6 * s) p.2 hr).1 hp
      have : t = s := by linarith
      subst this
      exact h
    refine Set.Finite.of_finite_image (f := Prod.fst) ?_ ?_
    · refine Set.Finite.subset (Set.finite_Icc (-|N| - 6 * s) (|N| - 6 * s)) ?_
      rintro _ ⟨p, hp, rfl⟩
      have h := key p hp
      have hdvd : (p.1 + 6 * s) ∣ N := ⟨_, h.symm⟩
      have hle : |p.1 + 6 * s| ≤ |N| :=
        Int.le_of_dvd (abs_pos.mpr hN) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr hdvd))
      rw [abs_le] at hle
      exact ⟨by linarith [hle.1], by linarith [hle.2]⟩
    · rintro ⟨x, k₁⟩ h₁ ⟨y, k₂⟩ h₂ hxy
      simp only at hxy
      subst hxy
      have e₁ := key _ h₁
      have e₂ := key _ h₂
      simp only at e₁ e₂
      have hne : x + 6 * s ≠ 0 := by
        rintro h0
        rw [h0, zero_mul] at e₁
        exact hN e₁.symm
      have : k₁ = k₂ := by
        have := e₁.trans e₂.symm
        have := mul_left_cancel₀ hne this
        linarith
      simp [this]
  · have : {p : ℤ × ℤ | SatisfiesEq p.1 r p.2} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hp => h6 (six_dvd_of_satisfiesEq hr hp)
    rw [this]
    exact Set.finite_empty
/-- Auxiliary enumeration: the factorizations of `222` in `ℤ`. -/
private theorem mul_eq_222 (d e : ℤ) (h : d * e = 222) :
    (d = 1 ∧ e = 222) ∨ (d = 2 ∧ e = 111) ∨ (d = 3 ∧ e = 74) ∨ (d = 6 ∧ e = 37) ∨
    (d = 37 ∧ e = 6) ∨ (d = 74 ∧ e = 3) ∨ (d = 111 ∧ e = 2) ∨ (d = 222 ∧ e = 1) ∨
    (d = -1 ∧ e = -222) ∨ (d = -2 ∧ e = -111) ∨ (d = -3 ∧ e = -74) ∨ (d = -6 ∧ e = -37) ∨
    (d = -37 ∧ e = -6) ∨ (d = -74 ∧ e = -3) ∨ (d = -111 ∧ e = -2) ∨ (d = -222 ∧ e = -1) := by
  have hd : d ∣ 222 := ⟨e, h.symm⟩
  have h2 : d.natAbs ∣ (222 : ℕ) := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  have h3 : d.natAbs ∈ Nat.divisors 222 := Nat.mem_divisors.mpr ⟨h2, by norm_num⟩
  have h4 : (Nat.divisors 222) = {1, 2, 3, 6, 37, 74, 111, 222} := by decide
  rw [h4] at h3
  obtain ⟨n, hn⟩ : ∃ n, d.natAbs = n := ⟨_, rfl⟩
  rw [hn] at h3
  fin_cases h3 <;>
    rcases Int.natAbs_eq d with hh | hh <;> rw [hn] at hh <;> subst hh <;>
      norm_num at h ⊢ <;> omega
/-- Auxiliary enumeration: the factorizations of `-210` in `ℤ`. -/
private theorem mul_eq_neg_210 (d e : ℤ) (h : d * e = -210) :
    (d = 1 ∧ e = -210) ∨ (d = 2 ∧ e = -105) ∨ (d = 3 ∧ e = -70) ∨ (d = 5 ∧ e = -42) ∨
    (d = 6 ∧ e = -35) ∨ (d = 7 ∧ e = -30) ∨ (d = 10 ∧ e = -21) ∨ (d = 14 ∧ e = -15) ∨
    (d = 15 ∧ e = -14) ∨ (d = 21 ∧ e = -10) ∨ (d = 30 ∧ e = -7) ∨ (d = 35 ∧ e = -6) ∨
    (d = 42 ∧ e = -5) ∨ (d = 70 ∧ e = -3) ∨ (d = 105 ∧ e = -2) ∨ (d = 210 ∧ e = -1) ∨
    (d = -1 ∧ e = 210) ∨ (d = -2 ∧ e = 105) ∨ (d = -3 ∧ e = 70) ∨ (d = -5 ∧ e = 42) ∨
    (d = -6 ∧ e = 35) ∨ (d = -7 ∧ e = 30) ∨ (d = -10 ∧ e = 21) ∨ (d = -14 ∧ e = 15) ∨
    (d = -15 ∧ e = 14) ∨ (d = -21 ∧ e = 10) ∨ (d = -30 ∧ e = 7) ∨ (d = -35 ∧ e = 6) ∨
    (d = -42 ∧ e = 5) ∨ (d = -70 ∧ e = 3) ∨ (d = -105 ∧ e = 2) ∨ (d = -210 ∧ e = 1) := by
  have hd : d ∣ (-210 : ℤ) := ⟨e, h.symm⟩
  have h2 : d.natAbs ∣ (210 : ℕ) := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  have h3 : d.natAbs ∈ Nat.divisors 210 := Nat.mem_divisors.mpr ⟨h2, by norm_num⟩
  have h4 : (Nat.divisors 210) =
      {1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210} := by decide
  rw [h4] at h3
  obtain ⟨n, hn⟩ : ∃ n, d.natAbs = n := ⟨_, rfl⟩
  rw [hn] at h3
  fin_cases h3 <;>
    rcases Int.natAbs_eq d with hh | hh <;> rw [hn] at hh <;> subst hh <;>
      norm_num at h ⊢ <;> omega
/-- **The complete list of solutions for `r = 6`**: there are exactly 16 pairs `(x, k)`. -/
theorem satisfiesEq_six_iff (x k : ℤ) :
    SatisfiesEq x 6 k ↔
      (x = -5 ∧ k = 336) ∨ (x = -4 ∧ k = 231) ∨ (x = -3 ∧ k = 200) ∨ (x = 0 ∧ k = 181) ∨
      (x = 31 ∧ k = 336) ∨ (x = 68 ∧ k = 555) ∨ (x = 105 ∧ k = 776) ∨ (x = 216 ∧ k = 1441) ∨
      (x = -7 ∧ k = -120) ∨ (x = -8 ∧ k = -15) ∨ (x = -9 ∧ k = 16) ∨ (x = -12 ∧ k = 35) ∨
      (x = -43 ∧ k = -120) ∨ (x = -80 ∧ k = -339) ∨ (x = -117 ∧ k = -560) ∨
      (x = -228 ∧ k = -1225) := by
  rw [satisfiesEq_iff x 6 k (by norm_num)]
  constructor
  · intro h
    have h6 : (6 : ℤ) * ((x + 6) * (k - 6 * x - 144)) = 6 * 222 := by linear_combination h
    have hcases := mul_eq_222 _ _ (mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0) h6)
    clear h h6
    casesm* _ ∨ _, _ ∧ _ <;>
      repeat first
        | exact Or.inl ⟨by omega, by omega⟩
        | exact ⟨by omega, by omega⟩
        | apply Or.inr
  · intro h
    casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> norm_num
/-- **The complete list of solutions for `r = -6`**: there are exactly 32 pairs `(x, k)`. -/
theorem satisfiesEq_neg_six_iff (x k : ℤ) :
    SatisfiesEq x (-6) k ↔
      (x = 7 ∧ k = -540) ∨ (x = 8 ∧ k = -441) ∨ (x = 9 ∧ k = -412) ∨ (x = 11 ∧ k = -396) ∨
      (x = 12 ∧ k = -395) ∨ (x = 13 ∧ k = -396) ∨ (x = 16 ∧ k = -405) ∨ (x = 20 ∧ k = -423) ∨
      (x = 21 ∧ k = -428) ∨ (x = 27 ∧ k = -460) ∨ (x = 36 ∧ k = -511) ∨ (x = 41 ∧ k = -540) ∨
      (x = 48 ∧ k = -581) ∨ (x = 76 ∧ k = -747) ∨ (x = 111 ∧ k = -956) ∨
      (x = 216 ∧ k = -1585) ∨
      (x = 5 ∧ k = -108) ∨ (x = 4 ∧ k = -207) ∨ (x = 3 ∧ k = -236) ∨ (x = 1 ∧ k = -252) ∨
      (x = 0 ∧ k = -253) ∨ (x = -1 ∧ k = -252) ∨ (x = -4 ∧ k = -243) ∨ (x = -8 ∧ k = -225) ∨
      (x = -9 ∧ k = -220) ∨ (x = -15 ∧ k = -188) ∨ (x = -24 ∧ k = -137) ∨
      (x = -29 ∧ k = -108) ∨ (x = -36 ∧ k = -67) ∨ (x = -64 ∧ k = 99) ∨ (x = -99 ∧ k = 308) ∨
      (x = -204 ∧ k = 937) := by
  rw [satisfiesEq_iff x (-6) k (by norm_num)]
  constructor
  · intro h
    have h6 : (6 : ℤ) * ((x - 6) * (k + 6 * x + 288)) = 6 * (-210) := by linear_combination h
    have hcases := mul_eq_neg_210 _ _ (mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0) h6)
    clear h h6
    casesm* _ ∨ _, _ ∧ _ <;>
      repeat first
        | exact Or.inl ⟨by omega, by omega⟩
        | exact ⟨by omega, by omega⟩
        | apply Or.inr
  · intro h
    casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> norm_num
/-- Every solution with `r = 6` automatically has `k ≠ 0`. -/
theorem satisfiesEq_six_k_ne_zero {x k : ℤ} (h : SatisfiesEq x 6 k) : k ≠ 0 := by
  rw [satisfiesEq_six_iff] at h
  casesm* _ ∨ _, _ ∧ _ <;> omega
/-- Every solution with `r = -6` automatically has `k ≠ 0`. -/
theorem satisfiesEq_neg_six_k_ne_zero {x k : ℤ} (h : SatisfiesEq x (-6) k) : k ≠ 0 := by
  rw [satisfiesEq_neg_six_iff] at h
  casesm* _ ∨ _, _ ∧ _ <;> omega
/-- The solution set for `r = 6`, listed as a set of pairs `(x, k)`. -/
theorem satisfiesEq_six_solutionSet :
    {p : ℤ × ℤ | SatisfiesEq p.1 6 p.2} =
      {(-5, 336), (-4, 231), (-3, 200), (0, 181), (31, 336), (68, 555), (105, 776), (216, 1441),
        (-7, -120), (-8, -15), (-9, 16), (-12, 35), (-43, -120), (-80, -339), (-117, -560),
        (-228, -1225)} := by
  ext ⟨x, k⟩
  simp only [Set.mem_setOf_eq, satisfiesEq_six_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
/-- There are exactly `16` solutions with `r = 6`. -/
theorem satisfiesEq_six_ncard : {p : ℤ × ℤ | SatisfiesEq p.1 6 p.2}.ncard = 16 := by
  have h : {p : ℤ × ℤ | SatisfiesEq p.1 6 p.2} =
      (({(-5, 336), (-4, 231), (-3, 200), (0, 181), (31, 336), (68, 555), (105, 776), (216, 1441),
        (-7, -120), (-8, -15), (-9, 16), (-12, 35), (-43, -120), (-80, -339), (-117, -560),
        (-228, -1225)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    ext ⟨x, k⟩
    simp only [Set.mem_setOf_eq, satisfiesEq_six_iff, Finset.coe_insert, Set.mem_insert_iff,
      Finset.coe_singleton, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [h, Set.ncard_coe_finset]
  decide
/-- The solution set for `r = -6`, listed as a set of pairs `(x, k)`. -/
theorem satisfiesEq_neg_six_solutionSet :
    {p : ℤ × ℤ | SatisfiesEq p.1 (-6) p.2} =
      {(7, -540), (8, -441), (9, -412), (11, -396), (12, -395), (13, -396), (16, -405),
        (20, -423), (21, -428), (27, -460), (36, -511), (41, -540), (48, -581), (76, -747),
        (111, -956), (216, -1585), (5, -108), (4, -207), (3, -236), (1, -252), (0, -253),
        (-1, -252), (-4, -243), (-8, -225), (-9, -220), (-15, -188), (-24, -137), (-29, -108),
        (-36, -67), (-64, 99), (-99, 308), (-204, 937)} := by
  ext ⟨x, k⟩
  simp only [Set.mem_setOf_eq, satisfiesEq_neg_six_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
/-- There are exactly `32` solutions with `r = -6`. -/
theorem satisfiesEq_neg_six_ncard : {p : ℤ × ℤ | SatisfiesEq p.1 (-6) p.2}.ncard = 32 := by
  have h : {p : ℤ × ℤ | SatisfiesEq p.1 (-6) p.2} =
      ((({(7, -540), (8, -441), (9, -412), (11, -396), (12, -395), (13, -396), (16, -405),
        (20, -423), (21, -428), (27, -460), (36, -511), (41, -540), (48, -581), (76, -747),
        (111, -956), (216, -1585), (5, -108), (4, -207), (3, -236), (1, -252), (0, -253),
        (-1, -252), (-4, -243), (-8, -225), (-9, -220), (-15, -188), (-24, -137), (-29, -108),
        (-36, -67), (-64, 99), (-99, 308), (-204, 937)}) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    ext ⟨x, k⟩
    simp only [Set.mem_setOf_eq, satisfiesEq_neg_six_iff, Finset.coe_insert, Set.mem_insert_iff,
      Finset.coe_singleton, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [h, Set.ncard_coe_finset]
  decide
/-!
## The case `k = 114`: there are no solutions at all
For the specific value `k = 114` the equation has **no** integer solutions `(x, r)` with
`r ≠ 0`.  Indeed, writing `r = 6s` (`s ≠ 0`) and `d = x + 6s`, the factorized form
`(x + 6s)·(k − 6sx − 216s³ + 72s²) = 6s²(36s + 1)` becomes, after dividing by `6`,
  `s d² + (36s³ − 18s² − 19) d + s²(36s + 1) = 0`.
Multiplying by `4s` and completing the square, `y = 2sd + 36s³ − 18s² − 19` must satisfy
  `y² = Δ(s) := 1296s⁶ − 1296s⁵ + 180s⁴ − 1372s³ + 684s² + 361`.
For `s ≥ 3` one has `(36s³ − 18s² − 2s − 21)² < Δ(s) < (36s³ − 18s² − 2s − 20)²`, and for
`s ≤ −8` one has `(36s³ − 18s² − 2s − 20)² < Δ(s) < (36s³ − 18s² − 2s − 21)²`; in both ranges
`Δ(s)` is squeezed strictly between the squares of two consecutive nonnegative integers, so it
is not a square.  The remaining values `s ∈ {−7, …, −1, 1, 2}` are checked one by one
(`Δ(1) = −147 < 0`, and for the others `Δ(s)` lies strictly between two consecutive squares).
-/
/-- No integer square lies strictly between `m²` and `(m+1)²` for `m ≥ 0`. -/
theorem no_int_sq_strictly_between {y m : ℤ} (hm : 0 ≤ m) (h1 : m ^ 2 < y ^ 2)
    (h2 : y ^ 2 < (m + 1) ^ 2) : False := by
  by_cases hy : 0 ≤ y
  · have hlt : m < y := by nlinarith
    have : m + 1 ≤ y := by omega
    nlinarith
  · have hy : y < 0 := by omega
    have hlt : m < -y := by nlinarith
    have : m + 1 ≤ -y := by omega
    nlinarith
/-- **For `k = 114` there is no integer solution.**  No pair of integers `(x, r)` with `r ≠ 0`
satisfies the equation when `k = 114`. -/
theorem not_satisfiesEq_114 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 114 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 114 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  -- the quadratic satisfied by `d = x + 6s`
  have key : s * (x + 6 * s) ^ 2 + (x + 6 * s) * (36 * s ^ 3 - 18 * s ^ 2 - 19)
      + s ^ 2 * (36 * s + 1) = 0 := by
    have h6 : 6 * (s * (x + 6 * s) ^ 2 + (x + 6 * s) * (36 * s ^ 3 - 18 * s ^ 2 - 19)
        + s ^ 2 * (36 * s + 1)) = 0 := by linear_combination -heq
    linarith
  -- completing the square
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 1296 * s ^ 6 - 1296 * s ^ 5 + 180 * s ^ 4 - 1372 * s ^ 3
      + 684 * s ^ 2 + 361 :=
    ⟨2 * s * (x + 6 * s) + 36 * s ^ 3 - 18 * s ^ 2 - 19, by linear_combination (4 * s) * key⟩
  clear key heq
  by_cases hb : 3 ≤ s
  · exact no_int_sq_strictly_between (y := y) (m := 36 * s ^ 3 - 18 * s ^ 2 - 2 * s - 21)
      (by nlinarith [sq_nonneg (s - 3), sq_nonneg s]) (by rw [hy]; nlinarith [sq_nonneg (s - 3)])
      (by rw [hy]; nlinarith [sq_nonneg (s - 3)])
  by_cases hb2 : s ≤ -8
  · exact no_int_sq_strictly_between (y := y) (m := -36 * s ^ 3 + 18 * s ^ 2 + 2 * s + 20)
      (by nlinarith [sq_nonneg (s + 8), sq_nonneg s]) (by rw [hy]; nlinarith [sq_nonneg (s + 8)])
      (by rw [hy]; nlinarith [sq_nonneg (s + 8)])
  · have hl : -7 ≤ s := by omega
    have hu : s ≤ 2 := by omega
    interval_cases s <;> first
      | exact hs rfl
      | norm_num at hy
    · exact no_int_sq_strictly_between (y := y) (m := 13235) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · exact no_int_sq_strictly_between (y := y) (m := 8431) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · exact no_int_sq_strictly_between (y := y) (m := 4959) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · exact no_int_sq_strictly_between (y := y) (m := 2603) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · exact no_int_sq_strictly_between (y := y) (m := 1147) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · exact no_int_sq_strictly_between (y := y) (m := 375) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · exact no_int_sq_strictly_between (y := y) (m := 72) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
    · nlinarith [sq_nonneg y]
    · exact no_int_sq_strictly_between (y := y) (m := 190) (by norm_num) (by rw [hy]; norm_num)
        (by rw [hy]; norm_num)
/-- **The solution set for `k = 114` is empty.** -/
theorem satisfiesEq_114_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 114} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_114 x r hr
/-!
## The values `k = 390, 627, 633, 732, 921, 975`
For each of these six values of `k` the equation has **no** integer solution `(x, r)` with
`r ≠ 0`.
The argument is uniform.  By `satisfiesEq_iff_factorization` a solution forces `r = 6s` with
`s ≠ 0` and, writing `d = x + 6s`,
  `6s·d² − (k − 216s³ + 108s²)·d + 216s³ + 6s² = 0`.
Multiplying by `24s` and completing the square, `y = 12s·d − (k − 216s³ + 108s²)` must satisfy
  `y² = Δ(s, k) := 46656s⁶ − 46656s⁵ + 6480s⁴ − (432k + 144)s³ + 216k·s² + k²`.
Setting `P(s, k) = 216s³ − 108s² − 12s − k − 6` one has the two polynomial identities
  `Δ − P²       = −144s³ − 1440s² − (24k + 144)s − 12k − 36`,
  `Δ − (P − 1)² = 288s³ − 1656s² − (24k + 168)s − 14k − 49`.
Hence for `390 ≤ k ≤ 975`:  if `s ≥ 13` then `(P − 1)² < Δ < P²` with `P − 1 ≥ 0`, and if
`s ≤ −7` then `P² < Δ < (P − 1)²` with `−P ≥ 0`; in both cases `Δ` is trapped strictly between
the squares of two consecutive nonnegative integers, so it is not a square.  The remaining
finitely many `s` with `−6 ≤ s ≤ 12`, `s ≠ 0` are checked one by one, again by exhibiting for
each the integer `m` with `m² < Δ < (m + 1)²`.
-/
/-- For `390 ≤ k ≤ 975` and `|s|` large, the discriminant `Δ(s, k)` is not a perfect square. -/
theorem disc_not_square_large {k s y : ℤ} (hk : 390 ≤ k) (hk' : k ≤ 975)
    (hs : 13 ≤ s ∨ s ≤ -7)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * k + 144) * s ^ 3
      + 216 * k * s ^ 2 + k ^ 2) : False := by
  rcases hs with hs | hs
  · refine no_int_sq_strictly_between (y := y) (m := 216 * s ^ 3 - 108 * s ^ 2 - 12 * s - k - 7)
      ?_ ?_ ?_
    · nlinarith [sq_nonneg (s - 13), sq_nonneg s]
    · rw [hy]; nlinarith [sq_nonneg (s - 13), sq_nonneg s]
    · rw [hy]; nlinarith [sq_nonneg (s - 13), sq_nonneg s]
  · refine no_int_sq_strictly_between (y := y) (m := -216 * s ^ 3 + 108 * s ^ 2 + 12 * s + k + 6)
      ?_ ?_ ?_
    · nlinarith [sq_nonneg (s + 7), sq_nonneg s]
    · rw [hy]; nlinarith [sq_nonneg (s + 7), sq_nonneg s]
    · rw [hy]; nlinarith [sq_nonneg (s + 7), sq_nonneg s]
/-- For `k = 390` and `-6 ≤ s ≤ 12`, `s ≠ 0`, the discriminant `Δ(s, 390)` is not a perfect
square. -/
theorem disc_not_square_small_390 {s y : ℤ} (hs : s ≠ 0) (h1 : -6 ≤ s) (h2 : s ≤ 12)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 390 + 144) * s ^ 3 + 216 * 390 * s ^ 2 + 390 ^ 2) : False := by
  interval_cases s <;> first | exact hs rfl | norm_num at hy
  · exact no_int_sq_strictly_between (y := y) (m := 50868) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 30036) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 15900) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 7165) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 2533) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 710) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 272) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 858) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 4422) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 11648) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 23841) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 42298) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 68314) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 103186) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 148210) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 204683) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 273899) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 357155) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
/-- **For `k = 390` there is no integer solution.** -/
theorem not_satisfiesEq_390 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 390 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 390 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 390 + 144) * s ^ 3 + 216 * 390 * s ^ 2 + 390 ^ 2 :=
    ⟨12 * s * (x + 6 * s) - (390 - 216 * s ^ 3 + 108 * s ^ 2), by linear_combination (-24 * s) * heq⟩
  clear heq
  by_cases hb : 13 ≤ s ∨ s ≤ -7
  · exact disc_not_square_large (by norm_num) (by norm_num) hb hy
  · push_neg at hb
    exact disc_not_square_small_390 hs (by omega) (by omega) hy
/-- **The solution set for `k = 390` is empty.** -/
theorem satisfiesEq_390_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 390} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_390 x r hr
/-- For `k = 627` and `-6 ≤ s ≤ 12`, `s ≠ 0`, the discriminant `Δ(s, 627)` is not a perfect
square. -/
theorem disc_not_square_small_627 {s y : ℤ} (hs : s ≠ 0) (h1 : -6 ≤ s) (h2 : s ≤ 12)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 627 + 144) * s ^ 3 + 216 * 627 * s ^ 2 + 627 ^ 2) : False := by
  interval_cases s <;> first | exact hs rfl | norm_num at hy
  · exact no_int_sq_strictly_between (y := y) (m := 51105) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 30273) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 16138) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 7402) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 2772) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 948) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 513) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 602) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 4182) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 11410) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 23604) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 42060) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 68077) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 102949) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 147973) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 204445) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 273662) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 356918) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
/-- **For `k = 627` there is no integer solution.** -/
theorem not_satisfiesEq_627 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 627 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 627 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 627 + 144) * s ^ 3 + 216 * 627 * s ^ 2 + 627 ^ 2 :=
    ⟨12 * s * (x + 6 * s) - (627 - 216 * s ^ 3 + 108 * s ^ 2), by linear_combination (-24 * s) * heq⟩
  clear heq
  by_cases hb : 13 ≤ s ∨ s ≤ -7
  · exact disc_not_square_large (by norm_num) (by norm_num) hb hy
  · push_neg at hb
    exact disc_not_square_small_627 hs (by omega) (by omega) hy
/-- **The solution set for `k = 627` is empty.** -/
theorem satisfiesEq_627_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 627} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_627 x r hr
/-- For `k = 633` and `-6 ≤ s ≤ 12`, `s ≠ 0`, the discriminant `Δ(s, 633)` is not a perfect
square. -/
theorem disc_not_square_small_633 {s y : ℤ} (hs : s ≠ 0) (h1 : -6 ≤ s) (h2 : s ≤ 12)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 633 + 144) * s ^ 3 + 216 * 633 * s ^ 2 + 633 ^ 2) : False := by
  interval_cases s <;> first | exact hs rfl | norm_num at hy
  · exact no_int_sq_strictly_between (y := y) (m := 51111) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 30279) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 16144) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 7408) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 2778) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 954) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 519) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 596) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 4176) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 11404) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 23598) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 42054) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 68071) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 102943) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 147967) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 204439) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 273656) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 356912) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
/-- **For `k = 633` there is no integer solution.** -/
theorem not_satisfiesEq_633 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 633 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 633 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 633 + 144) * s ^ 3 + 216 * 633 * s ^ 2 + 633 ^ 2 :=
    ⟨12 * s * (x + 6 * s) - (633 - 216 * s ^ 3 + 108 * s ^ 2), by linear_combination (-24 * s) * heq⟩
  clear heq
  by_cases hb : 13 ≤ s ∨ s ≤ -7
  · exact disc_not_square_large (by norm_num) (by norm_num) hb hy
  · push_neg at hb
    exact disc_not_square_small_633 hs (by omega) (by omega) hy
/-- **The solution set for `k = 633` is empty.** -/
theorem satisfiesEq_633_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 633} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_633 x r hr
/-- For `k = 732` and `-6 ≤ s ≤ 12`, `s ≠ 0`, the discriminant `Δ(s, 732)` is not a perfect
square. -/
theorem disc_not_square_small_732 {s y : ℤ} (hs : s ≠ 0) (h1 : -6 ≤ s) (h2 : s ≤ 12)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 732 + 144) * s ^ 3 + 216 * 732 * s ^ 2 + 732 ^ 2) : False := by
  interval_cases s <;> first | exact hs rfl | norm_num at hy
  · exact no_int_sq_strictly_between (y := y) (m := 51210) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 30379) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 16243) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 7508) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 2877) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 1053) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 619) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 483) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 4076) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 11305) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 23498) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 41955) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 67972) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 102844) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 147868) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 204340) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 273556) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 356813) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
/-- **For `k = 732` there is no integer solution.** -/
theorem not_satisfiesEq_732 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 732 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 732 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 732 + 144) * s ^ 3 + 216 * 732 * s ^ 2 + 732 ^ 2 :=
    ⟨12 * s * (x + 6 * s) - (732 - 216 * s ^ 3 + 108 * s ^ 2), by linear_combination (-24 * s) * heq⟩
  clear heq
  by_cases hb : 13 ≤ s ∨ s ≤ -7
  · exact disc_not_square_large (by norm_num) (by norm_num) hb hy
  · push_neg at hb
    exact disc_not_square_small_732 hs (by omega) (by omega) hy
/-- **The solution set for `k = 732` is empty.** -/
theorem satisfiesEq_732_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 732} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_732 x r hr
/-- For `k = 921` and `-6 ≤ s ≤ 12`, `s ≠ 0`, the discriminant `Δ(s, 921)` is not a perfect
square. -/
theorem disc_not_square_small_921 {s y : ℤ} (hs : s ≠ 0) (h1 : -6 ≤ s) (h2 : s ≤ 12)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 921 + 144) * s ^ 3 + 216 * 921 * s ^ 2 + 921 ^ 2) : False := by
  interval_cases s <;> first | exact hs rfl | norm_num at hy
  · exact no_int_sq_strictly_between (y := y) (m := 51399) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 30568) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 16432) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 7698) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 3067) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 1242) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 809) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 237) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 3884) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 11115) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 23309) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 41766) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 67782) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 102655) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 147679) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 204151) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 273367) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 356623) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
/-- **For `k = 921` there is no integer solution.** -/
theorem not_satisfiesEq_921 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 921 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 921 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 921 + 144) * s ^ 3 + 216 * 921 * s ^ 2 + 921 ^ 2 :=
    ⟨12 * s * (x + 6 * s) - (921 - 216 * s ^ 3 + 108 * s ^ 2), by linear_combination (-24 * s) * heq⟩
  clear heq
  by_cases hb : 13 ≤ s ∨ s ≤ -7
  · exact disc_not_square_large (by norm_num) (by norm_num) hb hy
  · push_neg at hb
    exact disc_not_square_small_921 hs (by omega) (by omega) hy
/-- **The solution set for `k = 921` is empty.** -/
theorem satisfiesEq_921_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 921} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_921 x r hr
/-- For `k = 975` and `-6 ≤ s ≤ 12`, `s ≠ 0`, the discriminant `Δ(s, 975)` is not a perfect
square. -/
theorem disc_not_square_small_975 {s y : ℤ} (hs : s ≠ 0) (h1 : -6 ≤ s) (h2 : s ≤ 12)
    (hy : y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 975 + 144) * s ^ 3 + 216 * 975 * s ^ 2 + 975 ^ 2) : False := by
  interval_cases s <;> first | exact hs rfl | norm_num at hy
  · exact no_int_sq_strictly_between (y := y) (m := 51454) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 30622) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 16487) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 7752) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 3121) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 1297) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 863) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 137) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 3830) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 11060) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 23255) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 41712) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 67728) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 102601) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 147625) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 204097) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 273313) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  · exact no_int_sq_strictly_between (y := y) (m := 356569) (by norm_num)
      (by rw [hy]; norm_num) (by rw [hy]; norm_num)
/-- **For `k = 975` there is no integer solution.** -/
theorem not_satisfiesEq_975 (x r : ℤ) (hr : r ≠ 0) : ¬ SatisfiesEq x r 975 := by
  intro h
  rw [satisfiesEq_iff_factorization x r 975 hr] at h
  obtain ⟨s, hs, rfl, heq⟩ := h
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y ^ 2 = 46656 * s ^ 6 - 46656 * s ^ 5 + 6480 * s ^ 4 - (432 * 975 + 144) * s ^ 3 + 216 * 975 * s ^ 2 + 975 ^ 2 :=
    ⟨12 * s * (x + 6 * s) - (975 - 216 * s ^ 3 + 108 * s ^ 2), by linear_combination (-24 * s) * heq⟩
  clear heq
  by_cases hb : 13 ≤ s ∨ s ≤ -7
  · exact disc_not_square_large (by norm_num) (by norm_num) hb hy
  · push_neg at hb
    exact disc_not_square_small_975 hs (by omega) (by omega) hy
/-- **The solution set for `k = 975` is empty.** -/
theorem satisfiesEq_975_solutionSet :
    {p : ℤ × ℤ | p.2 ≠ 0 ∧ SatisfiesEq p.1 p.2 975} = ∅ := by
  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hr => not_satisfiesEq_975 x r hr
/-- **Summary for the six requested values of `k`.**  For `k ∈ {390, 627, 633, 732, 921, 975}`
the equation has no integer solution `(x, r)` with `r ≠ 0`. -/
theorem not_satisfiesEq_of_mem_list (x r k : ℤ) (hr : r ≠ 0)
    (hk : k = 390 ∨ k = 627 ∨ k = 633 ∨ k = 732 ∨ k = 921 ∨ k = 975) :
    ¬ SatisfiesEq x r k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_satisfiesEq_390 x r hr
  · exact not_satisfiesEq_627 x r hr
  · exact not_satisfiesEq_633 x r hr
  · exact not_satisfiesEq_732 x r hr
  · exact not_satisfiesEq_921 x r hr
  · exact not_satisfiesEq_975 x r hr
end QuadraticIntegerSolutions
