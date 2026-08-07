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
end QuadraticIntegerSolutions
