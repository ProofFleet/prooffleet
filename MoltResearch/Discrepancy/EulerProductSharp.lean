import MoltResearch.Discrepancy.SmoothRankinTail

/-!
# A linear-plus-quadratic Euler-product bound

The generic estimate `prod_inv_one_sub_le_exp` costs twice the reciprocal
prime mass.  On a remote prime interval it is useful to retain the sharper
local expansion

`(1 - x)⁻¹ ≤ exp (x + 2*x²)` for `0 ≤ x ≤ 1/2`.

The resulting finite-product bound separates the Mertens-sized linear mass
from the absolutely summable square mass.
-/

namespace MoltResearch

open Finset

/-- A single reciprocal Euler factor is controlled by its linear and
quadratic Taylor terms. -/
theorem inv_one_sub_le_exp_linear_quadratic
    (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (x + 2 * x ^ 2) := by
  have hden : 0 < 1 - x := by linarith
  have hfrac0 : 0 ≤ x / (1 - x) := div_nonneg hx0 hden.le
  have hfrac : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 - 2 * x)]
  calc
    (1 - x)⁻¹ = 1 + x / (1 - x) := by field_simp; ring
    _ ≤ Real.exp (x / (1 - x)) := by
      simpa [add_comm] using Real.add_one_le_exp (x / (1 - x))
    _ ≤ Real.exp (x + 2 * x ^ 2) := Real.exp_le_exp.mpr hfrac

/-- The sharp finite Euler-product estimate. -/
theorem prod_inv_one_sub_le_exp_linear_quadratic
    (P : Finset ℕ) (r : ℕ → ℝ)
    (hr0 : ∀ p ∈ P, 0 ≤ r p) (hr : ∀ p ∈ P, r p ≤ 1 / 2) :
    ∏ p ∈ P, (1 - r p)⁻¹ ≤
      Real.exp ((∑ p ∈ P, r p) + 2 * ∑ p ∈ P, (r p) ^ 2) := by
  calc
    ∏ p ∈ P, (1 - r p)⁻¹ ≤
        ∏ p ∈ P, Real.exp (r p + 2 * (r p) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hden : 0 < 1 - r p := by linarith [hr p hp]
        positivity
      · intro p hp
        exact inv_one_sub_le_exp_linear_quadratic (r p) (hr0 p hp) (hr p hp)
    _ = Real.exp (∑ p ∈ P, (r p + 2 * (r p) ^ 2)) := by
      rw [← Real.exp_sum]
    _ = Real.exp ((∑ p ∈ P, r p) + 2 * ∑ p ∈ P, (r p) ^ 2) := by
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The harmonic mass of integers supported on `P` pays one copy of the
reciprocal prime mass and an absolutely summable quadratic correction. -/
theorem pSmoothHarmonicMass_le_exp_primeMass_sq
    (B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    pSmoothHarmonicMass B P ≤
      Real.exp ((∑ p ∈ P, (1 : ℝ) / p) +
        2 * ∑ p ∈ P, ((1 : ℝ) / p) ^ 2) := by
  have hprod := sum_pSmooth_rpow_le_prod B P hP 1 (by norm_num)
  have heuler := prod_inv_one_sub_le_exp_linear_quadratic P
    (fun p => (1 : ℝ) / p)
    (fun p hp => by positivity)
    (fun p hp => by
      have hp2 : 2 ≤ p := (hP p hp).two_le
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      exact one_div_le_one_div_of_le (by norm_num) hp2R)
  have hprod' : pSmoothHarmonicMass B P ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
    simpa [pSmoothHarmonicMass, Real.rpow_neg_one] using hprod
  exact hprod'.trans heuler

end MoltResearch
