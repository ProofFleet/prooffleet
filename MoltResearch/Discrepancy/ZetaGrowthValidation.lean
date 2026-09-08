import MoltResearch.Discrepancy.ZetaGrowthRegion

/-!
# Validation of the growth parametrization

The tree's extended-strip estimate has logarithmic size `2 * log |t|`.
The already checked de la Vallee Poussin assembly turns precisely this coarse
linear-logarithmic regime into a zero-free width of order `1 / log |t|`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- Logarithmic form of the tree's crude extended-strip zeta estimate. -/
theorem zeta_crude_log_norm_upper (σ t : ℝ)
    (hσl : 1 / 2 ≤ σ) (hσu : σ ≤ 5 / 2) (ht : 4 ≤ |t|) :
    Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤
      2 * Real.log |t| + Real.log 10000 := by
  have hupper' := zeta_norm_upper σ (-t) hσl hσu (by simpa using ht)
  have hupper : ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤ 10000 * t ^ 2 := by
    convert hupper' using 1 <;> push_cast <;> ring_nf
  by_cases hz : riemannZeta ((σ : ℂ) + I * t) = 0
  · rw [hz, norm_zero, Real.log_zero]
    have hlogt : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    have hlogc : 0 ≤ Real.log 10000 := Real.log_nonneg (by norm_num)
    linarith
  · have hnorm0 : 0 < ‖riemannZeta ((σ : ℂ) + I * t)‖ := norm_pos_iff.mpr hz
    have ht0 : 0 < |t| := by linarith
    have htne : t ≠ 0 := abs_pos.mp ht0
    calc
      Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤
          Real.log (10000 * t ^ 2) := Real.log_le_log hnorm0 hupper
      _ = Real.log 10000 + Real.log (t ^ 2) :=
        Real.log_mul (by norm_num) (pow_ne_zero 2 htne)
      _ = 2 * Real.log |t| + Real.log 10000 := by
        rw [Real.log_pow, Real.log_abs]
        push_cast
        ring

/-- **V-C4-5.**  The crude logarithmic growth regime and the resulting
de la Vallee Poussin zero-free width coexist with the expected constants. -/
theorem zeta_crude_growth_validation :
    (∀ σ t : ℝ, 4 ≤ |t| → 1 / 2 ≤ σ → σ ≤ 5 / 2 →
      Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤
        2 * Real.log |t| + Real.log 10000) ∧
    ∃ c t₁ : ℝ, 0 < c ∧ 4 ≤ t₁ ∧ ∀ β t : ℝ, t₁ ≤ |t| →
      riemannZeta ((β : ℂ) + I * t) = 0 →
        β ≤ 1 - c / Real.log |t| := by
  constructor
  · intro σ t ht hσl hσu
    exact zeta_crude_log_norm_upper σ t hσl hσu ht
  · obtain ⟨c, hc, hzero⟩ := zeta_zero_free_region
    exact ⟨c, 8, hc, by norm_num, hzero⟩

end ExpSums

end MoltResearch
