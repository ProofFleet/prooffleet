import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalRankinTail

/-!
# Track R A2-V': exponential-form exceptional Rankin tail

The fixed sharp-envelope interface uses the exponential majorant of the
tilted Euler product.  This leaf records the corresponding uniform tail
bound with exactly the same fixed allocation.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The exponential Rankin majorant fits in the fixed tail budget uniformly
over every exceptional quotient in the quadratic scale window. -/
theorem exists_sliceA2Exceptional_rankin_exp_tail_le
    (Cp : ℝ)
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 → Delta ≤ A →
      ∀ v : ℕ,
        (Real.log (((A + Delta) /
            sliceA2ExceptionalRepresentative A1 v epsc eps rho0 : ℕ) : ℝ) + 1) *
          (((((A /
              sliceA2ExceptionalRepresentative A1 v epsc eps rho0 : ℕ) : ℝ) /
                exceptionalSharpCutoff A) ^
              (-sliceA2ExceptionalRankinS A1 epsc)) *
            Real.exp (2 * ∑ p ∈ exceptionalPrimes A1 epsc,
              (p : ℝ) ^
                (-(1 - sliceA2ExceptionalRankinS A1 epsc)))) ≤
          sliceA2ExceptionalTailBudget Cp epsc eps rho0 := by
  obtain ⟨AS, hAS⟩ :=
    exists_sliceA2Exceptional_rankin_scalar_margin Cp epsc eps rho0 heps hrho0
  obtain ⟨AQ, hAQ⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    1 4 epsc (by norm_num) (by norm_num)
  obtain ⟨AL, hAL⟩ := exists_sliceA2_log_ge (8 * Real.log 8)
  obtain ⟨AP, hAP⟩ := exists_exceptionalPrimeLower_ge 6
  refine ⟨max 4 (max AS (max AQ (max AL AP))),
    fun A1 A Delta hA1 hA hAupper hDelta v => ?_⟩
  have hA14 : 4 ≤ A1 := (le_max_left _ _).trans hA1
  have hAS1 : AS ≤ A1 := by omega
  have hAQ1 : AQ ≤ A1 := by omega
  have hAL1 : AL ≤ A1 := by omega
  have hAP1 : AP ≤ A1 := by omega
  let q := sliceA2ExceptionalRepresentative A1 v epsc eps rho0
  let s := sliceA2ExceptionalRankinS A1 epsc
  let X := Real.log (A1 : ℝ)
  have hq : 1 ≤ q := by
    dsimp [q]
    exact (sliceA2Exceptional_cell_data A1 epsc eps rho0).2.2.1 v
  have hqQ : q ≤ exceptionalPrimeUpper A1 epsc := by
    dsimp [q]
    exact sliceA2ExceptionalRepresentative_le_upper A1 v epsc eps rho0
  have hQ4real : (exceptionalPrimeUpper A1 epsc : ℝ) ^ 4 ≤ A1 := by
    simpa using hAQ A1 hAQ1
  have hQ4 : exceptionalPrimeUpper A1 epsc ^ 4 ≤ A1 := by
    exact_mod_cast hQ4real
  have hq4 : q ^ 4 ≤ A1 :=
    (pow_le_pow_left' hqQ 4).trans hQ4
  have hlog8 : 8 * Real.log 8 ≤ X := by
    simpa [X] using hAL A1 hAL1
  have hlower : 6 ≤ exceptionalPrimeLower A1 := by
    exact_mod_cast hAP A1 hAP1
  have hlogFactor :
      Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 ≤ 3 * X + 2 := by
    simpa [X] using sliceA2Exceptional_quotient_log_factor_le
      A1 A Delta q (by omega) hAupper hDelta
  have hlogFactor0 : 0 ≤ Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 := by
    have hq0 : 0 < q := by omega
    have hq2q4 : q ^ 2 ≤ q ^ 4 := pow_le_pow_right' hq (by omega)
    have hq2A : q * q ≤ A := by
      simpa [pow_two] using hq2q4.trans (hq4.trans hA)
    have ha : 1 ≤ A / q := hq.trans ((Nat.le_div_iff_mul_le hq0).2 hq2A)
    have hB : 1 ≤ (A + Delta) / q :=
      ha.trans (Nat.div_le_div_right (Nat.le_add_right A Delta))
    have hBreal : (1 : ℝ) ≤ (((A + Delta) / q : ℕ) : ℝ) := by
      exact_mod_cast hB
    linarith [Real.log_nonneg hBreal]
  have hsum := sliceA2Exceptional_rankin_power_sum_le A1 epsc hlower
  have hexp :
      Real.exp (2 * ∑ p ∈ exceptionalPrimes A1 epsc,
          (p : ℝ) ^ (-(1 - s))) ≤
        Real.exp (6 * sliceA2ExceptionalMass 0 epsc) := by
    apply Real.exp_le_exp.mpr
    calc
      2 * ∑ p ∈ exceptionalPrimes A1 epsc,
            (p : ℝ) ^ (-(1 - s)) ≤
          2 * (3 * sliceA2ExceptionalMass A1 epsc) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [s] using hsum
        · norm_num
      _ = 6 * sliceA2ExceptionalMass 0 epsc := by
        simp [sliceA2ExceptionalMass]
        ring
  have hrpow := sliceA2Exceptional_rankin_rpow_le_decay
    A1 A q epsc hA14 hA hq hq4 hlog8
  have hmiddle :
      ((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^ (-s)) *
          Real.exp (2 * ∑ p ∈ exceptionalPrimes A1 epsc,
            (p : ℝ) ^ (-(1 - s))) ≤
        Real.exp (-(X ^ (1 / 50 : ℝ) /
            (16 * (exceptionalIntervalRatio epsc : ℝ)))) *
          Real.exp (6 * sliceA2ExceptionalMass 0 epsc) := by
    exact mul_le_mul hrpow hexp (by positivity) (by positivity)
  have htail :
      (Real.log (((A + Delta) / q : ℕ) : ℝ) + 1) *
          (((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^ (-s)) *
            Real.exp (2 * ∑ p ∈ exceptionalPrimes A1 epsc,
              (p : ℝ) ^ (-(1 - s)))) ≤
        (3 * X + 2) * Real.exp (6 * sliceA2ExceptionalMass 0 epsc) *
          Real.exp (-(X ^ (1 / 50 : ℝ) /
            (16 * (exceptionalIntervalRatio epsc : ℝ)))) := by
    calc
      _ ≤ (Real.log (((A + Delta) / q : ℕ) : ℝ) + 1) *
            (Real.exp (-(X ^ (1 / 50 : ℝ) /
                (16 * (exceptionalIntervalRatio epsc : ℝ)))) *
              Real.exp (6 * sliceA2ExceptionalMass 0 epsc)) :=
        mul_le_mul_of_nonneg_left hmiddle hlogFactor0
      _ ≤ (3 * X + 2) *
            (Real.exp (-(X ^ (1 / 50 : ℝ) /
                (16 * (exceptionalIntervalRatio epsc : ℝ)))) *
              Real.exp (6 * sliceA2ExceptionalMass 0 epsc)) := by
        apply mul_le_mul_of_nonneg_right hlogFactor
        positivity
      _ = _ := by ring
  have hscalar := hAS A1 hAS1
  dsimp only at hscalar
  simpa [q, s, X] using htail.trans hscalar

end Tao2015

end MoltResearch
