import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalRankinDecay

/-!
# Track R A2-V': exceptional Rankin tail

The quotient decay, logarithmic window factor, and tilted Euler product are
combined here.  The resulting tail is uniform over every exceptional cell
and every slice in the quadratic scale window.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The logarithmic factor at a cell quotient is bounded by the fixed
quadratic-window envelope. -/
theorem sliceA2Exceptional_quotient_log_factor_le
    (A1 A Delta q : ℕ) (hA1 : 1 ≤ A1) (hAupper : A ≤ A1 ^ 2)
    (hDelta : Delta ≤ A) :
    Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 ≤
      3 * Real.log (A1 : ℝ) + 2 := by
  let B := (A + Delta) / q
  have hBupper : B ≤ 2 * A1 ^ 2 := by
    calc
      B ≤ A + Delta := Nat.div_le_self _ _
      _ ≤ 2 * A := by omega
      _ ≤ 2 * A1 ^ 2 := Nat.mul_le_mul_left 2 hAupper
  have hX0 : 0 ≤ Real.log (A1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hA1)
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · simp [B, hB0]
    linarith
  · have hcast : (B : ℝ) ≤ 2 * (A1 : ℝ) ^ 2 := by
      exact_mod_cast hBupper
    have hlog : Real.log (B : ℝ) ≤
        Real.log (2 * (A1 : ℝ) ^ 2) :=
      Real.log_le_log (by exact_mod_cast hBpos) hcast
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_two_lt_d9]
    calc
      Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 ≤
          Real.log (2 * (A1 : ℝ) ^ 2) + 1 := by
        simpa [B] using add_le_add_right hlog 1
      _ = Real.log 2 + 2 * Real.log (A1 : ℝ) + 1 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      _ ≤ 3 * Real.log (A1 : ℝ) + 2 := by linarith

/-- Beyond one base threshold, the Rankin tail in `sharpRamareCost_le_eps`
fits inside its fixed exceptional allocation, uniformly over all cells and
all slices in the quadratic scale window. -/
theorem exists_sliceA2Exceptional_rankin_tail_le
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
            ∏ p ∈ exceptionalPrimes A1 epsc,
              (1 - (p : ℝ) ^
                (-(1 - sliceA2ExceptionalRankinS A1 epsc)))⁻¹) ≤
          sliceA2ExceptionalTailBudget epsc eps rho0 := by
  obtain ⟨AS, hAS⟩ :=
    exists_sliceA2Exceptional_rankin_scalar_margin epsc eps rho0 heps hrho0
  obtain ⟨AQ, hAQ⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    1 4 epsc (by norm_num) (by norm_num)
  obtain ⟨AL, hAL⟩ := exists_sliceA2_log_ge (8 * Real.log 8)
  obtain ⟨AP, hAP⟩ := exists_exceptionalPrimeLower_ge 6
  refine ⟨max 4 (max AS (max AQ (max AL AP))),
    fun A1 A Delta hA1 hA hAupper hDelta v => ?_⟩
  have hA14 : 4 ≤ A1 := (le_max_left _ _).trans hA1
  have hAS1 : AS ≤ A1 := by
    omega
  have hAQ1 : AQ ≤ A1 := by
    omega
  have hAL1 : AL ≤ A1 := by
    omega
  have hAP1 : AP ≤ A1 := by
    omega
  let q := sliceA2ExceptionalRepresentative A1 v epsc eps rho0
  let s := sliceA2ExceptionalRankinS A1 epsc
  let P := exceptionalPrimes A1 epsc
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
  have hs := sliceA2ExceptionalRankinS_pos_lt_one A1 epsc
  have hsum := sliceA2Exceptional_rankin_power_sum_le A1 epsc hlower
  have hprod :
      (∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹) ≤
        Real.exp (6 * sliceA2ExceptionalMass 0 epsc) := by
    calc
      (∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹) ≤
          Real.exp (2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 - s))) := by
        apply prod_inv_one_sub_le_exp
        · intro p hp
          positivity
        · intro p hp
          simpa [P, s] using
            sliceA2Exceptional_rankin_power_le_half A1 epsc hlower p hp
      _ ≤ Real.exp (6 * sliceA2ExceptionalMass A1 epsc) := by
        apply Real.exp_le_exp.mpr
        calc
          2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 - s)) ≤
              2 * (3 * sliceA2ExceptionalMass A1 epsc) := by
            apply mul_le_mul_of_nonneg_left
            · simpa [P, s] using hsum
            · norm_num
          _ = 6 * sliceA2ExceptionalMass A1 epsc := by ring
      _ = Real.exp (6 * sliceA2ExceptionalMass 0 epsc) := by rfl
  have hrpow := sliceA2Exceptional_rankin_rpow_le_decay
    A1 A q epsc hA14 hA hq hq4 hlog8
  have hrpow0 : 0 ≤
      ((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^ (-s)) := by
    positivity
  have hprod0 : 0 ≤
      ∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have hh := sliceA2Exceptional_rankin_power_le_half A1 epsc hlower p
      (by simpa [P] using hp)
    have : 0 < 1 - (p : ℝ) ^ (-(1 - s)) := by
      have hsimp : s = sliceA2ExceptionalRankinS A1 epsc := rfl
      rw [hsimp]
      linarith
    positivity
  have htail :
      (Real.log (((A + Delta) / q : ℕ) : ℝ) + 1) *
          (((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^ (-s)) *
            ∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹) ≤
        (3 * X + 2) *
          Real.exp (6 * sliceA2ExceptionalMass 0 epsc) *
          Real.exp (-(X ^ (1 / 50 : ℝ) /
            (16 * (exceptionalIntervalRatio epsc : ℝ)))) := by
    have hmiddle :
        ((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^ (-s)) *
            (∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹) ≤
          Real.exp (-(X ^ (1 / 50 : ℝ) /
              (16 * (exceptionalIntervalRatio epsc : ℝ)))) *
            Real.exp (6 * sliceA2ExceptionalMass 0 epsc) := by
      exact mul_le_mul hrpow hprod hprod0 (by positivity)
    calc
      (Real.log (((A + Delta) / q : ℕ) : ℝ) + 1) *
            (((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^ (-s)) *
              ∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹) ≤
          (Real.log (((A + Delta) / q : ℕ) : ℝ) + 1) *
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
      _ = (3 * X + 2) * Real.exp (6 * sliceA2ExceptionalMass 0 epsc) *
            Real.exp (-(X ^ (1 / 50 : ℝ) /
              (16 * (exceptionalIntervalRatio epsc : ℝ)))) := by ring
  have hscalar := hAS A1 hAS1
  dsimp only at hscalar
  simpa [q, s, P, X] using
    htail.trans hscalar

end Tao2015

end MoltResearch
