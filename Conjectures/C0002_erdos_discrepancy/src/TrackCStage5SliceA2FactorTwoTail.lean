import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalDeltaClose

/-!
# Track R A2-V': exceptional Rankin bounds on a doubled square window

The small-slice left endpoint may reach `2*A1^2`.  The extra factor two is
absorbed by one copy of `log A1`; all decay powers and fixed allocations are
unchanged.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The quotient logarithm has the same envelope on the doubled quadratic
window once `A1 >= 4`. -/
theorem sliceA2Exceptional_quotient_log_factor_le_two
    (A1 A Delta q : ℕ) (hA1 : 4 ≤ A1) (hAupper : A ≤ 2 * A1 ^ 2)
    (hDelta : Delta ≤ A) :
    Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 ≤
      3 * Real.log (A1 : ℝ) + 2 := by
  let B := (A + Delta) / q
  have hBupper : B ≤ 4 * A1 ^ 2 := by
    calc
      B ≤ A + Delta := Nat.div_le_self _ _
      _ ≤ 2 * A := by omega
      _ ≤ 4 * A1 ^ 2 := by nlinarith
  have hX1 : 1 ≤ Real.log (A1 : ℝ) := by
    have hfour : Real.exp 1 < 4 := Real.exp_one_lt_three.trans_le (by norm_num)
    apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < A1)).2
    exact hfour.le.trans (by exact_mod_cast hA1)
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · simp [B, hB0]
    linarith
  · have hcast : (B : ℝ) ≤ 4 * (A1 : ℝ) ^ 2 := by
      exact_mod_cast hBupper
    have hlog : Real.log (B : ℝ) ≤
        Real.log (4 * (A1 : ℝ) ^ 2) :=
      Real.log_le_log (by exact_mod_cast hBpos) hcast
    have hlog4 : Real.log 4 ≤ Real.log (A1 : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hA1)
    calc
      Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 ≤
          Real.log (4 * (A1 : ℝ) ^ 2) + 1 := by
        simpa [B] using add_le_add_right hlog 1
      _ = Real.log 4 + 2 * Real.log (A1 : ℝ) + 1 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      _ ≤ 3 * Real.log (A1 : ℝ) + 2 := by linarith

/-- The exponential Rankin tail keeps its fixed allocation throughout the
doubled quadratic window. -/
theorem exists_sliceA2Exceptional_rankin_exp_tail_le_two
    (Cp : ℝ)
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ 2 * A1 ^ 2 → Delta ≤ A →
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
  have hq4 : q ^ 4 ≤ A1 := (pow_le_pow_left' hqQ 4).trans hQ4
  have hlog8 : 8 * Real.log 8 ≤ X := by simpa [X] using hAL A1 hAL1
  have hlower : 6 ≤ exceptionalPrimeLower A1 := by exact_mod_cast hAP A1 hAP1
  have hlogFactor :
      Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 ≤ 3 * X + 2 := by
    simpa [X] using sliceA2Exceptional_quotient_log_factor_le_two
      A1 A Delta q hA14 hAupper hDelta
  have hlogFactor0 : 0 ≤ Real.log (((A + Delta) / q : ℕ) : ℝ) + 1 := by
    have hq0 : 0 < q := by omega
    have hq2q4 : q ^ 2 ≤ q ^ 4 := pow_le_pow_right' hq (by omega)
    have hq2A : q * q ≤ A := by
      simpa [pow_two] using hq2q4.trans (hq4.trans hA)
    have ha : 1 ≤ A / q := hq.trans ((Nat.le_div_iff_mul_le hq0).2 hq2A)
    have hB : 1 ≤ (A + Delta) / q :=
      ha.trans (Nat.div_le_div_right (Nat.le_add_right A Delta))
    have hBreal : (1 : ℝ) ≤ (((A + Delta) / q : ℕ) : ℝ) := by exact_mod_cast hB
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
          Real.exp (6 * sliceA2ExceptionalMass 0 epsc) :=
    mul_le_mul hrpow hexp (by positivity) (by positivity)
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

/-- The fixed sharp-cell envelope is unchanged on the doubled window. -/
theorem exists_sliceA2Exceptional_sharp_bound_two
    (Cp : ℝ)
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ (D : ℝ) (A0 : ℕ), 1 ≤ D ∧
      ∀ A1 A Delta : ℕ,
        A0 ≤ A1 → A1 ≤ A → A ≤ 2 * A1 ^ 2 → Delta ≤ A →
        ∀ v : ℕ, ∀ base : Finset ℕ,
          cellHalaszSharpBound
              (exceptionalSharpCutoff A) D
              (exceptionalDelta0
                (sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0))
              (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
              ((A + Delta) /
                sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
              (exceptionalPrimes A1 epsc) [base] ≤
            2 * (2 * sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 *
              Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) +
                sliceA2ExceptionalTailBudget Cp epsc eps rho0) := by
  let ep := sliceA2ExceptionalEpsilonPrime Cp 0 epsc eps rho0
  have hep : 0 < ep := by
    dsimp [ep]
    exact sliceA2ExceptionalEpsilonPrime_pos Cp 0 epsc eps rho0 heps hrho0
  obtain ⟨D0, xMin, hD0, hxMin, hsharp⟩ :=
    cellHalaszSharpBound_le_fixedEnvelope ep hep
  obtain ⟨AT, hAT⟩ :=
    exists_sliceA2Exceptional_rankin_exp_tail_le_two Cp epsc eps rho0 heps hrho0
  obtain ⟨AP, hAP⟩ := exists_exceptionalPrimeLower_ge 6
  obtain ⟨AQ, hAQ⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    1 4 epsc (by norm_num) (by norm_num)
  refine ⟨D0, max 4 (max AT (max AP (max AQ (xMin ^ 2)))), hD0,
    fun A1 A Delta hA1 hA hAupper hDelta v base => ?_⟩
  have hAT1 : AT ≤ A1 := by omega
  have hAP1 : AP ≤ A1 := by omega
  have hAQ1 : AQ ≤ A1 := by omega
  have hxMinSq : xMin ^ 2 ≤ A := by omega
  have hxMinCutoff : xMin ≤ exceptionalSharpCutoff A := by
    have hx0 : (0 : ℝ) ≤ xMin := by positivity
    have hrad0 : (0 : ℝ) ≤ 3 * (2 * (A : ℝ) + 1) := by positivity
    have hsq : (xMin : ℝ) ^ 2 ≤ 3 * (2 * (A : ℝ) + 1) := by
      have hcast : (xMin : ℝ) ^ 2 ≤ A := by exact_mod_cast hxMinSq
      nlinarith
    have hsqrt : (xMin : ℝ) ≤ Real.sqrt (3 * (2 * (A : ℝ) + 1)) :=
      (Real.le_sqrt hx0 hrad0).2 hsq
    exact_mod_cast hsqrt.trans (exceptionalSharpCutoff_real_lower A)
  let q := sliceA2ExceptionalRepresentative A1 v epsc eps rho0
  let Aq := A / q
  let Bq := (A + Delta) / q
  let s := sliceA2ExceptionalRankinS A1 epsc
  let R : ℝ := exceptionalIntervalRatio epsc
  have hq : 1 ≤ q := by
    dsimp [q]
    exact (sliceA2Exceptional_cell_data A1 epsc eps rho0).2.2.1 v
  have hqQ : q ≤ exceptionalPrimeUpper A1 epsc := by
    dsimp [q]
    exact sliceA2ExceptionalRepresentative_le_upper A1 v epsc eps rho0
  have hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A := by
    have hQ4 : exceptionalPrimeUpper A1 epsc ^ 4 ≤ A1 := by
      have hQ4real : (exceptionalPrimeUpper A1 epsc : ℝ) ^ 4 ≤ A1 := by
        simpa using hAQ A1 hAQ1
      exact_mod_cast hQ4real
    have hQ2Q4 : exceptionalPrimeUpper A1 epsc ^ 2 ≤
        exceptionalPrimeUpper A1 epsc ^ 4 :=
      pow_le_pow_right' (by
        have hQ3 := (exceptionalPrimeLower_three_le A1).trans
          (exceptionalPrimeLower_le_upper A1 epsc)
        omega) (by omega)
    exact hQ2Q4.trans (hQ4.trans hA)
  have hAq : 1 ≤ Aq := by
    dsimp [Aq, q]
    exact sliceA2ExceptionalRepresentative_quotient_one_le
      A1 A v epsc eps rho0 hQsq
  have hAB : Aq ≤ Bq := by
    dsimp [Aq, Bq]
    exact Nat.div_le_div_right (Nat.le_add_right A Delta)
  have hB : Bq ≤ 2 * Aq + 1 := by
    dsimp [Aq, Bq]
    exact div_le_two_mul_div_add_one A (A + Delta) q (by omega) (by omega)
  have hs := sliceA2ExceptionalRankinS_pos_lt_one A1 epsc
  have hlower : 6 ≤ exceptionalPrimeLower A1 := by exact_mod_cast hAP A1 hAP1
  have hhalf : ∀ p ∈ exceptionalPrimes A1 epsc,
      (p : ℝ) ^ (-(1 - s)) ≤ 1 / 2 := by
    intro p hp
    simpa [s] using sliceA2Exceptional_rankin_power_le_half A1 epsc hlower p hp
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hmass : ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p ≤
      Real.log R + 12 := by
    simpa [R] using exceptionalPrimes_mass_le_log_ratio A1 epsc
  have hsq : ∑ p ∈ exceptionalPrimes A1 epsc,
      ((1 : ℝ) / p) ^ 2 ≤ 1 / 2 := by
    calc
      ∑ p ∈ exceptionalPrimes A1 epsc, ((1 : ℝ) / p) ^ 2 =
          ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ 2 / (exceptionalPrimeLower A1 : ℝ) :=
        exceptionalPrimes_sq_mass_le_two_div A1 epsc
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < exceptionalPrimeLower A1)]
        have hP4 : (4 : ℝ) ≤ exceptionalPrimeLower A1 := by
          exact_mod_cast (show 4 ≤ exceptionalPrimeLower A1 by omega)
        norm_num
        linarith
  have htail := hAT A1 A Delta hAT1 hA hAupper hDelta v
  have hresult := hsharp D0 le_rfl (exceptionalSharpCutoff A) hxMinCutoff
    Aq Bq hAq hAB hB (exceptionalPrimes A1 epsc)
    (fun p hp => exceptionalPrimes_prime A1 epsc p hp)
    s hs.1 hs.2 hhalf base R (sliceA2ExceptionalTailBudget Cp epsc eps rho0)
    hR hmass hsq (by simpa [Aq, Bq, q, s] using htail)
  simpa [ep, exceptionalDelta0, Aq, Bq, q, s, R,
    sliceA2ExceptionalEpsilonPrime_eq_zero Cp A1 epsc eps rho0] using hresult

/-- The exceptional Delta envelope is uniform on the doubled window. -/
theorem exists_sliceA2Exceptional_delta_bound_two
    (Cp : ℝ)
    (P0 ratio0 : ℕ) (lowBudget epsc eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hlow : 0 < lowBudget) (hepsc : 0 < epsc)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ (D : ℝ) (A0 : ℕ), 1 ≤ D ∧
      ∀ A1 A Delta : ℕ,
        A0 ≤ A1 → A1 ≤ A → A ≤ 2 * A1 ^ 2 → Delta ≤ A →
        ∀ v : ℕ,
          let eta := sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0
          let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
          let tail := sliceA2ExceptionalTailBudget Cp epsc eps rho0
          let rem := sliceA2ExceptionalLadderBudget Cp lowBudget epsc eps rho0 / 4
          cellHalaszSharpBound
                (exceptionalSharpCutoff A) D
                (exceptionalDelta0
                  (sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0))
                (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                ((A + Delta) /
                  sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                (exceptionalPrimes A1 epsc)
                [sliceA2LadderPrimes P0 ratio0 eta 0] +
              ladderSiftedLogMass
                (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                ((A + Delta) /
                  sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                ((List.range (J - 1)).map
                  (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
            sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem := by
  let budget := sliceA2ExceptionalLadderBudget Cp lowBudget epsc eps rho0
  let eta := sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0
  have hbudget : 0 < budget := by
    simpa [budget] using sliceA2ExceptionalLadderBudget_pos
      Cp lowBudget epsc eps rho0 hlow heps hrho0
  have heta : 1 ≤ eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_one_le
      Cp lowBudget epsc eps rho0
  have hetaBrun : 64 * Real.exp 12 ≤ budget * eta := by
    simpa [budget, eta] using sliceA2ExceptionalLadderEta_brun_budget
      Cp lowBudget epsc eps rho0 hlow hepsc heps hrho0
  obtain ⟨D, AS, hD, hsharp⟩ :=
    exists_sliceA2Exceptional_sharp_bound_two Cp epsc eps rho0 heps hrho0
  obtain ⟨AB, hbrun⟩ :=
    exists_sliceA2PositiveLadder_exceptional_remainder_le_quarter
      P0 ratio0 eta epsc eps rho0 budget hP0 heta hbudget hetaBrun
  refine ⟨D, max AS AB, hD,
    fun A1 A Delta hA1 hA hAupper hDelta v => ?_⟩
  have hAS1 : AS ≤ A1 := by omega
  have hAB1 : AB ≤ A1 := by omega
  let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
  let tail := sliceA2ExceptionalTailBudget Cp epsc eps rho0
  let rem := budget / 4
  have hs := hsharp A1 A Delta hAS1 hA hAupper hDelta v
    (sliceA2LadderPrimes P0 ratio0 eta 0)
  have hb := hbrun A1 A Delta hAB1 hA hDelta v
  have hdelta := sliceA2Exceptional_delta_bound_of_sharp_remainder
    Cp A1 epsc eps rho0 tail rem
    (cellHalaszSharpBound
      (exceptionalSharpCutoff A) D
      (exceptionalDelta0
        (sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0))
      (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      ((A + Delta) / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      (exceptionalPrimes A1 epsc)
      [sliceA2LadderPrimes P0 ratio0 eta 0])
    (ladderSiftedLogMass
      (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      ((A + Delta) / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      ((List.range (J - 1)).map
        (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1)))) hs
    (by simpa [rem, budget, J] using hb)
  simpa [eta, budget, J, tail, rem] using hdelta

end Tao2015

end MoltResearch
