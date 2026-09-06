import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalRankinExpTail

/-!
# Track R A2-V': exceptional sharp bound

This leaf sharpens the elementary Mertens envelope from `log (R+1)` to
`log R` and instantiates the sharp Ramaré interface at the canonical
square-root cutoff.  Its conclusion is the fixed cell envelope used by the
exceptional aggregate.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The prime mass on `(P,P^R]` has the exact logarithmic ratio envelope
needed by the fixed sharp-cell constant. -/
theorem prime_power_Ioc_mass_upper_sharp
    (P R : ℕ) (hP : 3 ≤ P) (hR : 1 ≤ R) :
    ∑ p ∈ (Ioc P (P ^ R)).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (R : ℝ) + 12 := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPaddpos : (0 : ℝ) < P + 1 := by positivity
  have hlogPadd : 0 < Real.log ((P : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < P + 1 by omega))
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hPle : P ≤ P ^ R := Nat.le_pow (by omega)
  have hnat : P ^ R + 1 ≤ (P + 1) ^ R := by
    exact Nat.succ_le_iff.mpr (Nat.pow_lt_pow_left (by omega) (by omega))
  have hlog0 :
      Real.log (((P ^ R : ℕ) : ℝ) + 1) ≤
        (R : ℝ) * Real.log ((P : ℝ) + 1) := by
    calc
      Real.log (((P ^ R : ℕ) : ℝ) + 1) ≤
          Real.log ((((P + 1) ^ R : ℕ) : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hnat
      _ = (R : ℝ) * Real.log ((P : ℝ) + 1) := by
        rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow]
  have hloglog :
      Real.log (Real.log (((P ^ R : ℕ) : ℝ) + 1)) ≤
        Real.log ((R : ℝ) * Real.log ((P : ℝ) + 1)) := by
    apply Real.log_le_log
    · exact Real.log_pos (by
        have hpPow : (0 : ℝ) < ((P ^ R : ℕ) : ℝ) := by
          exact_mod_cast (pow_pos (show 0 < P by omega) R)
        linarith)
    · exact hlog0
  have hmertens := prime_Ioc_mass_upper_mertens P (P ^ R) hP hPle
  rw [Real.log_mul hRpos.ne' hlogPadd.ne'] at hloglog
  linarith

theorem exceptionalPrimes_mass_le_log_ratio
    (A1 : ℕ) (epsc : ℝ) :
    ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p ≤
      Real.log (exceptionalIntervalRatio epsc : ℝ) + 12 := by
  simpa [exceptionalPrimes, exceptionalPrimeUpper] using
    prime_power_Ioc_mass_upper_sharp
      (exceptionalPrimeLower A1) (exceptionalIntervalRatio epsc)
      (exceptionalPrimeLower_three_le A1)
      (by have := exceptionalIntervalRatio_three_le epsc; omega)

/-- At all sufficiently large base scales, every exceptional quotient obeys
the fixed sharp-cell envelope at the canonical cutoff and sharpness. -/
theorem exists_sliceA2Exceptional_sharp_bound
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ (D : ℝ) (A0 : ℕ), 1 ≤ D ∧
      ∀ A1 A Delta : ℕ,
        A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 → Delta ≤ A →
        ∀ v : ℕ, ∀ base : Finset ℕ,
          cellHalaszSharpBound
              (exceptionalSharpCutoff A) D
              (exceptionalDelta0
                (sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0))
              (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
              ((A + Delta) /
                sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
              (exceptionalPrimes A1 epsc) [base] ≤
            2 * (2 * sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 *
              Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) +
                sliceA2ExceptionalTailBudget epsc eps rho0) := by
  let ep := sliceA2ExceptionalEpsilonPrime 0 epsc eps rho0
  have hep : 0 < ep := by
    dsimp [ep]
    exact sliceA2ExceptionalEpsilonPrime_pos 0 epsc eps rho0 heps hrho0
  obtain ⟨D0, xMin, hD0, hxMin, hsharp⟩ :=
    cellHalaszSharpBound_le_fixedEnvelope ep hep
  obtain ⟨AT, hAT⟩ :=
    exists_sliceA2Exceptional_rankin_exp_tail_le epsc eps rho0 heps hrho0
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
    have hsqrt : (xMin : ℝ) ≤
        Real.sqrt (3 * (2 * (A : ℝ) + 1)) :=
      (Real.le_sqrt hx0 hrad0).2 hsq
    have hceil : (xMin : ℝ) ≤ exceptionalSharpCutoff A :=
      hsqrt.trans (exceptionalSharpCutoff_real_lower A)
    exact_mod_cast hceil
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
  have hlower : 6 ≤ exceptionalPrimeLower A1 := by
    exact_mod_cast hAP A1 hAP1
  have hhalf : ∀ p ∈ exceptionalPrimes A1 epsc,
      (p : ℝ) ^ (-(1 - s)) ≤ 1 / 2 := by
    intro p hp
    simpa [s] using
      sliceA2Exceptional_rankin_power_le_half A1 epsc hlower p hp
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
    s hs.1 hs.2 hhalf base R (sliceA2ExceptionalTailBudget epsc eps rho0)
    hR hmass hsq (by simpa [Aq, Bq, q, s] using htail)
  simpa [ep, exceptionalDelta0, Aq, Bq, q, s, R,
    sliceA2ExceptionalEpsilonPrime_eq_zero A1 epsc eps rho0] using hresult

end Tao2015

end MoltResearch
