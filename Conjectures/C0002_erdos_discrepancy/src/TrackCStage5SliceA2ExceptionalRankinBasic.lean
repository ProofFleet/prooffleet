import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalBrunClose

/-!
# Track R A2-V': exceptional Rankin parameters

This leaf fixes `s = 1 / log Q_U`, bounds the tilted reciprocal-prime mass
by the ordinary Mertens envelope, and records the square-root cutoff loss.
-/

namespace MoltResearch

namespace Tao2015

open Finset

noncomputable def sliceA2ExceptionalRankinS (A1 : ℕ) (epsc : ℝ) : ℝ :=
  1 / Real.log (exceptionalPrimeUpper A1 epsc : ℝ)

noncomputable def sliceA2ExceptionalTailBudget
    (epsc eps rho0 : ℝ) : ℝ :=
  sliceA2ExceptionalEpsilonPrime 0 epsc eps rho0 * Real.exp 13 *
    (exceptionalIntervalRatio epsc : ℝ)

theorem sliceA2ExceptionalEpsilonPrime_eq_zero
    (A1 : ℕ) (epsc eps rho0 : ℝ) :
    sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 =
      sliceA2ExceptionalEpsilonPrime 0 epsc eps rho0 := by
  rfl

theorem sliceA2ExceptionalTailBudget_pos
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2ExceptionalTailBudget epsc eps rho0 := by
  unfold sliceA2ExceptionalTailBudget
  have hp := sliceA2ExceptionalEpsilonPrime_pos 0 epsc eps rho0 heps hrho0
  have hR : (0 : ℝ) < exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  positivity

theorem sliceA2ExceptionalRankinS_pos_lt_one
    (A1 : ℕ) (epsc : ℝ) :
    0 < sliceA2ExceptionalRankinS A1 epsc ∧
      sliceA2ExceptionalRankinS A1 epsc < 1 := by
  have hQ3 : 3 ≤ exceptionalPrimeUpper A1 epsc :=
    (exceptionalPrimeLower_three_le A1).trans
      (exceptionalPrimeLower_le_upper A1 epsc)
  have hQpos : (0 : ℝ) < exceptionalPrimeUpper A1 epsc := by positivity
  have hlogQ1 : 1 < Real.log (exceptionalPrimeUpper A1 epsc : ℝ) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      _ ≤ Real.log (exceptionalPrimeUpper A1 epsc : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hQ3)
  unfold sliceA2ExceptionalRankinS
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    exact hlogQ1

/-- The Rankin-tilted reciprocal-prime mass costs at most the fixed factor
three over the ordinary exceptional Mertens mass. -/
theorem sliceA2Exceptional_rankin_power_sum_le
    (A1 : ℕ) (epsc : ℝ) (hlower : 6 ≤ exceptionalPrimeLower A1) :
    ∑ p ∈ exceptionalPrimes A1 epsc,
        (p : ℝ) ^ (-(1 - sliceA2ExceptionalRankinS A1 epsc)) ≤
      3 * sliceA2ExceptionalMass A1 epsc := by
  let Q := exceptionalPrimeUpper A1 epsc
  let s := sliceA2ExceptionalRankinS A1 epsc
  have hQ3 : 3 ≤ Q := (exceptionalPrimeLower_three_le A1).trans
    (exceptionalPrimeLower_le_upper A1 epsc)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hs : s = 1 / Real.log (Q : ℝ) := by rfl
  have hterm : ∀ p ∈ exceptionalPrimes A1 epsc,
      (p : ℝ) ^ (-(1 - s)) ≤ 3 * ((1 : ℝ) / p) := by
    intro p hp
    have hpBounds := exceptionalPrimes_bounds A1 epsc p hp
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (show 0 < p by omega)
    have hpQ : (p : ℝ) ≤ Q := by exact_mod_cast hpBounds.2
    have hlogpQ : Real.log (p : ℝ) ≤ Real.log (Q : ℝ) :=
      Real.log_le_log hp0 hpQ
    have hps : (p : ℝ) ^ s ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hp0]
      apply Real.exp_le_exp.mpr
      rw [hs]
      simpa [div_eq_mul_inv] using (div_le_one hlogQ).2 hlogpQ
    have hps3 : (p : ℝ) ^ s ≤ 3 := hps.trans Real.exp_one_lt_three.le
    rw [show -(1 - s) = s - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
    calc
      (p : ℝ) ^ s / p ≤ 3 / p := div_le_div_of_nonneg_right hps3 hp0.le
      _ = 3 * ((1 : ℝ) / p) := by ring
  calc
    ∑ p ∈ exceptionalPrimes A1 epsc, (p : ℝ) ^ (-(1 - s)) ≤
        ∑ p ∈ exceptionalPrimes A1 epsc, 3 * ((1 : ℝ) / p) :=
      Finset.sum_le_sum hterm
    _ = 3 * ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p := by
      rw [Finset.mul_sum]
    _ ≤ 3 * sliceA2ExceptionalMass A1 epsc :=
      mul_le_mul_of_nonneg_left
        (exceptionalPrimes_mass_le_sliceA2ExceptionalMass A1 epsc) (by norm_num)

theorem sliceA2Exceptional_rankin_power_le_half
    (A1 : ℕ) (epsc : ℝ) (hlower : 6 ≤ exceptionalPrimeLower A1)
    (p : ℕ) (hp : p ∈ exceptionalPrimes A1 epsc) :
    (p : ℝ) ^ (-(1 - sliceA2ExceptionalRankinS A1 epsc)) ≤ 1 / 2 := by
  let s := sliceA2ExceptionalRankinS A1 epsc
  have hpLower := (exceptionalPrimes_bounds A1 epsc p hp).1
  have hp7 : 7 ≤ p := by omega
  have hp7r : (7 : ℝ) ≤ p := by exact_mod_cast hp7
  have hQ3 : 3 ≤ exceptionalPrimeUpper A1 epsc :=
    (exceptionalPrimeLower_three_le A1).trans
      (exceptionalPrimeLower_le_upper A1 epsc)
  have hlogQ : 0 < Real.log (exceptionalPrimeUpper A1 epsc : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < exceptionalPrimeUpper A1 epsc by omega))
  have hp0 : (0 : ℝ) < p := by positivity
  have hpQ : (p : ℝ) ≤ exceptionalPrimeUpper A1 epsc := by
    exact_mod_cast (exceptionalPrimes_bounds A1 epsc p hp).2
  have hps : (p : ℝ) ^ s ≤ 3 := by
    rw [Real.rpow_def_of_pos hp0]
    apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
    unfold s sliceA2ExceptionalRankinS
    simpa [div_eq_mul_inv] using
      (div_le_one hlogQ).2 (Real.log_le_log hp0 hpQ)
  rw [show -(1 - s) = s - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
  calc
    (p : ℝ) ^ s / p ≤ 3 / p := div_le_div_of_nonneg_right hps hp0.le
    _ ≤ 3 / 7 := by gcongr
    _ ≤ 1 / 2 := by norm_num

/-- The canonical square-root cutoff loses at most `log 4 + (log A)/2`. -/
theorem exceptionalSharpCutoff_log_le
    (A : ℕ) (hA : 1 ≤ A) :
    Real.log (exceptionalSharpCutoff A : ℝ) ≤
      Real.log 4 + Real.log (A : ℝ) / 2 := by
  let z : ℝ := 3 * (2 * (A : ℝ) + 1)
  let x0 := exceptionalSharpCutoff A
  have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hsqrtA1 : 1 ≤ Real.sqrt (A : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hAreal
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hzA : z ≤ 9 * (A : ℝ) := by dsimp [z]; nlinarith
  have hsqrtz0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg _
  have hsqrtA0 : 0 ≤ Real.sqrt (A : ℝ) := Real.sqrt_nonneg _
  have hsqrtz : Real.sqrt z ≤ 3 * Real.sqrt (A : ℝ) := by
    have hzsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz0
    have hAsq : (Real.sqrt (A : ℝ)) ^ 2 = A := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt z - 3 * Real.sqrt (A : ℝ))]
  have hx0 : (x0 : ℝ) ≤ 4 * Real.sqrt (A : ℝ) := by
    have hceil : (x0 : ℝ) < Real.sqrt z + 1 := by
      simpa [x0, exceptionalSharpCutoff, z] using Nat.ceil_lt_add_one hsqrtz0
    linarith
  have hx0pos : (0 : ℝ) < x0 := by
    have hlower := exceptionalSharpCutoff_real_lower A
    have : (0 : ℝ) < Real.sqrt (3 * (2 * (A : ℝ) + 1)) := by positivity
    exact this.trans_le (by simpa [x0] using hlower)
  calc
    Real.log (x0 : ℝ) ≤ Real.log (4 * Real.sqrt (A : ℝ)) :=
      Real.log_le_log hx0pos hx0
    _ = Real.log 4 + Real.log (A : ℝ) / 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity)]

end Tao2015

end MoltResearch
