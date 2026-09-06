import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2FinalDensity

/-!
# Track R A2-V'-20: reciprocal-prime mass in power intervals

Both the bottom and exceptional levels have the form `(P, P^R]`.  The
in-tree lower Mertens estimate gives a common explicit lower bound
`log R - log 2 - 12`; the factor two is only the harmless replacement of
`log(P+1)` by `2 log P`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Reciprocal-prime mass in a natural power interval. -/
theorem prime_power_Ioc_mass_lower
    (P R : ℕ) (hP : 3 ≤ P) (hR : 2 ≤ R) :
    Real.log (R : ℝ) - Real.log 2 - 12 ≤
      ∑ p ∈ (Ioc P (P ^ R)).filter Nat.Prime, (1 : ℝ) / p := by
  have hPone : 1 < P := by omega
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hPone)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hPle : P ≤ P ^ R := Nat.le_pow (by omega)
  have hnum0 :
      (R : ℝ) * Real.log (P : ℝ) ≤
        Real.log ((P ^ R : ℕ) + 1) := by
    calc
      (R : ℝ) * Real.log (P : ℝ) =
          Real.log ((P : ℝ) ^ R) := (Real.log_pow P R).symm
      _ ≤ Real.log (((P ^ R : ℕ) : ℝ) + 1) := by
        rw [Nat.cast_pow]
        apply Real.log_le_log (pow_pos hPpos R)
        linarith [pow_pos hPpos R]
      _ = Real.log ((P ^ R : ℕ) + 1) := by norm_num
  have hnum :
      Real.log ((R : ℝ) * Real.log (P : ℝ)) ≤
        Real.log (Real.log ((P ^ R : ℕ) + 1)) := by
    apply Real.log_le_log (mul_pos hRpos hlogP)
    exact hnum0
  have hPadd : P + 1 ≤ P ^ 2 := by nlinarith
  have hden0 :
      Real.log ((P : ℝ) + 1) ≤ 2 * Real.log (P : ℝ) := by
    calc
      Real.log ((P : ℝ) + 1) ≤ Real.log ((P : ℝ) ^ 2) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hPadd
      _ = 2 * Real.log (P : ℝ) := by rw [Real.log_pow]; norm_num
  have hden :
      Real.log (Real.log ((P : ℝ) + 1)) ≤
        Real.log (2 * Real.log (P : ℝ)) := by
    apply Real.log_le_log
    · exact Real.log_pos (by exact_mod_cast (show 1 < P + 1 by omega))
    · exact hden0
  have hmain :
      Real.log (R : ℝ) - Real.log 2 ≤
        Real.log (Real.log ((P ^ R : ℕ) + 1)) -
          Real.log (Real.log ((P : ℝ) + 1)) := by
    rw [Real.log_mul hRpos.ne' hlogP.ne'] at hnum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogP.ne'] at hden
    linarith
  exact (sub_le_sub_right hmain 12).trans
    (prime_Ioc_mass_lower_mertens P (P ^ R) hP hPle)

/-- The chosen exceptional ratio has logarithm at least `4/epsc + 13`. -/
theorem exceptionalIntervalRatio_log_lower
    (epsc : ℝ) :
    4 / epsc + 13 ≤ Real.log (exceptionalIntervalRatio epsc : ℝ) := by
  have hRpos : (0 : ℝ) < exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  calc
    4 / epsc + 13 = Real.log (Real.exp (4 / epsc + 13)) :=
      (Real.log_exp _).symm
    _ ≤ Real.log (exceptionalIntervalRatio epsc : ℝ) := by
      apply Real.log_le_log (Real.exp_pos _)
      calc
        Real.exp (4 / epsc + 13) ≤
            (⌈Real.exp (4 / epsc + 13)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (exceptionalIntervalRatio epsc : ℝ) := by
          exact_mod_cast (le_max_right 3 ⌈Real.exp (4 / epsc + 13)⌉₊)

/-- The exceptional prime level has the fixed mass required by its density
and sharp-envelope estimates. -/
theorem exceptionalPrimes_mass_ge_four_div
    (A1 : ℕ) (epsc : ℝ) :
    4 / epsc ≤ ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p := by
  let R := exceptionalIntervalRatio epsc
  have hmass := prime_power_Ioc_mass_lower
    (exceptionalPrimeLower A1) R
    (exceptionalPrimeLower_three_le A1)
    (by have := exceptionalIntervalRatio_three_le epsc; omega)
  have hlog := exceptionalIntervalRatio_log_lower epsc
  unfold exceptionalPrimes exceptionalPrimeUpper
  dsimp [R] at hmass ⊢
  linarith [Real.log_two_lt_d9]

/-- Taking the bottom ratio equal to the exceptional ratio gives the same
`4/epsc` reciprocal-prime mass at level zero. -/
theorem sliceA2BottomPrimes_mass_ge_four_div
    (P0 eta : ℕ) (epsc : ℝ) (hP0 : 3 ≤ P0) :
    4 / epsc ≤
      ∑ p ∈ sliceA2LadderPrimes P0
          (exceptionalIntervalRatio epsc) eta 0,
        (1 : ℝ) / p := by
  have hR : max 2 (exceptionalIntervalRatio epsc) =
      exceptionalIntervalRatio epsc :=
    max_eq_right (by have := exceptionalIntervalRatio_three_le epsc; omega)
  have hmass := prime_power_Ioc_mass_lower P0
    (exceptionalIntervalRatio epsc) hP0
    (by have := exceptionalIntervalRatio_three_le epsc; omega)
  have hlog := exceptionalIntervalRatio_log_lower epsc
  have hfinal : 4 / epsc ≤
      ∑ p ∈ (Ioc P0 (P0 ^ exceptionalIntervalRatio epsc)).filter Nat.Prime,
        (1 : ℝ) / p := by
    linarith [Real.log_two_lt_d9]
  simpa [sliceA2LadderPrimes, sliceA2LadderQ, sliceA2LadderP,
    sliceA2LadderRatio, hR] using hfinal

end Tao2015

end MoltResearch
