import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalWideMargins

/-!
# Track R A2-V': exceptional integer polylog margin

Once the high-moment cover supplies
`Kcov * sqrt T * Q_U <= A`, the integer leg contains only three powers of
`log A` against the two hundred powers from the split threshold.  This leaf
records the exact constant and closes that remaining numerical estimate.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The fixed coefficient left after the cell count and logarithmic factor
are charged against `exceptionalSplitThreshold A ^ 2`. -/
noncomputable def sliceA2ExceptionalIntegerCoefficient
    (epsc eps rho0 : ℝ) : ℝ :=
  55296 *
    ((sliceA2ExceptionalN 0 epsc eps rho0 : ℝ) *
      (exceptionalIntervalRatio epsc : ℝ)) ^ 2

theorem exists_sliceA2_log_ge (C : ℝ) :
    ∃ A0 : ℕ, ∀ A : ℕ, A0 ≤ A → C ≤ Real.log (A : ℝ) := by
  refine ⟨⌈Real.exp C⌉₊ + 1, fun A hA => ?_⟩
  have hexp : Real.exp C ≤ (A : ℝ) := by
    calc
      Real.exp C ≤ (⌈Real.exp C⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (A : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hA)
  calc
    C = Real.log (Real.exp C) := (Real.log_exp C).symm
    _ ≤ Real.log (A : ℝ) := Real.log_le_log (Real.exp_pos C) hexp

/-- The residual `log(A)^(-197)` term eventually enters the integer
allocation. -/
theorem exists_sliceA2Exceptional_integer_polylog_margin
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A : ℕ, A0 ≤ A →
      sliceA2ExceptionalIntegerCoefficient epsc eps rho0 /
          Real.log (A : ℝ) ^ 197 ≤ eps ^ 2 * rho0 / 64 := by
  let b : ℝ := eps ^ 2 * rho0 / 64
  have hb : 0 < b := by dsimp [b]; positivity
  let C : ℝ := max 1 (sliceA2ExceptionalIntegerCoefficient epsc eps rho0 / b)
  obtain ⟨A0, hA0⟩ := exists_sliceA2_log_ge C
  refine ⟨A0, fun A hA => ?_⟩
  have hlog : C ≤ Real.log (A : ℝ) := hA0 A hA
  have hlog1 : 1 ≤ Real.log (A : ℝ) := (le_max_left _ _).trans hlog
  have hcoef : sliceA2ExceptionalIntegerCoefficient epsc eps rho0 / b ≤
      Real.log (A : ℝ) := (le_max_right _ _).trans hlog
  have hpow : Real.log (A : ℝ) ≤ Real.log (A : ℝ) ^ 197 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog1 (by norm_num : 1 ≤ 197)
  have hcross : sliceA2ExceptionalIntegerCoefficient epsc eps rho0 ≤
      b * Real.log (A : ℝ) ^ 197 := by
    calc
      sliceA2ExceptionalIntegerCoefficient epsc eps rho0 =
          b * (sliceA2ExceptionalIntegerCoefficient epsc eps rho0 / b) := by
        field_simp
      _ ≤ b * Real.log (A : ℝ) :=
        mul_le_mul_of_nonneg_left hcoef hb.le
      _ ≤ b * Real.log (A : ℝ) ^ 197 :=
        mul_le_mul_of_nonneg_left hpow hb.le
  have hden : 0 < Real.log (A : ℝ) ^ 197 := pow_pos (by linarith) _
  apply (div_le_iff₀ hden).2
  simpa [b, mul_comm] using hcross

/-- The literal scale inequality consumed by
`sliceA2Exceptional_integer_fit` follows from the cover-scale bound and the
fixed polylog margin. -/
theorem sliceA2Exceptional_integer_scale_fit
    (g : ℕ → ℂ) (P0 ratio0 eta J A1 A : ℕ)
    (epsc eps rho0 K1 K2 T : ℝ)
    (hA : 3 ≤ A) (hT : 1 ≤ T) (hTA : T ≤ A)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A)
    (hlogP : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hcoverScale :
      sliceA2ExceptionalCover g P0 ratio0 eta J A1 eps epsc rho0 K1 K2 *
          Real.sqrt T * (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A)
    (hpoly : sliceA2ExceptionalIntegerCoefficient epsc eps rho0 /
        Real.log (A : ℝ) ^ 197 ≤ eps ^ 2 * rho0 / 64) :
    1024 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) ^ 2 *
          exceptionalSplitThreshold A ^ 2 *
          sliceA2ExceptionalLogFactor T *
          (1 + sliceA2ExceptionalCover g P0 ratio0 eta J A1
              eps epsc rho0 K1 K2 * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ)) ≤
      eps ^ 2 * rho0 / 64 := by
  let N := sliceA2ExceptionalN A1 epsc eps rho0
  let R := exceptionalIntervalRatio epsc
  let I := sliceA2ExceptionalI A1 epsc eps rho0
  let Kcov := sliceA2ExceptionalCover g P0 ratio0 eta J A1
    eps epsc rho0 K1 K2
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlogA1 : 1 ≤ Real.log (A : ℝ) := by
    have : Real.exp 1 < 3 := Real.exp_one_lt_three
    apply (Real.le_log_iff_exp_le hApos).2
    exact this.le.trans (by exact_mod_cast hA)
  have hPQA : exceptionalPrimeLower A1 ≤ A :=
    (exceptionalPrimeLower_le_upper A1 epsc).trans <|
      (show exceptionalPrimeUpper A1 epsc ≤ A by
        have hQ1 : 1 ≤ exceptionalPrimeUpper A1 epsc := by
          have hthree := (exceptionalPrimeLower_three_le A1).trans
            (exceptionalPrimeLower_le_upper A1 epsc)
          omega
        have hQQ : exceptionalPrimeUpper A1 epsc ≤
            exceptionalPrimeUpper A1 epsc ^ 2 := by
          rw [pow_two]
          simpa only [mul_one] using Nat.mul_le_mul_left
            (exceptionalPrimeUpper A1 epsc) hQ1
        exact hQQ.trans hQsq)
  have hlogPA : Real.log (exceptionalPrimeLower A1 : ℝ) ≤
      Real.log (A : ℝ) := by
    exact Real.log_le_log (by
      exact_mod_cast (show 0 < exceptionalPrimeLower A1 by
        have := exceptionalPrimeLower_three_le A1
        omega))
      (by exact_mod_cast hPQA)
  have hcard : (I.card : ℝ) ≤
      3 * (N : ℝ) * (R : ℝ) * Real.log (A : ℝ) := by
    exact (sliceA2ExceptionalI_card_fixed A1 epsc eps rho0 hlogP).trans
      (mul_le_mul_of_nonneg_left hlogPA (by positivity))
  have hL : sliceA2ExceptionalLogFactor T ≤ 3 * Real.log (A : ℝ) := by
    have h2Tpos : (0 : ℝ) < 2 * T := by positivity
    have h2TA : 2 * T ≤ 2 * (A : ℝ) := by
      gcongr
    have hlogTA := Real.log_le_log h2Tpos h2TA
    have hlogtwo : Real.log 2 ≤ 1 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    have hlogmul : Real.log (2 * (A : ℝ)) =
        Real.log 2 + Real.log (A : ℝ) :=
      Real.log_mul (by norm_num) hApos.ne'
    unfold sliceA2ExceptionalLogFactor
    rw [hlogmul] at hlogTA
    linarith
  have hcover : 1 + Kcov * Real.sqrt T *
      (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ) ≤ 2 := by
    have hdiv : Kcov * Real.sqrt T *
        (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ) ≤ 1 := by
      apply (div_le_one hApos).2
      simpa [Kcov] using hcoverScale
    linarith
  have hcard0 : 0 ≤ (I.card : ℝ) := by positivity
  have hL0 : 0 ≤ sliceA2ExceptionalLogFactor T := by
    unfold sliceA2ExceptionalLogFactor
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)]
  have hcover0 : 0 ≤ 1 + Kcov * Real.sqrt T *
      (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ) := by
    dsimp [Kcov, sliceA2ExceptionalCover]
    positivity
  have hbound :
      1024 * (I.card : ℝ) ^ 2 * exceptionalSplitThreshold A ^ 2 *
          sliceA2ExceptionalLogFactor T *
          (1 + Kcov * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ)) ≤
        sliceA2ExceptionalIntegerCoefficient epsc eps rho0 /
          Real.log (A : ℝ) ^ 197 := by
    rw [exceptionalSplitThreshold_sq]
    have hlogpos : 0 < Real.log (A : ℝ) := by linarith
    calc
      _ ≤ 1024 *
          (3 * (N : ℝ) * (R : ℝ) * Real.log (A : ℝ)) ^ 2 *
          (1 / Real.log (A : ℝ) ^ 200) *
          (3 * Real.log (A : ℝ)) * 2 := by gcongr
      _ = sliceA2ExceptionalIntegerCoefficient epsc eps rho0 /
          Real.log (A : ℝ) ^ 197 := by
        have hNfixed : N = sliceA2ExceptionalN 0 epsc eps rho0 := by rfl
        rw [hNfixed]
        unfold sliceA2ExceptionalIntegerCoefficient
        field_simp
        ring
  simpa [I, Kcov] using hbound.trans hpoly

end Tao2015

end MoltResearch
