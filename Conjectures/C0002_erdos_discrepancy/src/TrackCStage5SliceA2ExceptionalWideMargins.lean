import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalMargins
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalDomination

/-!
# Track R A2-V': eventual wide exceptional margins

The exceptional interval ratio and cell resolution are fixed once the
accuracy data are fixed.  Endpoint subpolynomiality therefore pays the two
cardinality-over-window errors and the collar guard, while divergence of the
lower endpoint pays the reciprocal-square collision error.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- A fixed endpoint domination inequality pays a cardinality-over-window
term because the exceptional prime set has cardinality at most its upper
endpoint. -/
theorem exceptional_card_div_fit_of_upper_margin
    (A1 A : ℕ) (epsc coefficient target : ℝ)
    (hcoefficient : 0 ≤ coefficient) (htarget : 0 < target)
    (hA1 : 1 ≤ A1) (hA : A1 ≤ A)
    (hmargin : (coefficient / target) *
      (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A1) :
    coefficient * (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤ target := by
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < A1) hA
  have hcard : ((exceptionalPrimes A1 epsc).card : ℝ) ≤
      exceptionalPrimeUpper A1 epsc := by
    exact_mod_cast exceptionalPrimes_card_le_upper A1 epsc
  have hcore : coefficient *
      (exceptionalPrimeUpper A1 epsc : ℝ) ≤ target * A := by
    calc
      coefficient * (exceptionalPrimeUpper A1 epsc : ℝ) =
          target * ((coefficient / target) *
            (exceptionalPrimeUpper A1 epsc : ℝ)) := by field_simp
      _ ≤ target * (A1 : ℝ) :=
        mul_le_mul_of_nonneg_left hmargin htarget.le
      _ ≤ target * (A : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hA) htarget.le
  rw [show coefficient *
      (((exceptionalPrimes A1 epsc).card : ℝ) / A) =
        (coefficient * ((exceptionalPrimes A1 epsc).card : ℝ)) / A by ring]
  apply (div_le_iff₀ hApos).2
  exact (mul_le_mul_of_nonneg_left hcard hcoefficient).trans hcore

/-- All elementary scale conditions for the complete wide exceptional leg
hold uniformly throughout `[A1,A1^2]` beyond one base threshold. -/
theorem exists_sliceA2Exceptional_wide_margins
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 A : ℕ, A0 ≤ A1 → A1 ≤ A →
      exceptionalPrimeUpper A1 epsc ^ 2 ≤ A ∧
      sliceA2ExceptionalN A1 epsc eps rho0 *
          exceptionalPrimeUpper A1 epsc ≤ A ∧
      1152 * Real.exp Real.pi *
          (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
        eps ^ 2 * rho0 / 192 ∧
      320 * Real.exp Real.pi /
          (exceptionalPrimeLower A1 : ℝ) ≤ eps ^ 2 * rho0 / 192 ∧
      80 * Real.exp Real.pi *
          (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
        eps ^ 2 * rho0 / 192 := by
  let b : ℝ := eps ^ 2 * rho0 / 192
  have hb : 0 < b := by dsimp [b]; positivity
  let Crepl : ℝ := 1152 * Real.exp Real.pi / b
  let Ccoll : ℝ := 80 * Real.exp Real.pi / b
  let Cprime : ℝ := 320 * Real.exp Real.pi / b
  have hCrepl : 0 < Crepl := by dsimp [Crepl]; positivity
  have hCcoll : 0 < Ccoll := by dsimp [Ccoll]; positivity
  have hCprime : 0 < Cprime := by dsimp [Cprime]; positivity
  obtain ⟨Aq, hAq⟩ := exists_exceptionalPrimeUpper_sq_le epsc
  obtain ⟨An, hAn⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    (sliceA2ExceptionalN 0 epsc eps rho0 : ℝ) 1 epsc
    (by
      exact_mod_cast sliceA2ExceptionalN_pos 0 epsc eps rho0) (by norm_num)
  obtain ⟨Ar, hAr⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    Crepl 1 epsc hCrepl (by norm_num)
  obtain ⟨Ac, hAc⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    Ccoll 1 epsc hCcoll (by norm_num)
  obtain ⟨Ap, hAp⟩ := exists_exceptionalPrimeLower_ge Cprime
  let A0 := max 2 (max Aq (max An (max Ar (max Ac Ap))))
  refine ⟨A0, fun A1 A hA1 hA => ?_⟩
  have htwo : 2 ≤ A1 := (le_max_left _ _).trans hA1
  have hq := hAq A1 ((le_max_left Aq (max An (max Ar (max Ac Ap)))).trans
    ((le_max_right 2 _).trans hA1))
  have hn := hAn A1 ((le_max_left An (max Ar (max Ac Ap))).trans
    ((le_max_right Aq _).trans ((le_max_right 2 _).trans hA1)))
  have hr := hAr A1 ((le_max_left Ar (max Ac Ap)).trans
    ((le_max_right An _).trans ((le_max_right Aq _).trans
      ((le_max_right 2 _).trans hA1))))
  have hc := hAc A1 ((le_max_left Ac Ap).trans
    ((le_max_right Ar _).trans ((le_max_right An _).trans
      ((le_max_right Aq _).trans ((le_max_right 2 _).trans hA1)))))
  have hp := hAp A1 ((le_max_right Ac Ap).trans
    ((le_max_right Ar _).trans ((le_max_right An _).trans
      ((le_max_right Aq _).trans ((le_max_right 2 _).trans hA1)))))
  have hNfixed : sliceA2ExceptionalN A1 epsc eps rho0 =
      sliceA2ExceptionalN 0 epsc eps rho0 := by
    rfl
  have hnA1 : sliceA2ExceptionalN A1 epsc eps rho0 *
      exceptionalPrimeUpper A1 epsc ≤ A1 := by
    rw [hNfixed]
    norm_num only [pow_one] at hn
    exact_mod_cast hn
  have hrepl := exceptional_card_div_fit_of_upper_margin A1 A epsc
    (1152 * Real.exp Real.pi) b (by positivity) hb (by omega) hA (by
      simpa [Crepl] using hr)
  have hcoll := exceptional_card_div_fit_of_upper_margin A1 A epsc
    (80 * Real.exp Real.pi) b (by positivity) hb (by omega) hA (by
      simpa [Ccoll] using hc)
  have hPpos : (0 : ℝ) < exceptionalPrimeLower A1 := by
    exact_mod_cast (show 0 < exceptionalPrimeLower A1 by
      have := exceptionalPrimeLower_three_le A1
      omega)
  have hprime : 320 * Real.exp Real.pi /
      (exceptionalPrimeLower A1 : ℝ) ≤ b := by
    apply (div_le_iff₀ hPpos).2
    calc
      320 * Real.exp Real.pi = b * Cprime := by
        dsimp [Cprime]
        field_simp
      _ ≤ b * (exceptionalPrimeLower A1 : ℝ) :=
        mul_le_mul_of_nonneg_left hp hb.le
  refine ⟨hq.trans hA, hnA1.trans hA, ?_, ?_, ?_⟩
  · simpa [b] using hrepl
  · simpa [b] using hprime
  · simpa [b] using hcoll

end Tao2015

end MoltResearch
