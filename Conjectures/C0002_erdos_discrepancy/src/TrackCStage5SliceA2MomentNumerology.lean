import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentClose

/-!
# Track R A2-V': exceptional moment numerology

This leaf records the scale inequalities behind the exceptional damping
certificate.  The adaptive order is no larger than its defining logarithmic
ratio plus two, while every remote anchor retains half of the
`(log A1)^(49/50)` lower-endpoint logarithm.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The ceiling in the adaptive prime moment costs less than two. -/
theorem adaptivePrimeMoment_cast_lt_log_ratio_add_two
    (P : ℕ) (T : ℝ) (hP : 2 ≤ P) (hT : 1 ≤ T) :
    (adaptivePrimeMoment P T : ℝ) <
      Real.log (2 * T) / Real.log (P : ℝ) + 2 := by
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlogT : 0 ≤ Real.log (2 * T) :=
    Real.log_nonneg (by linarith)
  have hratio : 0 ≤ Real.log (2 * T) / Real.log (P : ℝ) := by positivity
  have hceil := Nat.ceil_lt_add_one hratio
  unfold adaptivePrimeMoment
  push_cast
  linarith

/-- The defining exponential is below the integral exceptional lower
endpoint, so no logarithmic loss is incurred by its ceiling. -/
theorem exceptionalScaleLog_le_primeLower_log (A1 : ℕ) :
    (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ) ≤
      Real.log (exceptionalPrimeLower A1 : ℝ) := by
  let x := (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)
  have hexp : Real.exp x ≤ (exceptionalPrimeLower A1 : ℝ) := by
    calc
      Real.exp x ≤ (⌈Real.exp x⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (exceptionalPrimeLower A1 : ℝ) := by
        exact_mod_cast (le_max_right 3 ⌈Real.exp x⌉₊)
  have hPpos : (0 : ℝ) < exceptionalPrimeLower A1 := by
    exact_mod_cast (show 0 < exceptionalPrimeLower A1 by
      have := exceptionalPrimeLower_three_le A1
      omega)
  calc
    (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ) =
        Real.log (Real.exp x) := by rw [Real.log_exp]
    _ ≤ Real.log (exceptionalPrimeLower A1 : ℝ) :=
      Real.log_le_log (Real.exp_pos x) hexp

/-- Uniformly over the remote cover, an exceptional cell anchor keeps at
least half of the defining lower-endpoint logarithm. -/
theorem sliceA2Exceptional_halfScaleLog_le_anchor_log
    (A1 v : ℕ) (epsc eps rho0 : ℝ)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog6 : 2 * Real.log 6 ≤
      Real.log (exceptionalPrimeLower A1 : ℝ)) :
    (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ) / 2 ≤
      Real.log (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := by
  exact (div_le_div_of_nonneg_right
      (exceptionalScaleLog_le_primeLower_log A1) (by norm_num)).trans
    (sliceA2ExceptionalPrimeLog_le_anchor_log A1 v epsc eps rho0
      hv hanchor hlog6)

/-- Once `log(2T)` is at most `3 log A1`, the exceptional adaptive order is
bounded by `6 (log A1)^(1/50) + 2`. -/
theorem sliceA2ExceptionalMoment_cast_le_six_rpow_add_two
    (A1 v : ℕ) (epsc eps rho0 T : ℝ)
    (hX : 1 ≤ Real.log (A1 : ℝ)) (hT : 1 ≤ T)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog6 : 2 * Real.log 6 ≤
      Real.log (exceptionalPrimeLower A1 : ℝ))
    (hlogT : Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ)) :
    (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
      6 * (Real.log (A1 : ℝ)) ^ (1 / 50 : ℝ) + 2 := by
  let X := Real.log (A1 : ℝ)
  let P := sliceA2ExceptionalAnchor A1 v epsc eps rho0
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hhalf := sliceA2Exceptional_halfScaleLog_le_anchor_log
    A1 v epsc eps rho0 hv hanchor hlog6
  have hden : 0 < Real.log (P : ℝ) := by
    dsimp [P]
    exact Real.log_pos (by exact_mod_cast (show
      1 < sliceA2ExceptionalAnchor A1 v epsc eps rho0 by omega))
  have hratio : Real.log (2 * T) / Real.log (P : ℝ) ≤
      6 * X ^ (1 / 50 : ℝ) := by
    have hhalfPos : 0 < X ^ (49 / 50 : ℝ) / 2 := by positivity
    have hdiv : Real.log (2 * T) / Real.log (P : ℝ) ≤
        (3 * X) / (X ^ (49 / 50 : ℝ) / 2) := by
      exact div_le_div₀ (by positivity) hlogT hhalfPos hhalf
    have hpow : X ^ (49 / 50 : ℝ) * X ^ (1 / 50 : ℝ) = X := by
      rw [← Real.rpow_add hXpos]
      norm_num
    calc
      Real.log (2 * T) / Real.log (P : ℝ) ≤
          (3 * X) / (X ^ (49 / 50 : ℝ) / 2) := hdiv
      _ = 6 * X ^ (1 / 50 : ℝ) := by
        field_simp
        nlinarith
  have hell := adaptivePrimeMoment_cast_lt_log_ratio_add_two P T (by
    dsimp [P]
    omega) hT
  simpa [sliceA2ExceptionalMoment, exceptionalCellMoment, P, X] using
    hell.le.trans (add_le_add_left hratio 2)

end Tao2015

end MoltResearch
