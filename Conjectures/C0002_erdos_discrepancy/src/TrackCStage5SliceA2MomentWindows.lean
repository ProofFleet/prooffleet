import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentScalar

/-!
# Track R A2-V': window-uniform exceptional logarithms

For `A1 <= A <= A1^2` and `T <= A`, every logarithm occurring in the
exceptional high moment is bounded by one common quantity depending only on
the base window.  The dependence on the fixed remote interval ratio is kept
explicit.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Fixed additive logarithmic allowance for the remote interval ratio. -/
noncomputable def sliceA2MomentLogConstant (epsc : ℝ) : ℝ :=
  3 + Real.log (1 + 3 * (exceptionalIntervalRatio epsc : ℝ))

theorem sliceA2MomentLogConstant_three_le (epsc : ℝ) :
    3 ≤ sliceA2MomentLogConstant epsc := by
  unfold sliceA2MomentLogConstant
  have harg : (1 : ℝ) ≤
      1 + 3 * (exceptionalIntervalRatio epsc : ℝ) := by
    have : (0 : ℝ) ≤ exceptionalIntervalRatio epsc := by positivity
    nlinarith
  linarith [Real.log_nonneg harg]

/-- A lower anchor whose index belongs to the remote cover never exceeds
the remote interval's upper endpoint. -/
theorem sliceA2ExceptionalAnchor_le_upper
    (A1 v : ℕ) (epsc eps rho0 : ℝ)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0) :
    (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) ≤
      exceptionalPrimeUpper A1 epsc := by
  let N := sliceA2ExceptionalN A1 epsc eps rho0
  let Q := exceptionalPrimeUpper A1 epsc
  let x := Real.exp ((v : ℝ) / (2 * (N : ℝ)))
  have hN : 0 < N := by
    simpa [N] using sliceA2ExceptionalN_pos A1 epsc eps rho0
  have hQpos : (0 : ℝ) < Q := by
    exact_mod_cast (show 0 < Q by
      have hP := exceptionalPrimeLower_le_upper A1 epsc
      have hP3 := exceptionalPrimeLower_three_le A1
      omega)
  have hvUpper : v ≤ exceptionalV1 A1 N epsc := by
    have hv' : v ∈ Finset.Ico
        (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1) := by
      simpa only [sliceA2ExceptionalI] using hv
    have hvLe : v ≤ sliceA2ExceptionalV1 A1 epsc eps rho0 := by
      have := (Finset.mem_Ico.mp hv').2
      omega
    simpa [sliceA2ExceptionalV1, N] using hvLe
  have hfloor : (v : ℝ) ≤ (2 * N : ℕ) * Real.log Q := by
    unfold exceptionalV1 eadicCoverIndexUpper at hvUpper
    exact (by exact_mod_cast hvUpper :
      (v : ℝ) ≤ ⌊(2 * N : ℕ) * Real.log Q⌋₊) |>.trans
        (Nat.floor_le (by positivity))
  have hxQ : x ≤ Q := by
    have hden : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    have hdiv : (v : ℝ) / (2 * (N : ℝ)) ≤ Real.log Q := by
      rw [div_le_iff₀ hden]
      simpa [mul_comm] using hfloor
    calc
      x ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr hdiv
      _ = Q := Real.exp_log hQpos
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hanchorX :
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) ≤ x := by
    have hceil := Nat.ceil_lt_add_one hx0
    unfold sliceA2ExceptionalAnchor exceptionalCellAnchor eadicCellLowerAnchor
    rw [Nat.cast_sub (by simpa [x, N] using hceil1)]
    push_cast
    simpa [x, N] using hceil.le
  exact hanchorX.trans hxQ

/-- The logarithm of twice any remote anchor is at most a fixed multiple of
`log A1`. -/
theorem sliceA2Exceptional_log_two_anchor_le
    (A1 v : ℕ) (epsc eps rho0 : ℝ)
    (hX : 1 ≤ Real.log (A1 : ℝ))
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) :
    Real.log (2 * (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ)) ≤
      (1 + 3 * (exceptionalIntervalRatio epsc : ℝ)) *
        Real.log (A1 : ℝ) := by
  let X := Real.log (A1 : ℝ)
  let R := exceptionalIntervalRatio epsc
  let P := sliceA2ExceptionalAnchor A1 v epsc eps rho0
  let Q := exceptionalPrimeUpper A1 epsc
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hA1one : 1 ≤ A1 := by
    by_contra h
    have : A1 = 0 := by omega
    subst A1
    norm_num at hX
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hQpos : (0 : ℝ) < Q := by
    exact_mod_cast (show 0 < Q by
      have hlo := exceptionalPrimeLower_three_le A1
      have hle := exceptionalPrimeLower_le_upper A1 epsc
      omega)
  have hPQ : (P : ℝ) ≤ Q := by
    simpa [P, Q] using sliceA2ExceptionalAnchor_le_upper
      A1 v epsc eps rho0 hv
  have hlogPQ : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hPpos hPQ
  have hbase := exceptionalPrimeLower_cast_le_four_exp A1 hA1one
  have hbasePos : (0 : ℝ) < exceptionalPrimeLower A1 := by
    exact_mod_cast (show 0 < exceptionalPrimeLower A1 by
      have := exceptionalPrimeLower_three_le A1
      omega)
  have hlogBase : Real.log (exceptionalPrimeLower A1 : ℝ) ≤
      Real.log 4 + X ^ (49 / 50 : ℝ) := by
    calc
      Real.log (exceptionalPrimeLower A1 : ℝ) ≤
          Real.log (4 * Real.exp (X ^ (49 / 50 : ℝ))) :=
        Real.log_le_log hbasePos hbase
      _ = Real.log 4 + X ^ (49 / 50 : ℝ) := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hlogQ : Real.log (Q : ℝ) =
      (R : ℝ) * Real.log (exceptionalPrimeLower A1 : ℝ) := by
    dsimp [Q]
    unfold exceptionalPrimeUpper
    rw [Nat.cast_pow, Real.log_pow]
  have hxpow : X ^ (49 / 50 : ℝ) ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num :
        (49 / 50 : ℝ) ≤ 1)
  have hlog4 : Real.log 4 ≤ 2 * X := by
    have hlog2one : Real.log 2 ≤ 1 :=
      ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
        Real.exp_one_gt_two).le
    have : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
      nlinarith
    nlinarith
  have hlogP : Real.log (P : ℝ) ≤ 3 * (R : ℝ) * X := by
    rw [hlogQ] at hlogPQ
    have hR0 : (0 : ℝ) ≤ R := by positivity
    have := mul_le_mul_of_nonneg_left hlogBase hR0
    nlinarith
  have hlog2 : Real.log 2 ≤ X := Real.log_two_lt_d9.le.trans (by linarith)
  calc
    Real.log (2 * (P : ℝ)) = Real.log 2 + Real.log (P : ℝ) :=
      Real.log_mul (by norm_num) hPpos.ne'
    _ ≤ X + 3 * (R : ℝ) * X := add_le_add hlog2 hlogP
    _ = (1 + 3 * (R : ℝ)) * X := by ring

/-- All four logarithmic factors in a remote moment share one base-window
envelope. -/
theorem sliceA2Exceptional_common_log_bounds
    (A1 A v : ℕ) (epsc eps rho0 T : ℝ)
    (hX : 1 ≤ Real.log (A1 : ℝ)) (hA : 3 ≤ A)
    (hAA1 : A ≤ A1 ^ 2) (hT : 1 ≤ T) (hTA : T ≤ A)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog6 : 2 * Real.log 6 ≤
      Real.log (exceptionalPrimeLower A1 : ℝ)) :
    let X := Real.log (A1 : ℝ)
    let Z := Real.log X + sliceA2MomentLogConstant epsc
    0 ≤ Z ∧
      Real.log (2 * T) ≤ 3 * X ∧
      (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
        6 * X ^ (1 / 50 : ℝ) + 2 ∧
      Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤ Z ∧
      Real.log (Real.log (2 *
        (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))) ≤ Z ∧
      Real.log (Real.log (A : ℝ)) ≤ Z ∧
      Real.log (Real.log (2 * T)) ≤ Z := by
  let X := Real.log (A1 : ℝ)
  let C := sliceA2MomentLogConstant epsc
  let Z := Real.log X + C
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hC3 : 3 ≤ C := sliceA2MomentLogConstant_three_le epsc
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by
      by_contra h
      have : A1 = 0 := Nat.eq_zero_of_not_pos h
      subst A1
      norm_num at hX)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAA1R : (A : ℝ) ≤ (A1 : ℝ) ^ 2 := by exact_mod_cast hAA1
  have hlogA : Real.log (A : ℝ) ≤ 2 * X := by
    calc
      Real.log (A : ℝ) ≤ Real.log ((A1 : ℝ) ^ 2) :=
        Real.log_le_log hApos hAA1R
      _ = 2 * X := by rw [Real.log_pow]; norm_num [X]
  have hlog2 : Real.log 2 ≤ X := Real.log_two_lt_d9.le.trans (by linarith)
  have hlogTinner : Real.log (2 * T) ≤ 3 * X := by
    have h2Tpos : 0 < 2 * T := by positivity
    have h2TA : 2 * T ≤ 2 * (A : ℝ) := by
      have hTAR : T ≤ (A : ℝ) := hTA
      linarith
    calc
      Real.log (2 * T) ≤ Real.log (2 * (A : ℝ)) :=
        Real.log_le_log h2Tpos h2TA
      _ = Real.log 2 + Real.log (A : ℝ) :=
        Real.log_mul (by norm_num) hApos.ne'
      _ ≤ X + 2 * X := add_le_add hlog2 hlogA
      _ = 3 * X := by ring
  have hell := sliceA2ExceptionalMoment_cast_le_six_rpow_add_two
    A1 v epsc eps rho0 T hX hT hv hanchor hlog6 hlogTinner
  have hx02 : 1 ≤ X ^ (1 / 50 : ℝ) :=
    Real.one_le_rpow hX (by norm_num)
  have hellEight :
      (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
        8 * X ^ (1 / 50 : ℝ) := by nlinarith
  have hellPos : (0 : ℝ) <
      sliceA2ExceptionalMoment A1 v epsc eps rho0 T := by
    exact_mod_cast (show 0 < sliceA2ExceptionalMoment A1 v epsc eps rho0 T by
      have := sliceA2ExceptionalMoment_one_le A1 v epsc eps rho0 T
      omega)
  have hlogell :
      Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤ Z := by
    calc
      Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
          Real.log (8 * X ^ (1 / 50 : ℝ)) :=
        Real.log_le_log hellPos hellEight
      _ = Real.log 8 + (1 / 50 : ℝ) * Real.log X := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity)),
          Real.log_rpow hXpos]
      _ ≤ Real.log X + 3 := by
        have hlog2one : Real.log 2 ≤ 1 :=
          ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
            Real.exp_one_gt_two).le
        have hlog8 : Real.log 8 ≤ 3 := by
          rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
          norm_num
          nlinarith
        nlinarith
      _ ≤ Z := by dsimp [Z]; linarith
  let B : ℝ := 1 + 3 * (exceptionalIntervalRatio epsc : ℝ)
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have : (0 : ℝ) ≤ exceptionalIntervalRatio epsc := by positivity
    nlinarith
  have hlogAnchorInner := sliceA2Exceptional_log_two_anchor_le
    A1 v epsc eps rho0 hX hv hanchor
  have hlogAnchorPos : 0 < Real.log (2 *
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 *
      sliceA2ExceptionalAnchor A1 v epsc eps rho0 by omega))
  have hlogAnchor : Real.log (Real.log (2 *
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))) ≤ Z := by
    calc
      Real.log (Real.log (2 *
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))) ≤
          Real.log (B * X) :=
        Real.log_le_log hlogAnchorPos (by simpa [B, X] using hlogAnchorInner)
      _ = Real.log B + Real.log X :=
        Real.log_mul (by positivity) hXpos.ne'
      _ ≤ Z := by
        dsimp [Z, C, sliceA2MomentLogConstant, B]
        linarith
  have hlogApos : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hloglogA : Real.log (Real.log (A : ℝ)) ≤ Z := by
    calc
      Real.log (Real.log (A : ℝ)) ≤ Real.log (2 * X) :=
        Real.log_le_log hlogApos hlogA
      _ = Real.log 2 + Real.log X :=
        Real.log_mul (by norm_num) hXpos.ne'
      _ ≤ Z := by dsimp [Z]; nlinarith [Real.log_two_lt_d9]
  have hlogTpos : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hloglogT : Real.log (Real.log (2 * T)) ≤ Z := by
    calc
      Real.log (Real.log (2 * T)) ≤ Real.log (3 * X) :=
        Real.log_le_log hlogTpos hlogTinner
      _ = Real.log 3 + Real.log X :=
        Real.log_mul (by norm_num) hXpos.ne'
      _ ≤ Z := by
        have hlog3 : Real.log 3 ≤ 3 := by
          have h3 : Real.log 3 ≤ Real.log 9 :=
            Real.log_le_log (by norm_num) (by norm_num)
          exact h3.trans (log_nine_le.trans (by norm_num))
        dsimp [Z]
        linarith
  exact ⟨by linarith, hlogTinner, hell, hlogell,
    hlogAnchor, hloglogA, hloglogT⟩

end Tao2015

end MoltResearch
