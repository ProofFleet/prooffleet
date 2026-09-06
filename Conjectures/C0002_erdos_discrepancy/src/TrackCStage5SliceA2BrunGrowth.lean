import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunCutoffEnvelope

/-!
# Track R A2-V'-32: the final Brun growth margins

The cutoff overshoot exponent and cutoff logarithm are each bounded by
`X^(1/16)`, where `X = log A1`.  Thus the last upper endpoint has logarithm
at most `X^(1/8)`.  The last canonical Brun depth is only linear in
`log X`.  Both fit comfortably under the common envelope `y = X^(1/3)`,
whose square is still sublinear in `X`.
-/

namespace MoltResearch

namespace Tao2015

/-- The two one-sixteenth-power cutoff bounds imply the required
one-third-power endpoint bound. -/
theorem sliceA2LadderQ_add_one_le_exp_third
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hJ2 : 2 ≤ sliceA2LadderJ P0 ratio0 eta A1 hP0)
    (hX1 : 1 ≤ Real.log (A1 : ℝ))
    (hXlarge : (2 : ℝ) ^ 24 ≤ Real.log (A1 : ℝ))
    (hF : let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      let F : ℕ :=
        sliceA2LadderRatio ratio0 eta (J - 2) *
          (100 * (J - 1) ^ 2) * sliceA2LadderRatio ratio0 eta (J - 1)
      (F : ℝ) ≤ Real.log (A1 : ℝ) ^ (1 / 16 : ℝ))
    (hcut : Real.log (ordinaryLadderCutoff A1) ≤
      Real.log (A1 : ℝ) ^ (1 / 16 : ℝ)) :
    (sliceA2LadderQ P0 ratio0 eta
        (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1) : ℝ) + 1 ≤
      Real.exp (Real.log (A1 : ℝ) ^ (1 / 3 : ℝ)) := by
  let X := Real.log (A1 : ℝ)
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  let n := J - 1
  let F : ℕ :=
    sliceA2LadderRatio ratio0 eta (J - 2) *
      (100 * n ^ 2) * sliceA2LadderRatio ratio0 eta n
  let Q := sliceA2LadderQ P0 ratio0 eta n
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hcutPos : 0 < ordinaryLadderCutoff A1 := by
    unfold ordinaryLadderCutoff
    positivity
  have hcutLog0 : 0 ≤ Real.log (ordinaryLadderCutoff A1) :=
    Real.log_nonneg (by
      unfold ordinaryLadderCutoff
      exact one_le_pow₀ hX1)
  have hF' : (F : ℝ) ≤ X ^ (1 / 16 : ℝ) := by
    simpa [F, J, n, X] using hF
  have hprod : (F : ℝ) * Real.log (ordinaryLadderCutoff A1) ≤
      X ^ (1 / 8 : ℝ) := by
    calc
      (F : ℝ) * Real.log (ordinaryLadderCutoff A1) ≤
          X ^ (1 / 16 : ℝ) * X ^ (1 / 16 : ℝ) :=
        mul_le_mul hF' hcut (by positivity) (by positivity)
      _ = X ^ ((1 / 16 : ℝ) + 1 / 16) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X ^ (1 / 8 : ℝ) := by norm_num
  have hcutPow : ordinaryLadderCutoff A1 ^ F ≤
      Real.exp (X ^ (1 / 8 : ℝ)) := by
    calc
      ordinaryLadderCutoff A1 ^ F =
          (Real.exp (Real.log (ordinaryLadderCutoff A1))) ^ F := by
        rw [Real.exp_log hcutPos]
      _ =
          Real.exp ((F : ℝ) * Real.log (ordinaryLadderCutoff A1)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (X ^ (1 / 8 : ℝ)) :=
        Real.exp_le_exp.mpr hprod
  have hQcut := sliceA2LadderQ_lt_cutoff_pow
    P0 ratio0 eta A1 hP0 hJ2
  have hQexp : (Q : ℝ) ≤ Real.exp (X ^ (1 / 8 : ℝ)) := by
    dsimp [Q, n, J]
    exact hQcut.le.trans (by simpa [F, n, J] using hcutPow)
  have hQone : (1 : ℝ) ≤ Q := by
    dsimp [Q]
    exact_mod_cast (show 1 ≤ sliceA2LadderQ P0 ratio0 eta n by
      exact (sliceA2LadderP_two_le P0 ratio0 eta n hP0).trans'
        (by norm_num) |>.trans (sliceA2LadderP_le_Q P0 ratio0 eta n))
  have hroot : (2 : ℝ) ≤ X ^ (1 / 24 : ℝ) := by
    have hr := Real.rpow_le_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 24)
      hXlarge (by norm_num : (0 : ℝ) ≤ (24 : ℝ)⁻¹)
    calc
      (2 : ℝ) = ((2 : ℝ) ^ 24) ^ ((24 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num : (24 : ℕ) ≠ 0)).symm
      _ ≤ X ^ ((24 : ℝ)⁻¹) := hr
      _ = X ^ (1 / 24 : ℝ) := by norm_num
  have hfactor : (2 : ℝ) ≤ X ^ (5 / 24 : ℝ) :=
    hroot.trans (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num))
  have hdouble : 2 * X ^ (1 / 8 : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
    calc
      2 * X ^ (1 / 8 : ℝ) ≤
          X ^ (5 / 24 : ℝ) * X ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = X ^ ((5 / 24 : ℝ) + 1 / 8) :=
        (Real.rpow_add hXpos _ _).symm
      _ = X ^ (1 / 3 : ℝ) := by norm_num
  have hlogtwo : Real.log 2 ≤ X ^ (1 / 8 : ℝ) :=
    Real.log_two_lt_d9.le.trans (by
      have : (1 : ℝ) ≤ X ^ (1 / 8 : ℝ) :=
        Real.one_le_rpow hX1 (by norm_num)
      linarith)
  have hexponent : Real.log 2 + X ^ (1 / 8 : ℝ) ≤
      X ^ (1 / 3 : ℝ) := by linarith
  calc
    (Q : ℝ) + 1 ≤ 2 * Q := by linarith
    _ ≤ 2 * Real.exp (X ^ (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hQexp (by norm_num)
    _ = Real.exp (Real.log 2 + X ^ (1 / 8 : ℝ)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (X ^ (1 / 3 : ℝ)) := Real.exp_le_exp.mpr hexponent

set_option maxHeartbeats 800000 in
/-- Eventually all four hypotheses of the subpower Brun closure hold for
the selected schedule. -/
theorem exists_sliceA2Ladder_brunGrowthMargins
    (P0 ratio0 eta : ℕ) (epsc : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let X := Real.log (A1 : ℝ)
      let y := X ^ (1 / 3 : ℝ)
      let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      let n := J - 1
      (n : ℝ) ≤ Real.exp y ∧
        (sliceA2LadderQ P0 ratio0 eta n : ℝ) + 1 ≤ Real.exp y ∧
        (brunPowerIntervalDepth
          (sliceA2LadderRatio ratio0 eta n) : ℝ) ≤ y ∧
        Real.log (32 / epsc) + y + 2 * y ^ 2 ≤
          Real.log (A1 : ℝ) := by
  obtain ⟨AC, hAC⟩ :=
    exists_sliceA2Ladder_cutoff_envelopes P0 ratio0 eta hP0 heta
  let D : ℝ := max 0 (Real.log (32 / epsc))
  let M : ℝ := max 1000 (Real.log (4 * (D + 1)))
  let AG : ℕ := ⌈Real.exp (Real.exp M)⌉₊ + 1
  refine ⟨max AC AG, fun A1 hA1 ↦ ?_⟩
  have hAC1 : AC ≤ A1 := (le_max_left AC AG).trans hA1
  have hAG1 : AG ≤ A1 := (le_max_right AC AG).trans hA1
  obtain ⟨hJ2, hnSmall, hRsmall, hFsmall, hcutSmall⟩ := hAC A1 hAC1
  let X := Real.log (A1 : ℝ)
  let W := Real.log X
  let y := X ^ (1 / 3 : ℝ)
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  let n := J - 1
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by dsimp [AG] at hAG1; omega)
  have hExpExp : Real.exp (Real.exp M) ≤ (A1 : ℝ) := by
    calc
      Real.exp (Real.exp M) ≤ (⌈Real.exp (Real.exp M)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (A1 : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ ⌈Real.exp (Real.exp M)⌉₊) hAG1)
  have hX : Real.exp M ≤ X := by
    dsimp [X]
    exact (Real.le_log_iff_exp_le hA1pos).mpr hExpExp
  have hXpos : 0 < X := (Real.exp_pos M).trans_le hX
  have hW : M ≤ W := by
    dsimp [W]
    exact (Real.le_log_iff_exp_le hXpos).mpr hX
  have hW1000 : (1000 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ Real.exp M := Real.one_le_exp (by
      have : (0 : ℝ) ≤ M := (by norm_num : (0 : ℝ) ≤ 1000).trans
        (le_max_left _ _)
      exact this)
    exact this.trans hX
  have hXlarge : (2 : ℝ) ^ 24 ≤ X := by
    have hlogBound : 24 * Real.log 2 ≤ W := by
      have hlogtwo := Real.log_two_lt_d9
      nlinarith
    calc
      (2 : ℝ) ^ 24 = (Real.exp (Real.log 2)) ^ 24 := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (24 * Real.log 2) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ Real.exp W := Real.exp_le_exp.mpr hlogBound
      _ = X := Real.exp_log hXpos
  have hQ : (sliceA2LadderQ P0 ratio0 eta n : ℝ) + 1 ≤
      Real.exp y := by
    apply sliceA2LadderQ_add_one_le_exp_third P0 ratio0 eta A1 hP0
      hJ2 hX1 hXlarge
    · simpa [J, n, X] using hFsmall
    · simpa [X] using hcutSmall
  have hyExp : y = Real.exp (W / 3) := by
    dsimp [y, W]
    rw [Real.rpow_def_of_pos hXpos]
    congr 1
    ring
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hn : (n : ℝ) ≤ Real.exp y := by
    have hn' : (n : ℝ) ≤ W / 1000 := by
      simpa [n, J, W, X] using hnSmall
    have hny : (n : ℝ) ≤ y := by
      rw [hyExp]
      have hpow := Real.pow_div_factorial_le_exp
        (W / 3) (by positivity) 2
      norm_num at hpow
      nlinarith
    exact hny.trans (by
      have := Real.add_one_le_exp y
      linarith)
  have hdepth : (brunPowerIntervalDepth
      (sliceA2LadderRatio ratio0 eta n) : ℝ) ≤ y := by
    let R := sliceA2LadderRatio ratio0 eta n
    have hR2 : 2 ≤ R := sliceA2LadderRatio_two_le ratio0 eta n
    have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    have hRbound : (R : ℝ) ≤ X ^ (1 / 16 : ℝ) := by
      have hpowMono := Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num : (3 / 1000 : ℝ) ≤ 1 / 16)
      have hRsmall' : (R : ℝ) ≤ X ^ (3 / 1000 : ℝ) := by
        simpa [R, n, J, X] using hRsmall
      exact hRsmall'.trans hpowMono
    have hRadd : (R : ℝ) + 1 ≤ 2 * X ^ (1 / 16 : ℝ) := by
      have hone : (1 : ℝ) ≤ X ^ (1 / 16 : ℝ) :=
        Real.one_le_rpow hX1 (by norm_num)
      linarith
    have hlogR : Real.log ((R : ℝ) + 1) ≤ W := by
      calc
        Real.log ((R : ℝ) + 1) ≤
            Real.log (2 * X ^ (1 / 16 : ℝ)) :=
          Real.log_le_log (by positivity) hRadd
        _ = Real.log 2 + (1 / 16 : ℝ) * W := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          rw [Real.log_rpow hXpos]
        _ ≤ W := by
          have hlogtwo := Real.log_two_lt_d9
          nlinarith
    have ht0 : 0 ≤ Real.exp 1 * (Real.log ((R : ℝ) + 1) + 12) := by
      have : 0 ≤ Real.log ((R : ℝ) + 1) :=
        Real.log_nonneg (by linarith)
      positivity
    have hceil : (brunPowerIntervalDepth R : ℝ) ≤
        Real.exp 1 * (Real.log ((R : ℝ) + 1) + 12) + 1 := by
      unfold brunPowerIntervalDepth
      exact (Nat.ceil_lt_add_one ht0).le
    have hquad := Real.pow_div_factorial_le_exp
      (W / 3) (by positivity) 2
    norm_num at hquad
    rw [hyExp]
    calc
      (brunPowerIntervalDepth R : ℝ) ≤
          Real.exp 1 * (Real.log ((R : ℝ) + 1) + 12) + 1 := hceil
      _ ≤ 3 * (W + 12) + 1 := by
        have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
        have hsum0 : 0 ≤ Real.log ((R : ℝ) + 1) + 12 := by
          have : 0 ≤ Real.log ((R : ℝ) + 1) :=
            Real.log_nonneg (by linarith)
          linarith
        nlinarith
      _ ≤ (W / 3) ^ 2 / 2 := by nlinarith
      _ ≤ Real.exp (W / 3) := hquad
  have hD : D ≤ X / 4 := by
    have hm : Real.log (4 * (D + 1)) ≤ W :=
      (le_max_right 1000 (Real.log (4 * (D + 1)))).trans hW
    have hD0 : 0 ≤ D := le_max_left _ _
    have harg : 0 < 4 * (D + 1) := by positivity
    have : 4 * (D + 1) ≤ X := by
      calc
        4 * (D + 1) = Real.exp (Real.log (4 * (D + 1))) :=
          (Real.exp_log harg).symm
        _ ≤ Real.exp W := Real.exp_le_exp.mpr hm
        _ = X := Real.exp_log hXpos
    linarith
  have hlogCoeff : Real.log (32 / epsc) ≤ X / 4 :=
    (le_max_right 0 (Real.log (32 / epsc))).trans hD
  have hfourRoot : (4 : ℝ) ≤ X ^ (1 / 12 : ℝ) := by
    have hbase : (4 : ℝ) ^ 12 = (2 : ℝ) ^ 24 := by ring
    have hr := Real.rpow_le_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) 12)
      (hbase.le.trans hXlarge) (by norm_num : (0 : ℝ) ≤ (12 : ℝ)⁻¹)
    calc
      (4 : ℝ) = ((4 : ℝ) ^ 12) ^ ((12 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4)
          (by norm_num : (12 : ℕ) ≠ 0)).symm
      _ ≤ X ^ ((12 : ℝ)⁻¹) := hr
      _ = X ^ (1 / 12 : ℝ) := by norm_num
  have hyQuarter : y ≤ X / 4 := by
    have hfac : (4 : ℝ) ≤ X ^ (2 / 3 : ℝ) :=
      hfourRoot.trans (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num))
    have hmul := mul_le_mul_of_nonneg_right hfac hy0
    have hprod : X ^ (2 / 3 : ℝ) * y = X := by
      dsimp [y]
      rw [← Real.rpow_add hXpos]
      norm_num
    rw [hprod] at hmul
    linarith
  have htwoYSq : 2 * y ^ 2 ≤ X / 2 := by
    have hfac : (4 : ℝ) ≤ X ^ (1 / 3 : ℝ) :=
      hfourRoot.trans (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num))
    have hySq : y ^ 2 = X ^ (2 / 3 : ℝ) := by
      dsimp [y]
      rw [pow_two, ← Real.rpow_add hXpos]
      norm_num
    have hmul := mul_le_mul_of_nonneg_right hfac (by positivity : 0 ≤ y ^ 2)
    rw [hySq] at hmul
    have hprod : X ^ (1 / 3 : ℝ) * X ^ (2 / 3 : ℝ) = X := by
      rw [← Real.rpow_add hXpos]
      norm_num
    rw [hprod] at hmul
    linarith
  have hmargin : Real.log (32 / epsc) + y + 2 * y ^ 2 ≤ X := by
    linarith
  exact ⟨hn, hQ, hdepth, by simpa [y, X] using hmargin⟩

end Tao2015

end MoltResearch
