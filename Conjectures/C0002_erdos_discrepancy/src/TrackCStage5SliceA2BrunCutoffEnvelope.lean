import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunHeight

/-!
# Track R A2-V'-31: subpower cutoff exponents

Write `X = log A1`, `W = log X`, and `u = exp(W/1000)`.  The preceding
height bound gives `J-1 <= W/1000`, hence `2^(J-1) <= u`.  Once the fixed
schedule constants are also below `u`, both adjacent ratios are at most
`u^3`; the cutoff overshoot exponent is then at most `u^10`, which is far
below `X^(1/16)`.
-/

namespace MoltResearch

namespace Tao2015

set_option maxHeartbeats 800000 in
/-- The selected last ratio, the cutoff overshoot exponent, and the cutoff
logarithm all have fixed subpower envelopes. -/
theorem exists_sliceA2Ladder_cutoff_envelopes
    (P0 ratio0 eta : ℕ) (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let X := Real.log (A1 : ℝ)
      let W := Real.log X
      let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      let n := J - 1
      let F : ℕ :=
        sliceA2LadderRatio ratio0 eta (J - 2) *
          (100 * n ^ 2) * sliceA2LadderRatio ratio0 eta n
      2 ≤ J ∧
        (n : ℝ) ≤ W / 1000 ∧
        (sliceA2LadderRatio ratio0 eta n : ℝ) ≤
          X ^ (3 / 1000 : ℝ) ∧
        (F : ℝ) ≤ X ^ (1 / 16 : ℝ) ∧
        Real.log (ordinaryLadderCutoff A1) ≤
          X ^ (1 / 16 : ℝ) := by
  obtain ⟨AH, hAH⟩ :=
    exists_sliceA2LadderHeight_le_loglog_div P0 ratio0 eta hP0 heta
  let C0 : ℝ := 2 + ratio0
  let M : ℝ := max 1 (max (Real.log (P0 + 1))
    (max (1000 * Real.log C0)
      (max (1000 * Real.log eta) (1000 * Real.log 10))))
  let AG : ℕ := ⌈Real.exp (Real.exp M)⌉₊ + 1
  refine ⟨max AH AG, fun A1 hA1 ↦ ?_⟩
  have hAH1 : AH ≤ A1 := (le_max_left AH AG).trans hA1
  have hAG1 : AG ≤ A1 := (le_max_right AH AG).trans hA1
  have hheight := hAH A1 hAH1
  let X := Real.log (A1 : ℝ)
  let W := Real.log X
  let z := W / 1000
  let u := Real.exp z
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  let n := J - 1
  let F : ℕ :=
    sliceA2LadderRatio ratio0 eta (J - 2) *
      (100 * n ^ 2) * sliceA2LadderRatio ratio0 eta n
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by dsimp [AG] at hAG1; omega)
  have hExpExp : Real.exp (Real.exp M) ≤ (A1 : ℝ) := by
    calc
      Real.exp (Real.exp M) ≤ (⌈Real.exp (Real.exp M)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ ≤ (A1 : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ ⌈Real.exp (Real.exp M)⌉₊) hAG1)
  have hX : Real.exp M ≤ X := by
    dsimp [X]
    exact (Real.le_log_iff_exp_le hA1pos).mpr hExpExp
  have hXpos : 0 < X := (Real.exp_pos M).trans_le hX
  have hW : M ≤ W := by
    dsimp [W]
    exact (Real.le_log_iff_exp_le hXpos).mpr hX
  have hW1 : 1 ≤ W :=
    (le_max_left 1 (max (Real.log (P0 + 1))
      (max (1000 * Real.log C0)
        (max (1000 * Real.log eta) (1000 * Real.log 10))))).trans hW
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hC0pos : 0 < C0 := by dsimp [C0]; positivity
  have hetaReal : (0 : ℝ) < eta := by exact_mod_cast (show 0 < eta by omega)
  have hten : (10 : ℝ) ≤ u := by
    have hm : 1000 * Real.log 10 ≤ W :=
      (le_max_right (1000 * Real.log eta) (1000 * Real.log 10)).trans
        ((le_max_right (1000 * Real.log C0)
          (max (1000 * Real.log eta) (1000 * Real.log 10))).trans
          ((le_max_right (Real.log (P0 + 1))
            (max (1000 * Real.log C0)
              (max (1000 * Real.log eta) (1000 * Real.log 10)))).trans
            ((le_max_right 1 (max (Real.log (P0 + 1))
              (max (1000 * Real.log C0)
                (max (1000 * Real.log eta) (1000 * Real.log 10))))).trans hW)))
    have : Real.log 10 ≤ z := by dsimp [z]; linarith
    calc
      (10 : ℝ) = Real.exp (Real.log 10) :=
        (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp z := Real.exp_le_exp.mpr this
      _ = u := rfl
  have hC0 : C0 ≤ u := by
    have hm : 1000 * Real.log C0 ≤ W :=
      (le_max_left (1000 * Real.log C0)
        (max (1000 * Real.log eta) (1000 * Real.log 10))).trans
        ((le_max_right (Real.log (P0 + 1))
          (max (1000 * Real.log C0)
            (max (1000 * Real.log eta) (1000 * Real.log 10)))).trans
          ((le_max_right 1 (max (Real.log (P0 + 1))
            (max (1000 * Real.log C0)
              (max (1000 * Real.log eta) (1000 * Real.log 10))))).trans hW))
    have : Real.log C0 ≤ z := by dsimp [z]; linarith
    calc
      C0 = Real.exp (Real.log C0) := (Real.exp_log hC0pos).symm
      _ ≤ Real.exp z := Real.exp_le_exp.mpr this
      _ = u := rfl
  have hetaU : (eta : ℝ) ≤ u := by
    have hm : 1000 * Real.log eta ≤ W :=
      (le_max_left (1000 * Real.log eta) (1000 * Real.log 10)).trans
        ((le_max_right (1000 * Real.log C0)
          (max (1000 * Real.log eta) (1000 * Real.log 10))).trans
          ((le_max_right (Real.log (P0 + 1))
            (max (1000 * Real.log C0)
              (max (1000 * Real.log eta) (1000 * Real.log 10)))).trans
            ((le_max_right 1 (max (Real.log (P0 + 1))
              (max (1000 * Real.log C0)
                (max (1000 * Real.log eta) (1000 * Real.log 10))))).trans hW)))
    have : Real.log (eta : ℝ) ≤ z := by dsimp [z]; linarith
    calc
      (eta : ℝ) = Real.exp (Real.log (eta : ℝ)) :=
        (Real.exp_log hetaReal).symm
      _ ≤ Real.exp z := Real.exp_le_exp.mpr this
      _ = u := rfl
  have hP0X : (P0 : ℝ) < X := by
    have hm : Real.log (P0 + 1) ≤ W :=
      (le_max_left (Real.log (P0 + 1))
        (max (1000 * Real.log C0)
          (max (1000 * Real.log eta) (1000 * Real.log 10)))).trans
        ((le_max_right 1 (max (Real.log (P0 + 1))
          (max (1000 * Real.log C0)
            (max (1000 * Real.log eta) (1000 * Real.log 10))))).trans hW)
    have hPadd : (P0 : ℝ) + 1 ≤ X := by
      calc
        (P0 : ℝ) + 1 = Real.exp (Real.log ((P0 : ℝ) + 1)) :=
          (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp W := Real.exp_le_exp.mpr (by simpa using hm)
        _ = X := Real.exp_log hXpos
    linarith
  have hX1 : 1 ≤ X := by
    have : (2 : ℝ) ≤ P0 := by exact_mod_cast hP0
    linarith
  have hbottom : (P0 : ℝ) < ordinaryLadderCutoff A1 := by
    unfold ordinaryLadderCutoff
    exact hP0X.trans_le (by
      simpa only [pow_one] using pow_le_pow_right₀ hX1 (by norm_num : 1 ≤ 40))
  have hJ2 : 2 ≤ J := by
    dsimp [J]
    exact sliceA2LadderJ_two_le_of_bottom_lt P0 ratio0 eta A1 hP0 hbottom
  have hn : (n : ℝ) ≤ z := by
    dsimp [n, J, z, W, X]
    exact hheight
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnU : (n : ℝ) ≤ u := by
    exact hn.trans (by
      have := Real.add_one_le_exp z
      linarith)
  have htwoPowN : ((2 ^ n : ℕ) : ℝ) ≤ u := by
    calc
      ((2 ^ n : ℕ) : ℝ) = (Real.exp (Real.log 2)) ^ n := by
        rw [Nat.cast_pow, Nat.cast_ofNat,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp z := by
        rw [Real.exp_le_exp]
        have hlogtwo : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
        nlinarith
      _ = u := rfl
  have hratio : ∀ j ≤ n,
      (sliceA2LadderRatio ratio0 eta j : ℝ) ≤ u ^ 3 := by
    intro j hj
    have hpowNat : 2 ^ j ≤ 2 ^ n := pow_le_pow_right' (by norm_num) hj
    have hpow : ((2 ^ j : ℕ) : ℝ) ≤ u :=
      (by exact_mod_cast hpowNat : ((2 ^ j : ℕ) : ℝ) ≤ (2 ^ n : ℕ)) |>.trans htwoPowN
    have hr := sliceA2LadderRatio_le ratio0 eta j
    have hrCast : (sliceA2LadderRatio ratio0 eta j : ℝ) ≤
        C0 + ((2 ^ j : ℕ) : ℝ) * eta := by
      have hr' : (sliceA2LadderRatio ratio0 eta j : ℝ) ≤
          ((2 + ratio0 + 2 ^ j * eta : ℕ) : ℝ) := by
        exact_mod_cast hr
      push_cast at hr'
      simpa [C0] using hr'
    have hu1 : (1 : ℝ) ≤ u := (by norm_num : (1 : ℝ) ≤ 10).trans hten
    calc
      (sliceA2LadderRatio ratio0 eta j : ℝ) ≤
          C0 + ((2 ^ j : ℕ) : ℝ) * eta := hrCast
      _ ≤ u + u * u := by gcongr
      _ ≤ u ^ 3 := by
        have hu2 : 2 ≤ u := (by norm_num : (2 : ℝ) ≤ 10).trans hten
        have h1 : u ≤ u ^ 2 := by nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hu1)]
        have h2 : 2 * u ^ 2 ≤ u ^ 3 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg u)]
        nlinarith
  have hnPred : J - 2 ≤ n := by dsimp [n]; omega
  have hRn := hratio n le_rfl
  have hRprev := hratio (J - 2) hnPred
  have hFraw : (F : ℝ) ≤ u ^ 10 := by
    have hnSq : (n : ℝ) ^ 2 ≤ u ^ 2 :=
      pow_le_pow_left₀ hn0 hnU 2
    have huSq100 : (100 : ℝ) ≤ u ^ 2 := by
      have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hten 2
      norm_num at ht ⊢
      exact ht
    have hmul : (F : ℝ) ≤ u ^ 3 * (100 * u ^ 2) * u ^ 3 := by
      dsimp [F]
      push_cast
      gcongr
    calc
      (F : ℝ) ≤ u ^ 3 * (100 * u ^ 2) * u ^ 3 := hmul
      _ = 100 * u ^ 8 := by ring
      _ ≤ u ^ 2 * u ^ 8 :=
        mul_le_mul_of_nonneg_right huSq100 (pow_nonneg hu0.le 8)
      _ = u ^ 10 := by ring
  have huPow (m : ℕ) : u ^ m = Real.exp ((m : ℝ) * z) := by
    dsimp [u]
    rw [← Real.exp_nat_mul]
  have hrpow (c : ℝ) : X ^ c = Real.exp (c * W) := by
    rw [Real.rpow_def_of_pos hXpos]
    dsimp [W]
    congr 1
    ring
  have hratioFinal : (sliceA2LadderRatio ratio0 eta n : ℝ) ≤
      X ^ (3 / 1000 : ℝ) := by
    calc
      (sliceA2LadderRatio ratio0 eta n : ℝ) ≤ u ^ 3 := hRn
      _ = Real.exp ((3 : ℝ) * z) := huPow 3
      _ = X ^ (3 / 1000 : ℝ) := by
        rw [hrpow]
        congr 1
        dsimp [z]
        ring
  have hFFinal : (F : ℝ) ≤ X ^ (1 / 16 : ℝ) := by
    calc
      (F : ℝ) ≤ u ^ 10 := hFraw
      _ = Real.exp ((10 : ℝ) * z) := huPow 10
      _ ≤ Real.exp ((1 / 16 : ℝ) * W) := by
        rw [Real.exp_le_exp]
        dsimp [z]
        nlinarith
      _ = X ^ (1 / 16 : ℝ) := (hrpow _).symm
  have hlogCut : Real.log (ordinaryLadderCutoff A1) ≤
      X ^ (1 / 16 : ℝ) := by
    have hzU : z ≤ u := by
      have := Real.add_one_le_exp z
      linarith
    have hlogForm : Real.log (ordinaryLadderCutoff A1) = 40 * W := by
      unfold ordinaryLadderCutoff
      rw [Real.log_pow]
      dsimp [X, W]
    have huPowSix : u ^ 6 ≤ X ^ (1 / 16 : ℝ) := by
      rw [huPow 6, hrpow]
      rw [Real.exp_le_exp]
      dsimp [z]
      nlinarith
    rw [hlogForm]
    calc
      40 * W = 40000 * z := by dsimp [z]; ring
      _ ≤ 40000 * u := mul_le_mul_of_nonneg_left hzU (by norm_num)
      _ ≤ u ^ 6 := by
        have hpowFive : (100000 : ℝ) ≤ u ^ 5 :=
          by
            have ht := pow_le_pow_left₀
              (by norm_num : (0 : ℝ) ≤ 10) hten 5
            norm_num at ht ⊢
            exact ht
        have : 40000 ≤ u ^ 5 := (by norm_num : (40000 : ℝ) ≤ 100000).trans hpowFive
        calc
          40000 * u ≤ u ^ 5 * u :=
            mul_le_mul_of_nonneg_right this hu0.le
          _ = u ^ 6 := by ring
      _ ≤ X ^ (1 / 16 : ℝ) := huPowSix
  exact ⟨hJ2, hn, hratioFinal, hFFinal, hlogCut⟩

end Tao2015

end MoltResearch
