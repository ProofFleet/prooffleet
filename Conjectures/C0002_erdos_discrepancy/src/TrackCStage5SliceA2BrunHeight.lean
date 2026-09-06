import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunClose

/-!
# Track R A2-V'-30: the selected ladder height is sublogarithmic

The triangular double-exponential growth estimate bounds the selected height
by twice a square root of a binary logarithm.  After converting that binary
logarithm to the real logarithm of the cutoff, the height is eventually at
most `loglog(A1)/1000`.  The generous factor `1000` reserves the margins used
for the endpoint and Brun-depth bounds.
-/

namespace MoltResearch

namespace Tao2015

/-- At large base scale, the number of positive ordinary levels is at most
one thousandth of `loglog(A1)`. -/
theorem exists_sliceA2LadderHeight_le_loglog_div
    (P0 ratio0 eta : ℕ) (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let X := Real.log (A1 : ℝ)
      let W := Real.log X
      ((sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1 : ℕ) : ℝ) ≤ W / 1000 := by
  let M : ℝ := 18000 ^ 2
  let A0 : ℕ := ⌈Real.exp (Real.exp M)⌉₊ + 1
  refine ⟨A0, fun A1 hA1 ↦ ?_⟩
  let X := Real.log (A1 : ℝ)
  let W := Real.log X
  let C : ℕ := ⌈ordinaryLadderCutoff A1⌉₊
  let L : ℕ := Nat.log 2 C + 1
  let S : ℕ := 2 * (Nat.sqrt L + 1)
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by dsimp [A0] at hA1; omega)
  have hExpExp : Real.exp (Real.exp M) ≤ (A1 : ℝ) := by
    calc
      Real.exp (Real.exp M) ≤ (⌈Real.exp (Real.exp M)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ ≤ (A1 : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ ⌈Real.exp (Real.exp M)⌉₊) hA1)
  have hX : Real.exp M ≤ X := by
    dsimp [X]
    exact (Real.le_log_iff_exp_le hA1pos).mpr hExpExp
  have hXpos : 0 < X := (Real.exp_pos M).trans_le hX
  have hW : M ≤ W := by
    dsimp [W]
    exact (Real.le_log_iff_exp_le hXpos).mpr hX
  have hM : (18000 : ℝ) ^ 2 ≤ W := by simpa [M] using hW
  have hW1 : 1 ≤ W := by
    have : (1 : ℝ) ≤ 18000 ^ 2 := by norm_num
    exact this.trans hM
  have hX1 : 1 ≤ X := by
    calc
      (1 : ℝ) ≤ Real.exp M := by
        exact Real.one_le_exp (by positivity)
      _ ≤ X := hX
  have hcut1 : (1 : ℝ) ≤ ordinaryLadderCutoff A1 := by
    unfold ordinaryLadderCutoff
    dsimp [X] at hX1 ⊢
    exact one_le_pow₀ hX1
  have hCupper : (C : ℝ) ≤ 2 * ordinaryLadderCutoff A1 := by
    calc
      (C : ℝ) ≤ ordinaryLadderCutoff A1 + 1 := by
        dsimp [C]
        exact (Nat.ceil_lt_add_one (ordinaryLadderCutoff_nonneg A1)).le
      _ ≤ ordinaryLadderCutoff A1 + ordinaryLadderCutoff A1 :=
        by simpa [add_comm] using
          add_le_add_left hcut1 (ordinaryLadderCutoff A1)
      _ = 2 * ordinaryLadderCutoff A1 := by ring
  have hCposNat : 0 < C := by
    have hceil := Nat.le_ceil (ordinaryLadderCutoff A1)
    have : (1 : ℝ) ≤ C := hcut1.trans hceil
    exact_mod_cast (show (0 : ℝ) < C by linarith)
  have hlogC : Real.log (C : ℝ) ≤ 41 * W := by
    have htwoCut : (0 : ℝ) < 2 * ordinaryLadderCutoff A1 :=
      mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hcut1)
    calc
      Real.log (C : ℝ) ≤ Real.log (2 * ordinaryLadderCutoff A1) :=
        Real.log_le_log (by exact_mod_cast hCposNat) hCupper
      _ = Real.log 2 + 40 * W := by
        rw [Real.log_mul (by norm_num) (ne_of_gt
          (lt_of_lt_of_le zero_lt_one hcut1))]
        unfold ordinaryLadderCutoff
        rw [Real.log_pow]
        dsimp [X, W]
      _ ≤ 41 * W := by
        have hlogtwo : Real.log 2 ≤ W :=
          (Real.log_two_lt_d9.le).trans (by linarith)
        linarith
  let l : ℕ := Nat.log 2 C
  have hpowlog : 2 ^ l ≤ C := by
    dsimp [l]
    exact Nat.pow_log_le_self 2 (by omega)
  have hlogLower : (l : ℝ) * Real.log 2 ≤ Real.log (C : ℝ) := by
    calc
      (l : ℝ) * Real.log 2 = Real.log (((2 ^ l : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      _ ≤ Real.log (C : ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hpowlog
  have hl : (l : ℝ) ≤ 60 * W := by
    have hlogtwo := Real.log_two_gt_d9
    have hl0 : (0 : ℝ) ≤ l := by positivity
    nlinarith [hlogLower.trans hlogC]
  have hL : (L : ℝ) ≤ 61 * W := by
    dsimp [L, l] at hl ⊢
    push_cast
    linarith
  have hsqrt : (Nat.sqrt L : ℝ) ≤ 8 * Real.sqrt W := by
    have hsquare : (Nat.sqrt L : ℝ) ^ 2 ≤ (L : ℝ) := by
      exact_mod_cast Nat.sqrt_le' L
    have hW0 : 0 ≤ W := hW1.trans' (by norm_num)
    have hsqrtSq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0
    have hs0 : (0 : ℝ) ≤ Nat.sqrt L := by positivity
    have hr0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg W
    nlinarith
  have hsqrtW1 : 1 ≤ Real.sqrt W := by
    rw [Real.one_le_sqrt]
    exact hW1
  have hSsqrt : (S : ℝ) ≤ 18 * Real.sqrt W := by
    dsimp [S]
    push_cast
    nlinarith
  have hsqrtLarge : (18000 : ℝ) ≤ Real.sqrt W :=
    Real.le_sqrt_of_sq_le hM
  have hS : (S : ℝ) ≤ W / 1000 := by
    have hW0 : 0 ≤ W := hW1.trans' (by norm_num)
    have hsqrtSq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0
    calc
      (S : ℝ) ≤ 18 * Real.sqrt W := hSsqrt
      _ ≤ W / 1000 := by nlinarith
  have hJ := sliceA2LadderJ_le_sqrt_log_cutoff
    P0 ratio0 eta A1 hP0 heta
  have hnS : sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1 ≤ S := by
    dsimp [S, L, C]
    omega
  dsimp only [X, W]
  exact (by exact_mod_cast hnS :
    ((sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1 : ℕ) : ℝ) ≤ S) |>.trans hS

end Tao2015

end MoltResearch
