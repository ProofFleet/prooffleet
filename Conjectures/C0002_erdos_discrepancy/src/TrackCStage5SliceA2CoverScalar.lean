import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverConditions

/-!
# Track R A2-V': scalar cover remainder

The last ordinary anchor and the two residual logarithms are sublinear in
`X = log A1`.  This leaf gives a fully explicit double-exponential threshold
at which they occupy only `X/2000`.
-/

namespace MoltResearch

namespace Tao2015

/-- At a sufficiently large logarithmic scale, the last cover's complete
subpower remainder is at most `X/2000`. -/
theorem sliceA2Cover_scalar_remainder
    (X : ℝ) (hX : 1 ≤ X) (hW : 100000 ≤ Real.log X) :
    (101 / 125 : ℝ) * X ^ (1 / 3 : ℝ) +
        8 * Real.log X + 6 ≤ X / 2000 := by
  let W := Real.log X
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hW0 : 0 ≤ W := by dsimp [W]; linarith
  have hxexp : Real.exp W = X := by
    dsimp [W]
    exact Real.exp_log hXpos
  have hx23 : (3232 : ℝ) ≤ X ^ (2 / 3 : ℝ) := by
    have hexp : 1 + (2 / 3 : ℝ) * W ≤
        Real.exp ((2 / 3 : ℝ) * W) := by
      simpa [add_comm] using Real.add_one_le_exp ((2 / 3 : ℝ) * W)
    have hlarge : (3232 : ℝ) ≤ 1 + (2 / 3 : ℝ) * W := by
      linarith
    calc
      (3232 : ℝ) ≤ Real.exp ((2 / 3 : ℝ) * W) := hlarge.trans hexp
      _ = X ^ (2 / 3 : ℝ) := by
        rw [Real.rpow_def_of_pos hXpos]
        congr 1
        ring
  have hpowers : X ^ (1 / 3 : ℝ) * X ^ (2 / 3 : ℝ) = X := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hfirst : (101 / 125 : ℝ) * X ^ (1 / 3 : ℝ) ≤ X / 4000 := by
    have hm := mul_le_mul_of_nonneg_left hx23
      (Real.rpow_nonneg hXpos.le (1 / 3 : ℝ))
    rw [hpowers] at hm
    nlinarith
  have hexpQuad := Real.pow_div_factorial_le_exp W hW0 2
  norm_num at hexpQuad
  have hsecond : 8 * W + 6 ≤ X / 4000 := by
    rw [← hxexp]
    have hquad : 8 * W + 6 ≤ W ^ 2 / 8000 := by
      nlinarith [sq_nonneg (W - 100000)]
    exact hquad.trans (by nlinarith)
  dsimp [W] at hsecond
  linarith

/-- One explicit base threshold supplies the size, iterated-log and scalar
remainder margins used by every last-level cover cell. -/
theorem exists_sliceA2Cover_scalar_margins :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      12 ≤ Real.log (A1 : ℝ) ∧
      7 ≤ Real.log (Real.log (A1 : ℝ)) ∧
      (101 / 125 : ℝ) *
            (Real.log (A1 : ℝ)) ^ (1 / 3 : ℝ) +
          8 * Real.log (Real.log (A1 : ℝ)) + 6 ≤
            Real.log (A1 : ℝ) / 2000 := by
  let M : ℝ := 100000
  let A0 : ℕ := ⌈Real.exp (Real.exp M)⌉₊ + 1
  refine ⟨A0, fun A1 hA1 => ?_⟩
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by dsimp [A0] at hA1; omega)
  have hbase : Real.exp (Real.exp M) ≤ (A1 : ℝ) := by
    calc
      Real.exp (Real.exp M) ≤ (⌈Real.exp (Real.exp M)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (A1 : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) hA1)
  let X := Real.log (A1 : ℝ)
  have hX : Real.exp M ≤ X := by
    dsimp [X]
    exact (Real.le_log_iff_exp_le hA1pos).2 hbase
  have hX12 : (12 : ℝ) ≤ X := by
    calc
      (12 : ℝ) ≤ 1 + M := by norm_num [M]
      _ ≤ Real.exp M := by simpa [add_comm] using Real.add_one_le_exp M
      _ ≤ X := hX
  have hW : M ≤ Real.log X :=
    (Real.le_log_iff_exp_le (by linarith : 0 < X)).2 hX
  refine ⟨by simpa [X] using hX12, by simpa [X, M] using
    (show (7 : ℝ) ≤ Real.log X by dsimp [M] at hW; linarith), ?_⟩
  simpa [X, M] using sliceA2Cover_scalar_remainder X (by linarith)
    (by simpa [M] using hW)

end Tao2015

end MoltResearch
