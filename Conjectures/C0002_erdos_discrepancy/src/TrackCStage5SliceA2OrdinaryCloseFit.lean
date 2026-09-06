import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryCloseGrowth

/-!
# Track R A2-V': closed ordinary not-too-close fit

The exact coefficient below records the full margin.  One twentieth-power
absorbs its `2^(36j)` growth, a second absorbs `(log Q)^6`, and the original
`Q^(-9/20)` saving leaves `Q^(-7/20) ≤ 1`.
-/

namespace MoltResearch

namespace Tao2015

/-- Fixed coefficient whose twentieth power is imposed at the bottom
ordinary endpoint. -/
noncomputable def sliceA2OrdinaryCloseCoefficient
    (ratio0 eta : ℕ) (eps rho0 : ℝ) : ℝ :=
  max 1
    (1024 * sliceA2OrdinaryCellCountCoefficient eps rho0 ^ 3 * Real.exp 17 *
      sliceA2OrdinaryFarCoefficient ratio0 eta ^ 8 /
        (3 * eps ^ 2 * rho0))

theorem sliceA2OrdinaryCloseCoefficient_one_le
    (ratio0 eta : ℕ) (eps rho0 : ℝ) :
    1 ≤ sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 := by
  unfold sliceA2OrdinaryCloseCoefficient
  exact le_max_left _ _

theorem sliceA2OrdinaryCloseCoefficient_raw_le
    (ratio0 eta : ℕ) (eps rho0 : ℝ) :
    1024 * sliceA2OrdinaryCellCountCoefficient eps rho0 ^ 3 * Real.exp 17 *
        sliceA2OrdinaryFarCoefficient ratio0 eta ^ 8 /
          (3 * eps ^ 2 * rho0) ≤
      sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 := by
  unfold sliceA2OrdinaryCloseCoefficient
  exact le_max_right _ _

/-- The completely exposed close-scale envelope fits the exact ordinary
main-leg allocation. -/
theorem sliceA2Ordinary_close_envelope_fit
    (P0 ratio0 eta j Qlog0 : ℕ) (eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hj : 0 < j)
    (heps : 0 < eps) (hrho0 : 0 < rho0)
    (hlogThreshold : Qlog0 ≤
      sliceA2LadderQ P0 ratio0 eta (j - 1))
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hbottom :
      sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 ^ 20 *
          (2 : ℝ) ^ 720 ≤ P0) :
    let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
    let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
    sliceA2OrdinaryCellCountCoefficient eps rho0 ^ 3 * Real.exp 17 *
        (2 : ℝ) ^ (3 * j) * L ^ 8 * Real.log (Qprev : ℝ) ^ 6 *
        (Qprev : ℝ) ^ (-(9 : ℝ) / 20) ≤
      ordinaryLegShare j * eps ^ 2 * rho0 / 8 := by
  dsimp only
  let C := sliceA2OrdinaryCellCountCoefficient eps rho0
  let F := sliceA2OrdinaryFarCoefficient ratio0 eta
  let D := sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0
  let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  have hC0 : 0 ≤ C :=
    (sliceA2OrdinaryCellCountCoefficient_pos eps rho0 heps hrho0).le
  have hF0 : 0 ≤ F := by dsimp [F, sliceA2OrdinaryFarCoefficient]; positivity
  have hL0 : 0 ≤ L :=
    zero_le_one.trans (sliceA2OrdinaryMomentEnvelope_one_le ratio0 eta j)
  have hQ3 : 3 ≤ Qprev :=
    hP0.trans ((sliceA2LadderP_mono P0 ratio0 eta (by omega))
      (Nat.zero_le (j - 1))) |>.trans
      (sliceA2LadderP_le_Q P0 ratio0 eta (j - 1))
  have hQ1 : (1 : ℝ) ≤ Qprev := by exact_mod_cast (show 1 ≤ Qprev by omega)
  have hQ0 : (0 : ℝ) ≤ Qprev := zero_le_one.trans hQ1
  have hlog0 : 0 ≤ Real.log (Qprev : ℝ) := Real.log_nonneg hQ1
  have hL := sliceA2OrdinaryMomentEnvelope_le_farCoefficient ratio0 eta j hj
  have hLpow : L ^ 8 ≤ (F * (16 : ℝ) ^ j) ^ 8 :=
    pow_le_pow_left₀ hL0 (by simpa [L, F] using hL) 8
  have hcostShape :
      C ^ 3 * Real.exp 17 * (2 : ℝ) ^ (3 * j) *
          (F * (16 : ℝ) ^ j) ^ 8 =
        C ^ 3 * Real.exp 17 * F ^ 8 * (2 : ℝ) ^ (35 * j) := by
    have h16 : ((16 : ℝ) ^ j) ^ 8 = (2 : ℝ) ^ (32 * j) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]
      congr 1 <;> omega
    calc
      C ^ 3 * Real.exp 17 * (2 : ℝ) ^ (3 * j) *
          (F * (16 : ℝ) ^ j) ^ 8 =
        C ^ 3 * Real.exp 17 * F ^ 8 *
          ((2 : ℝ) ^ (3 * j) * (2 : ℝ) ^ (32 * j)) := by
            rw [mul_pow, h16]
            ring
      _ = C ^ 3 * Real.exp 17 * F ^ 8 * (2 : ℝ) ^ (35 * j) := by
        rw [← pow_add, show 3 * j + 32 * j = 35 * j by omega]
  have hrawD := sliceA2OrdinaryCloseCoefficient_raw_le ratio0 eta eps rho0
  have hrawD' : 1024 * C ^ 3 * Real.exp 17 * F ^ 8 /
      (3 * eps ^ 2 * rho0) ≤ D := by simpa [C, F, D] using hrawD
  have hDgrowth := sliceA2Ordinary_exponential_cost_le_twentieth_rpow
    P0 ratio0 eta j D (by omega) hj
      (sliceA2OrdinaryCloseCoefficient_one_le ratio0 eta eps rho0)
      (by simpa [D] using hbottom)
  have hlog := hlogFit Qprev hlogThreshold
  have hnormalized :
      C ^ 3 * Real.exp 17 * F ^ 8 * (2 : ℝ) ^ (35 * j) =
        (ordinaryLegShare j * eps ^ 2 * rho0 / 8) *
          (1024 * C ^ 3 * Real.exp 17 * F ^ 8 /
            (3 * eps ^ 2 * rho0)) * (2 : ℝ) ^ (36 * j) := by
    unfold ordinaryLegShare
    rw [show j + 1 = j + 1 by rfl, pow_succ]
    field_simp
    ring_nf
  have hdecay :
      (Qprev : ℝ) ^ (1 / 20 : ℝ) *
          (Qprev : ℝ) ^ (1 / 20 : ℝ) *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) ≤ 1 := by
    have hQpos : (0 : ℝ) < Qprev := zero_lt_one.trans_le hQ1
    rw [← Real.rpow_add hQpos, ← Real.rpow_add hQpos]
    convert Real.rpow_le_one_of_one_le_of_nonpos hQ1
      (by norm_num : (1 / 20 : ℝ) + 1 / 20 + -(9 / 20) ≤ 0) using 1 <;>
      norm_num
  have hshare0 : 0 ≤ ordinaryLegShare j * eps ^ 2 * rho0 / 8 := by
    unfold ordinaryLegShare
    positivity
  have hrawGrowth :
      (1024 * C ^ 3 * Real.exp 17 * F ^ 8 /
          (3 * eps ^ 2 * rho0)) * (2 : ℝ) ^ (36 * j) ≤
        D * (2 : ℝ) ^ (36 * j) :=
    mul_le_mul_of_nonneg_right hrawD' (by positivity)
  have hlogPow0 : 0 ≤ Real.log (Qprev : ℝ) ^ 6 := pow_nonneg hlog0 6
  have hQpow0 : 0 ≤ (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by positivity
  have hproduct :
      (D * (2 : ℝ) ^ (36 * j)) * Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) ≤
        (Qprev : ℝ) ^ (1 / 20 : ℝ) *
          (Qprev : ℝ) ^ (1 / 20 : ℝ) *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hDgrowth hlog hlogPow0 (by positivity)) hQpow0
  calc
    C ^ 3 * Real.exp 17 * (2 : ℝ) ^ (3 * j) * L ^ 8 *
          Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) ≤
        C ^ 3 * Real.exp 17 * (2 : ℝ) ^ (3 * j) *
          (F * (16 : ℝ) ^ j) ^ 8 * Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by gcongr
    _ = C ^ 3 * Real.exp 17 * F ^ 8 * (2 : ℝ) ^ (35 * j) *
          Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by rw [hcostShape]
    _ = (ordinaryLegShare j * eps ^ 2 * rho0 / 8) *
          (1024 * C ^ 3 * Real.exp 17 * F ^ 8 /
            (3 * eps ^ 2 * rho0)) * (2 : ℝ) ^ (36 * j) *
          Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by rw [hnormalized]
    _ ≤ (ordinaryLegShare j * eps ^ 2 * rho0 / 8) *
          (D * (2 : ℝ) ^ (36 * j)) *
          Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by
      have h₁ := mul_le_mul_of_nonneg_left hrawGrowth hshare0
      have h₂ := mul_le_mul_of_nonneg_right h₁ hlogPow0
      have h₃ := mul_le_mul_of_nonneg_right h₂ hQpow0
      simpa only [mul_assoc] using h₃
    _ ≤ (ordinaryLegShare j * eps ^ 2 * rho0 / 8) *
          ((Qprev : ℝ) ^ (1 / 20 : ℝ) *
            (Qprev : ℝ) ^ (1 / 20 : ℝ) *
            (Qprev : ℝ) ^ (-(9 : ℝ) / 20)) :=
      by simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hproduct hshare0)
    _ ≤ (ordinaryLegShare j * eps ^ 2 * rho0 / 8) * 1 :=
      mul_le_mul_of_nonneg_left hdecay hshare0
    _ = ordinaryLegShare j * eps ^ 2 * rho0 / 8 := by ring

end Tao2015

end MoltResearch
