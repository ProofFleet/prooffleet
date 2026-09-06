import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentLoss

/-!
# Track R A2-V': scalar exceptional damping margin

The damping gain has exponent `49/50 - 4/5 = 9/50`, whereas the adaptive
moment has exponent only `1/50`.  This leaf proves an explicit threshold at
which the remaining logarithm is absorbed by the positive `4/25` gap.
-/

namespace MoltResearch

namespace Tao2015

/-- Lower bounds for the anchor logarithm and upper bounds for the time
logarithm leave a `9/50`-power damping gain. -/
theorem exceptionalDamping_rpow_lower
    (X logP logT : ℝ) (hX : 1 ≤ X)
    (hP : X ^ (49 / 50 : ℝ) / 2 ≤ logP)
    (hT0 : 0 < logT) (hT : logT ≤ 3 * X) :
    X ^ (9 / 50 : ℝ) / 6 ≤ logP / logT ^ primeLargeValuesExponent := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have h3X0 : 0 ≤ 3 * X := by positivity
  have hpowT : logT ^ primeLargeValuesExponent ≤
      (3 * X) ^ primeLargeValuesExponent :=
    Real.rpow_le_rpow hT0.le hT (by norm_num [primeLargeValuesExponent])
  have hthree : (3 : ℝ) ^ primeLargeValuesExponent ≤ 3 := by
    calc
      (3 : ℝ) ^ primeLargeValuesExponent ≤ 3 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by norm_num [primeLargeValuesExponent])
      _ = 3 := by simp
  have hden : logT ^ primeLargeValuesExponent ≤
      3 * X ^ primeLargeValuesExponent := by
    calc
      logT ^ primeLargeValuesExponent ≤ (3 * X) ^ primeLargeValuesExponent := hpowT
      _ = 3 ^ primeLargeValuesExponent * X ^ primeLargeValuesExponent := by
        rw [Real.mul_rpow (by norm_num) hXpos.le]
      _ ≤ 3 * X ^ primeLargeValuesExponent := by gcongr
  have hprod : X ^ (9 / 50 : ℝ) * X ^ primeLargeValuesExponent =
      X ^ (49 / 50 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    norm_num [primeLargeValuesExponent]
  have hcross : X ^ (9 / 50 : ℝ) / 6 *
      logT ^ primeLargeValuesExponent ≤ logP := by
    calc
      X ^ (9 / 50 : ℝ) / 6 * logT ^ primeLargeValuesExponent ≤
          X ^ (9 / 50 : ℝ) / 6 *
            (3 * X ^ primeLargeValuesExponent) := by gcongr
      _ = X ^ (49 / 50 : ℝ) / 2 := by rw [← hprod]; ring
      _ ≤ logP := hP
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hT0 _)).2 hcross

/-- A concrete logarithmic threshold absorbs the complete coarse moment
loss into the `9/50` damping power. -/
theorem sliceA2ExceptionalMoment_scalar_margin
    (C X : ℝ) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (hlarge : 100 * (11880 * (C + 2)) ≤ Real.log X) :
    220 * (6 * X ^ (1 / 50 : ℝ) + 3) *
        (Real.log X + C + 1) ≤ X ^ (9 / 50 : ℝ) / 6 := by
  let W := Real.log X
  let K := 11880 * (C + 2)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hW1 : 1 ≤ W := by
    have hK : (1 : ℝ) ≤ 100 * K := by
      dsimp [K]
      nlinarith
    exact hK.trans (by simpa [W, K] using hlarge)
  have hx02 : 1 ≤ X ^ (1 / 50 : ℝ) :=
    Real.one_le_rpow hX (by norm_num)
  have hfirst : 6 * X ^ (1 / 50 : ℝ) + 3 ≤
      9 * X ^ (1 / 50 : ℝ) := by nlinarith
  have hsecond : W + C + 1 ≤ (C + 2) * W := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hW1)]
  have hKW : K * W ≤ W ^ 2 / 100 := by
    have hlarge' : 100 * K ≤ W := by simpa [W, K] using hlarge
    nlinarith [mul_nonneg hK0 (zero_le_one.trans hW1)]
  have hexpLower := Real.pow_div_factorial_le_exp
    ((4 / 25 : ℝ) * W) (by positivity) 2
  norm_num at hexpLower
  have hWsq : W ^ 2 / 100 ≤
      Real.exp ((4 / 25 : ℝ) * W) := by
    nlinarith [sq_nonneg W]
  have hx16 : Real.exp ((4 / 25 : ℝ) * W) =
      X ^ (4 / 25 : ℝ) := by
    dsimp [W]
    rw [Real.rpow_def_of_pos hXpos]
    congr 1
    ring
  have hgap : K * W ≤ X ^ (4 / 25 : ℝ) := by
    rw [← hx16]
    exact hKW.trans hWsq
  have hpowers : X ^ (1 / 50 : ℝ) * X ^ (4 / 25 : ℝ) =
      X ^ (9 / 50 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  calc
    220 * (6 * X ^ (1 / 50 : ℝ) + 3) * (Real.log X + C + 1) ≤
        220 * (9 * X ^ (1 / 50 : ℝ)) * ((C + 2) * W) := by
      dsimp [W]
      gcongr
    _ = (K * W * X ^ (1 / 50 : ℝ)) / 6 := by
      dsimp [K]
      ring
    _ ≤ (X ^ (4 / 25 : ℝ) * X ^ (1 / 50 : ℝ)) / 6 := by
      gcongr
    _ = X ^ (9 / 50 : ℝ) / 6 := by rw [mul_comm, hpowers]

/-- The scalar exceptional moment margin holds uniformly beyond a recorded
double-exponential base threshold. -/
theorem exists_sliceA2ExceptionalMoment_scalar_margin
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let X := Real.log (A1 : ℝ)
      1 ≤ X ∧
        220 * (6 * X ^ (1 / 50 : ℝ) + 3) *
          (Real.log X + C + 1) ≤ X ^ (9 / 50 : ℝ) / 6 := by
  let K := 11880 * (C + 2)
  let M := max 1 (100 * K)
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
  have hM0 : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  have hX1 : 1 ≤ X := (Real.one_le_exp hM0).trans hX
  have hlogX : M ≤ Real.log X :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans_le hX1)).2 hX
  have hlarge : 100 * (11880 * (C + 2)) ≤ Real.log X :=
    (le_max_right 1 (100 * K)).trans hlogX
  exact ⟨hX1, sliceA2ExceptionalMoment_scalar_margin C X hC hX1 (by
    simpa [K] using hlarge)⟩

end Tao2015

end MoltResearch
