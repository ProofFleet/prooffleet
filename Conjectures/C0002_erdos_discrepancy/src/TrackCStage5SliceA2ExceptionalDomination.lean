import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BaseDensity

/-!
# Track R A2-V'-22: exceptional endpoint power domination

The earlier square bound is enough for support.  Density errors and collar
terms need the stronger eventual statement `C * Q_U^m <= A1` for arbitrary
fixed `C` and positive natural `m`.  The same `49/50` margin proves it.
-/

namespace MoltResearch

namespace Tao2015

/-- A displayed logarithmic margin implies a fixed-power endpoint bound. -/
theorem const_mul_exceptionalPrimeUpper_pow_le_of_log_margin
    (C : ℝ) (m A1 : ℕ) (epsc : ℝ)
    (hC : 0 < C) (hA1 : 1 ≤ A1)
    (hmargin :
      Real.log C +
          (m : ℝ) * (exceptionalIntervalRatio epsc : ℝ) *
            (Real.log 4 +
              (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)) ≤
        Real.log (A1 : ℝ)) :
    C * (exceptionalPrimeUpper A1 epsc : ℝ) ^ m ≤ A1 := by
  let x := (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)
  let R := exceptionalIntervalRatio epsc
  have hA1pos : (0 : ℝ) < A1 := by exact_mod_cast (show 0 < A1 by omega)
  have hlower0 : (0 : ℝ) ≤ exceptionalPrimeLower A1 := by positivity
  have hbase := exceptionalPrimeLower_cast_le_four_exp A1 hA1
  have hupper : (exceptionalPrimeUpper A1 epsc : ℝ) ≤
      (4 * Real.exp x) ^ R := by
    unfold exceptionalPrimeUpper
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ hlower0 hbase R
  have hupper0 : (0 : ℝ) ≤ exceptionalPrimeUpper A1 epsc := by positivity
  have hpow : (exceptionalPrimeUpper A1 epsc : ℝ) ^ m ≤
      ((4 * Real.exp x) ^ R) ^ m :=
    pow_le_pow_left₀ hupper0 hupper m
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hrewrite : 4 * Real.exp x = Real.exp (Real.log 4 + x) := by
    rw [Real.exp_add, Real.exp_log hfour]
  calc
    C * (exceptionalPrimeUpper A1 epsc : ℝ) ^ m ≤
        C * ((4 * Real.exp x) ^ R) ^ m :=
      mul_le_mul_of_nonneg_left hpow hC.le
    _ = Real.exp (Real.log C +
        (m : ℝ) * (R : ℝ) * (Real.log 4 + x)) := by
      rw [hrewrite, ← pow_mul, ← Real.exp_nat_mul]
      calc
        C * Real.exp ((R * m : ℕ) * (Real.log 4 + x)) =
            Real.exp (Real.log C) *
              Real.exp ((R * m : ℕ) * (Real.log 4 + x)) := by
          rw [Real.exp_log hC]
        _ = Real.exp (Real.log C +
            ((R * m : ℕ) : ℝ) * (Real.log 4 + x)) :=
          (Real.exp_add _ _).symm
        _ = Real.exp (Real.log C +
            (m : ℝ) * (R : ℝ) * (Real.log 4 + x)) := by
          congr 2
          push_cast
          ring
    _ ≤ Real.exp (Real.log (A1 : ℝ)) := by
      rw [Real.exp_le_exp]
      simpa [x, R] using hmargin
    _ = (A1 : ℝ) := Real.exp_log hA1pos

/-- Every fixed positive multiple and fixed positive power of the exceptional
upper endpoint is eventually below the scale-window base. -/
theorem exists_const_mul_exceptionalPrimeUpper_pow_le
    (C : ℝ) (m : ℕ) (epsc : ℝ) (hC : 0 < C) (hm : 0 < m) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      C * (exceptionalPrimeUpper A1 epsc : ℝ) ^ m ≤ A1 := by
  let R : ℝ := exceptionalIntervalRatio epsc
  let D : ℝ := (m : ℝ) * R
  let L : ℝ :=
    2 * (max 0 (Real.log C) + D * Real.log 4)
  let M : ℝ := max 1 (max L ((2 * D) ^ 50))
  let A0 := ⌈Real.exp M⌉₊ + 1
  refine ⟨A0, fun A1 hA1 ↦ ?_⟩
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by dsimp [A0] at hA1; omega)
  have hExpM : Real.exp M ≤ (A1 : ℝ) := by
    calc
      Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (A1 : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ ⌈Real.exp M⌉₊) hA1)
  have hXM : M ≤ Real.log (A1 : ℝ) := by
    calc
      M = Real.log (Real.exp M) := (Real.log_exp M).symm
      _ ≤ Real.log (A1 : ℝ) :=
        Real.log_le_log (Real.exp_pos M) hExpM
  let X := Real.log (A1 : ℝ)
  have hX1 : 1 ≤ X :=
    (le_max_left 1 (max L ((2 * D) ^ 50))).trans hXM
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hA1one : 1 ≤ A1 := by
    exact_mod_cast ((Real.log_pos_iff hA1pos.le).mp hXpos).le
  have hlinear : L ≤ X :=
    (le_max_left L ((2 * D) ^ 50)).trans
      ((le_max_right 1 (max L ((2 * D) ^ 50))).trans hXM)
  have hpower : (2 * D) ^ 50 ≤ X :=
    (le_max_right L ((2 * D) ^ 50)).trans
      ((le_max_right 1 (max L ((2 * D) ^ 50))).trans hXM)
  have hD0 : 0 ≤ D := by
    dsimp [D, R]
    positivity
  have hroot := Real.rpow_le_rpow (pow_nonneg (mul_nonneg (by norm_num) hD0) 50)
    hpower (by norm_num : (0 : ℝ) ≤ (50 : ℝ)⁻¹)
  have hDroot : 2 * D ≤ X ^ (1 / 50 : ℝ) := by
    calc
      2 * D = ((2 * D) ^ 50) ^ ((50 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (mul_nonneg (by norm_num) hD0)
          (by norm_num : (50 : ℕ) ≠ 0)).symm
      _ ≤ X ^ ((50 : ℝ)⁻¹) := hroot
      _ = X ^ (1 / 50 : ℝ) := by norm_num
  have hsublinear :
      2 * D * X ^ (49 / 50 : ℝ) ≤ X := by
    calc
      2 * D * X ^ (49 / 50 : ℝ) ≤
          X ^ (1 / 50 : ℝ) * X ^ (49 / 50 : ℝ) := by
        gcongr
      _ = X ^ ((1 / 50 : ℝ) + 49 / 50) :=
        (Real.rpow_add hXpos (1 / 50 : ℝ) (49 / 50 : ℝ)).symm
      _ = X := by norm_num
  have hlogC : Real.log C ≤ max 0 (Real.log C) := le_max_right _ _
  apply const_mul_exceptionalPrimeUpper_pow_le_of_log_margin
    C m A1 epsc hC hA1one
  dsimp [D, R, L, X] at hlinear hsublinear ⊢
  linarith

end Tao2015

end MoltResearch
