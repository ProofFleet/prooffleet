import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Levels

/-!
# Track R A2-V'-18: the exceptional interval stays below the window

The exceptional lower endpoint is an exponential of the sublinear power
`(log A1)^(49/50)`.  This leaf keeps the ceiling loss explicit and proves
that the fixed-ratio upper endpoint has square at most `A1` once the base
scale is large enough.
-/

namespace MoltResearch

namespace Tao2015

/-- The natural ceiling and the protective `max 3` cost at most a factor
four above the defining exponential. -/
theorem exceptionalPrimeLower_cast_le_four_exp
    (A1 : ℕ) (hA1 : 1 ≤ A1) :
    (exceptionalPrimeLower A1 : ℝ) ≤
      4 * Real.exp ((Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)) := by
  let x := (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)
  have hlog0 : 0 ≤ Real.log (A1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hA1)
  have hx0 : 0 ≤ x := Real.rpow_nonneg hlog0 _
  have hey1 : 1 ≤ Real.exp x := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hx0
  have hceil : (⌈Real.exp x⌉₊ : ℝ) ≤ 2 * Real.exp x := by
    calc
      (⌈Real.exp x⌉₊ : ℝ) ≤ Real.exp x + 1 :=
        (Nat.ceil_lt_add_one (Real.exp_nonneg x)).le
      _ ≤ Real.exp x + Real.exp x := add_le_add_right hey1 _
      _ = 2 * Real.exp x := by ring
  have hthree : (3 : ℝ) ≤ 4 * Real.exp x := by nlinarith
  have hceil' : (⌈Real.exp x⌉₊ : ℝ) ≤ 4 * Real.exp x :=
    hceil.trans (by nlinarith [Real.exp_pos x])
  unfold exceptionalPrimeLower
  rw [Nat.cast_max]
  exact max_le hthree hceil'

/-- A logarithmic margin is sufficient for the exceptional upper endpoint
to have square at most the base scale. -/
theorem exceptionalPrimeUpper_sq_le_of_log_margin
    (A1 : ℕ) (epsc : ℝ) (hA1 : 1 ≤ A1)
    (hmargin :
      2 * (exceptionalIntervalRatio epsc : ℝ) *
          (Real.log 4 +
            (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)) ≤
        Real.log (A1 : ℝ)) :
    exceptionalPrimeUpper A1 epsc ^ 2 ≤ A1 := by
  let x := (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)
  let R := exceptionalIntervalRatio epsc
  have hA1pos : (0 : ℝ) < A1 := by exact_mod_cast (show 0 < A1 by omega)
  have hlower0 : (0 : ℝ) ≤ exceptionalPrimeLower A1 := by positivity
  have hbase := exceptionalPrimeLower_cast_le_four_exp A1 hA1
  have hpow :
      (exceptionalPrimeLower A1 : ℝ) ^ (2 * R) ≤
        (4 * Real.exp x) ^ (2 * R) :=
    pow_le_pow_left₀ hlower0 hbase (2 * R)
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hrewrite : 4 * Real.exp x = Real.exp (Real.log 4 + x) := by
    rw [Real.exp_add, Real.exp_log hfour]
  have hexp : (4 * Real.exp x) ^ (2 * R) ≤ (A1 : ℝ) := by
    rw [hrewrite, ← Real.exp_nat_mul]
    calc
      Real.exp ((2 * R : ℕ) * (Real.log 4 + x)) ≤
          Real.exp (Real.log (A1 : ℝ)) := by
        rw [Real.exp_le_exp]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        simpa [x, R] using hmargin
      _ = (A1 : ℝ) := Real.exp_log hA1pos
  have hcast : (exceptionalPrimeUpper A1 epsc ^ 2 : ℕ) =
      exceptionalPrimeLower A1 ^ (2 * R) := by
    unfold exceptionalPrimeUpper R
    rw [← pow_mul]
    ring_nf
  rw [hcast]
  exact_mod_cast hpow.trans hexp

/-- For every fixed density parameter, the exceptional interval is
eventually contained below the square-root of the scale-window base. -/
theorem exists_exceptionalPrimeUpper_sq_le (epsc : ℝ) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      exceptionalPrimeUpper A1 epsc ^ 2 ≤ A1 := by
  let R : ℝ := exceptionalIntervalRatio epsc
  let M : ℝ := max 1 (max (8 * R * Real.log 4) ((4 * R) ^ 50))
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
    (le_max_left 1 (max (8 * R * Real.log 4) ((4 * R) ^ 50))).trans hXM
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hA1one : 1 ≤ A1 := by
    have : 1 < (A1 : ℝ) := by
      exact (Real.log_pos_iff hA1pos.le).mp hXpos
    exact_mod_cast this.le
  have hlinear : 8 * R * Real.log 4 ≤ X :=
    (le_max_left (8 * R * Real.log 4) ((4 * R) ^ 50)).trans
      ((le_max_right 1
        (max (8 * R * Real.log 4) ((4 * R) ^ 50))).trans hXM)
  have hpower : (4 * R) ^ 50 ≤ X :=
    (le_max_right (8 * R * Real.log 4) ((4 * R) ^ 50)).trans
      ((le_max_right 1
        (max (8 * R * Real.log 4) ((4 * R) ^ 50))).trans hXM)
  have hR0 : 0 ≤ 4 * R := by
    dsimp [R]
    positivity
  have hroot := Real.rpow_le_rpow (pow_nonneg hR0 50) hpower
    (by norm_num : (0 : ℝ) ≤ (50 : ℝ)⁻¹)
  have hRroot : 4 * R ≤ X ^ (1 / 50 : ℝ) := by
    calc
      4 * R = ((4 * R) ^ 50) ^ ((50 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hR0 (by norm_num : (50 : ℕ) ≠ 0)).symm
      _ ≤ X ^ ((50 : ℝ)⁻¹) := hroot
      _ = X ^ (1 / 50 : ℝ) := by norm_num
  have hsublinear :
      4 * R * X ^ (49 / 50 : ℝ) ≤ X := by
    calc
      4 * R * X ^ (49 / 50 : ℝ) ≤
          X ^ (1 / 50 : ℝ) * X ^ (49 / 50 : ℝ) := by
        gcongr
      _ = X ^ ((1 / 50 : ℝ) + 49 / 50) :=
        (Real.rpow_add hXpos (1 / 50 : ℝ) (49 / 50 : ℝ)).symm
      _ = X := by norm_num
  apply exceptionalPrimeUpper_sq_le_of_log_margin A1 epsc hA1one
  dsimp [R, X] at hlinear hsublinear ⊢
  linarith

end Tao2015

end MoltResearch
