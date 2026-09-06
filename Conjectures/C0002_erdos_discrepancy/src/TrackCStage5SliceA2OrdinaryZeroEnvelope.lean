import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryWideClose

/-!
# Track R A2-V': fixed bottom-level envelopes

The logarithmic length of the bottom prime interval depends only on the
density ratio.  Consequently its cell resolution is bounded independently
of the freely enlarged lower endpoint `P0`.
-/

namespace MoltResearch

namespace Tao2015

/-- Fixed Mertens envelope for the bottom ordinary interval. -/
noncomputable def sliceA2OrdinaryZeroMassBound (ratio0 : ℕ) : ℝ :=
  Real.log (max 2 ratio0 : ℝ) + 12

/-- Fixed upper bound for the bottom ordinary resolution. -/
noncomputable def sliceA2OrdinaryZeroNBound
    (ratio0 : ℕ) (eps rho0 : ℝ) : ℝ :=
  3 + sliceA2CoverCellCoefficient eps rho0 *
    sliceA2OrdinaryZeroMassBound ratio0

/-- The bottom Mertens envelope is controlled only by its fixed logarithmic
ratio. -/
theorem sliceA2LevelMass_zero_le_ratio_bound
    (P0 ratio0 eta : ℕ) (hP0 : 3 ≤ P0) :
    sliceA2LevelMass P0 ratio0 eta 0 ≤
      sliceA2OrdinaryZeroMassBound ratio0 := by
  let P := P0
  let R := max 2 ratio0
  have hP : 3 ≤ P := by simpa [P] using hP0
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPaddpos : (0 : ℝ) < P + 1 := by positivity
  have hlogPadd : 0 < Real.log ((P : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < P + 1 by omega))
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hnat : P ^ R + 1 ≤ (P + 1) ^ R := by
    exact Nat.succ_le_iff.mpr (Nat.pow_lt_pow_left (by omega) (by omega))
  have hlog0 :
      Real.log (((P ^ R : ℕ) : ℝ) + 1) ≤
        (R : ℝ) * Real.log ((P : ℝ) + 1) := by
    calc
      Real.log (((P ^ R : ℕ) : ℝ) + 1) ≤
          Real.log ((((P + 1) ^ R : ℕ) : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hnat
      _ = (R : ℝ) * Real.log ((P : ℝ) + 1) := by
        rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow]
  have hloglog :
      Real.log (Real.log (((P ^ R : ℕ) : ℝ) + 1)) ≤
        Real.log ((R : ℝ) * Real.log ((P : ℝ) + 1)) := by
    apply Real.log_le_log
    · exact Real.log_pos (by
        have hpPow : (0 : ℝ) < ((P ^ R : ℕ) : ℝ) := by
          exact_mod_cast (pow_pos (show 0 < P by omega) R)
        linarith)
    · exact hlog0
  rw [Real.log_mul hRpos.ne' hlogPadd.ne'] at hloglog
  have hbound :
      Real.log (Real.log (((P ^ R : ℕ) : ℝ) + 1)) -
          Real.log (Real.log ((P : ℝ) + 1)) + 12 ≤
        Real.log (R : ℝ) + 12 := by
    linarith
  have hzero : (0 : ℝ) ≤ Real.log (R : ℝ) + 12 := by
    have : 0 ≤ Real.log (R : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hR)
    linarith
  unfold sliceA2LevelMass sliceA2OrdinaryZeroMassBound
  simp only [sliceA2LadderP_zero, sliceA2LadderQ_eq,
    sliceA2LadderRatio_zero]
  simpa [P, R, Nat.cast_max] using (max_le hzero hbound)

/-- The bottom resolution is a fixed function of the two requested
accuracies and of the bottom density ratio. -/
theorem sliceA2OrdinaryN_zero_le_fixed
    (P0 ratio0 eta : ℕ) (eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) ≤
      sliceA2OrdinaryZeroNBound ratio0 eps rho0 := by
  have hN := sliceA2OrdinaryN_le_cellCoefficient
    P0 ratio0 eta 0 eps rho0 heps hrho0
  have hmass := sliceA2LevelMass_zero_le_ratio_bound P0 ratio0 eta hP0
  calc
    (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) ≤
        3 + sliceA2CoverCellCoefficient eps rho0 *
          sliceA2LevelMass P0 ratio0 eta 0 * (2 ^ 0 : ℕ) := hN
    _ ≤ 3 + sliceA2CoverCellCoefficient eps rho0 *
          sliceA2OrdinaryZeroMassBound ratio0 := by
      have hC : 0 ≤ sliceA2CoverCellCoefficient eps rho0 := by
        unfold sliceA2CoverCellCoefficient
        positivity
      norm_num only [pow_zero, Nat.cast_one, mul_one]
      gcongr
    _ = sliceA2OrdinaryZeroNBound ratio0 eps rho0 := rfl

theorem sliceA2OrdinaryZeroNBound_pos
    (ratio0 : ℕ) (eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2OrdinaryZeroNBound ratio0 eps rho0 := by
  unfold sliceA2OrdinaryZeroNBound sliceA2CoverCellCoefficient
    sliceA2OrdinaryZeroMassBound
  have hR : (1 : ℝ) ≤ max 2 (ratio0 : ℝ) := by
    exact le_trans (by norm_num) (le_max_left _ _)
  have hlog : 0 ≤ Real.log (max 2 ratio0 : ℝ) := Real.log_nonneg hR
  positivity

end Tao2015

end MoltResearch
