import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZeroFrequency

/-!
# Track R A2-V': closed bottom-level schedule

The two level-zero numerical fits are now packaged behind one fixed lower
endpoint threshold and one explicit `T/A` margin.
-/

namespace MoltResearch

namespace Tao2015

/-- The exact pair of numerical hypotheses consumed by the instantiated
level-zero main theorem. -/
def SliceA2OrdinaryZeroFits
    (P0 ratio0 eta A : ℕ) (eps rho0 T : ℝ) : Prop :=
  (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
        (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
          Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
      (Real.exp Real.pi * Real.log 4 *
        ((2 * T * Real.exp
            (1 / ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ)) /
            (A : ℝ)) *
          ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^
              (1 - 2 * innerBandScheduleAlpha 0) *
            Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
              ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
          (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
              (1 - 2 * innerBandScheduleAlpha 0) + 1))) ≤
      sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) ∧
  (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
        (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
          Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
      (Real.exp Real.pi * Real.log 4 *
        (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
            (-(2 * innerBandScheduleAlpha 0)) *
          Real.exp (2 * innerBandScheduleAlpha 0 /
            ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
          (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
            (2 * innerBandScheduleAlpha 0) + 1))) ≤
      sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8)

/-- A fixed bottom threshold and the displayed height ratio close both
level-zero fits. -/
theorem exists_sliceA2Ordinary_zero_fits
    (ratio0 : ℕ) (eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ Pmin : ℕ, 3 ≤ Pmin ∧ ∀ P0 eta A : ℕ, ∀ T : ℝ,
      Pmin ≤ P0 → 1 ≤ A → 0 ≤ T →
      (T / (A : ℝ)) *
          sliceA2OrdinaryZeroFrequencyCoefficient
            P0 ratio0 eta eps rho0 ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) →
      SliceA2OrdinaryZeroFits P0 ratio0 eta A eps rho0 T := by
  obtain ⟨Pmin, hPmin, hprime⟩ :=
    exists_sliceA2Ordinary_zero_prime_fit ratio0 eps rho0 heps hrho0
  refine ⟨Pmin, hPmin, fun P0 eta A T hP0 hA hT hfrequency => ?_⟩
  have hP03 : 3 ≤ P0 := hPmin.trans hP0
  constructor
  · exact sliceA2Ordinary_zero_frequency_fit_of_ratio
      P0 ratio0 eta A eps rho0 T hP03 hA heps hrho0 hT hfrequency
  · exact hprime P0 eta hP0

end Tao2015

end MoltResearch
