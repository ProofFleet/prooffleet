import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2EndpointDensity

/-!
# Track R A2-V'-25: the final density window

The endpoint pair now has a uniform three-quarter density allocation.  This
leaf combines it with the remaining one-quarter Brun bound for the positive
ordinary ladder and returns the exact final level-list clause.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Once the positive ladder occupies its one-quarter allocation, the exact
final level list satisfies the `SliceMeanSquareA2` density clause. -/
theorem exists_sliceA2FinalLevels_density_of_ladder
    (P0 eta : ℕ) (epsc : ℝ) (hP0 : 3 ≤ P0) (hepsc : 0 < epsc) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ A : ℕ, A1 ≤ A →
      ladderSiftedLogMass A (2 * A)
          ((List.range
            (sliceA2LadderJ P0 (exceptionalIntervalRatio epsc) eta A1
              (by omega) - 1)).map
            (fun i ↦ sliceA2LadderPrimes P0
              (exceptionalIntervalRatio epsc) eta (i + 1))) ≤
        (epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n →
      ∑ n ∈ (Ioc A (2 * A)).filter
          (fun n ↦ ¬ HasFactorInAll
            (sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc) eta A1
              epsc (by omega)) n),
          (1 : ℝ) / n ≤
        epsc * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n := by
  obtain ⟨A0, hA0⟩ :=
    exists_sliceA2_bottom_exceptional_density P0 eta epsc hP0 hepsc
  refine ⟨A0, fun A1 hA1 A hAA1 hladder ↦ ?_⟩
  have hbase := (hA0 A1 hA1 A hAA1).1
  have hfinal := sliceA2FinalLevels_density_of_bounds P0
    (exceptionalIntervalRatio epsc) eta A1 A epsc
    (3 * epsc / 4) (epsc / 4)
    (∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n)
    (by omega) hbase hladder
  convert hfinal using 1 <;> ring

end Tao2015

end MoltResearch
