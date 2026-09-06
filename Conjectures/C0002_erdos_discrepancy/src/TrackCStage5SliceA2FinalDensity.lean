import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalScale

/-!
# Track R A2-V'-19: density in the final level order

The analytic density estimates are naturally proved with level zero and the
exceptional interval adjacent.  The final inner-band list has the ordinary
levels first.  This leaf combines the Brun ladder split with the exact
permutation between those two orders.
-/

namespace MoltResearch

namespace Tao2015

/-- Base and positive-ladder density estimates imply the complement-density
clause for the exact final list. -/
theorem sliceA2FinalLevels_density_of_bounds
    (P0 ratio0 eta A1 A : ℕ) (epsc epsBase epsLadder H : ℝ)
    (hP0 : 2 ≤ P0)
    (hbase :
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter
          (fun n ↦ ¬ HasFactorInAll
            [sliceA2LadderPrimes P0 ratio0 eta 0,
              exceptionalPrimes A1 epsc] n),
          (1 : ℝ) / n ≤ epsBase * H)
    (hladder :
      ladderSiftedLogMass A (2 * A)
        ((List.range (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1)).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        epsLadder * H) :
    ∑ n ∈ (Finset.Ioc A (2 * A)).filter
        (fun n ↦ ¬ HasFactorInAll
          (sliceA2FinalLevels P0 ratio0 eta A1 epsc hP0) n),
        (1 : ℝ) / n ≤ (epsBase + epsLadder) * H := by
  let base : List (Finset ℕ) :=
    [sliceA2LadderPrimes P0 ratio0 eta 0, exceptionalPrimes A1 epsc]
  let ladder : List (Finset ℕ) :=
    (List.range (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1)).map
      (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))
  have hsplit := typicalS_complement_append_le_of_bounds
    A (2 * A) base ladder epsBase epsLadder H hbase hladder
  calc
    ∑ n ∈ (Finset.Ioc A (2 * A)).filter
        (fun n ↦ ¬ HasFactorInAll
          (sliceA2FinalLevels P0 ratio0 eta A1 epsc hP0) n),
        (1 : ℝ) / n =
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter
        (fun n ↦ ¬ HasFactorInAll (base ++ ladder) n),
        (1 : ℝ) / n :=
      typicalS_complement_sum_perm A (2 * A)
        (sliceA2FinalLevels_perm_lowBand P0 ratio0 eta A1 epsc hP0)
    _ ≤ (epsBase + epsLadder) * H := hsplit

/-- The symmetric half-budget form used by `SliceMeanSquareA2`. -/
theorem sliceA2FinalLevels_density
    (P0 ratio0 eta A1 A : ℕ) (epsc H : ℝ)
    (hP0 : 2 ≤ P0)
    (hbase :
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter
          (fun n ↦ ¬ HasFactorInAll
            [sliceA2LadderPrimes P0 ratio0 eta 0,
              exceptionalPrimes A1 epsc] n),
          (1 : ℝ) / n ≤ (epsc / 2) * H)
    (hladder :
      ladderSiftedLogMass A (2 * A)
        ((List.range (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1)).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        (epsc / 2) * H) :
    ∑ n ∈ (Finset.Ioc A (2 * A)).filter
        (fun n ↦ ¬ HasFactorInAll
          (sliceA2FinalLevels P0 ratio0 eta A1 epsc hP0) n),
        (1 : ℝ) / n ≤ epsc * H := by
  convert sliceA2FinalLevels_density_of_bounds P0 ratio0 eta A1 A epsc
    (epsc / 2) (epsc / 2) H hP0 hbase hladder using 1 <;> ring

end Tao2015

end MoltResearch
