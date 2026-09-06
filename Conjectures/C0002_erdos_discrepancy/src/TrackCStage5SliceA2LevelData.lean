import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Geometry

/-!
# Track R A2-V'-9: cell data for the two-ratio ladder

The final ladder differs from the L3 ladder only at level zero.  Its prime
intervals therefore need a small set of structural wrappers: Mertens mass,
cardinality and square-mass bounds, followed by the empty-cell-safe
representative data consumed by the shifted capstone.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Sharp upper Mertens bound for one level of the final ladder. -/
theorem sliceA2LadderPrimes_mass_le_mertens
    (P0 ratio0 eta j : ℕ) (hP0 : 3 ≤ P0) :
    ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j, (1 : ℝ) / p ≤
      Real.log (Real.log ((sliceA2LadderQ P0 ratio0 eta j : ℝ) + 1)) -
        Real.log (Real.log ((sliceA2LadderP P0 ratio0 eta j : ℝ) + 1)) + 12 := by
  apply prime_Ioc_mass_upper_mertens
  · exact hP0.trans (sliceA2LadderP_mono P0 ratio0 eta (by omega)
      (Nat.zero_le j))
  · exact sliceA2LadderP_le_Q P0 ratio0 eta j

theorem sliceA2LadderPrimes_card_le_Q (P0 ratio0 eta j : ℕ) :
    (sliceA2LadderPrimes P0 ratio0 eta j).card ≤
      sliceA2LadderQ P0 ratio0 eta j := by
  calc
    (sliceA2LadderPrimes P0 ratio0 eta j).card ≤
        (Finset.Ioc (sliceA2LadderP P0 ratio0 eta j)
          (sliceA2LadderQ P0 ratio0 eta j)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ sliceA2LadderQ P0 ratio0 eta j := by
      rw [Nat.card_Ioc]
      omega

/-- Elementary collision-mass bound for one final-ladder interval. -/
theorem sliceA2LadderPrimes_sq_mass_le_card
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) /
        (sliceA2LadderP P0 ratio0 eta j : ℝ) ^ 2 := by
  have hPj : (0 : ℝ) < sliceA2LadderP P0 ratio0 eta j := by
    exact_mod_cast (show 0 < sliceA2LadderP P0 ratio0 eta j by
      have := sliceA2LadderP_two_le P0 ratio0 eta j hP0
      omega)
  calc
    ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ _p ∈ sliceA2LadderPrimes P0 ratio0 eta j,
        (1 : ℝ) / (sliceA2LadderP P0 ratio0 eta j : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          apply one_div_le_one_div_of_le (by positivity)
          have hpP : (sliceA2LadderP P0 ratio0 eta j : ℝ) ≤ p := by
            exact_mod_cast
              (sliceA2LadderPrimes_bounds P0 ratio0 eta j p hp).1.le
          nlinarith
    _ = ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) /
        (sliceA2LadderP P0 ratio0 eta j : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Empty-cell-safe representative for the final ladder. -/
noncomputable def sliceA2LevelRepresentative
    (P0 ratio0 eta j N v : ℕ) : ℕ :=
  scaleCellRepresentative (sliceA2LadderPrimes P0 ratio0 eta j) N v

/-- All cell-cover and representative properties required by the shifted
wide capstone, specialized to a final-ladder prime interval. -/
theorem sliceA2Level_cell_data
    (P0 ratio0 eta j N : ℕ) (hP0 : 2 ≤ P0) (hN : 0 < N) :
    ((Finset.Ico
        (ordinaryLevelV0 (sliceA2LadderP P0 ratio0 eta j) N)
        (ordinaryLevelV1 (sliceA2LadderQ P0 ratio0 eta j) N + 1)).biUnion
      (eadicCell (sliceA2LadderPrimes P0 ratio0 eta j) (2 * N)) =
        sliceA2LadderPrimes P0 ratio0 eta j) ∧
    (∀ v ∈ Finset.Ico
        (ordinaryLevelV0 (sliceA2LadderP P0 ratio0 eta j) N)
        (ordinaryLevelV1 (sliceA2LadderQ P0 ratio0 eta j) N + 1),
      (sliceA2LevelRepresentative P0 ratio0 eta j N v : ℝ) ≤
        Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ)))) ∧
    (∀ v, 1 ≤ sliceA2LevelRepresentative P0 ratio0 eta j N v) ∧
    (∀ v ∈ Finset.Ico
        (ordinaryLevelV0 (sliceA2LadderP P0 ratio0 eta j) N)
        (ordinaryLevelV1 (sliceA2LadderQ P0 ratio0 eta j) N + 1),
      ∀ p ∈ eadicCell (sliceA2LadderPrimes P0 ratio0 eta j) (2 * N) v,
        sliceA2LevelRepresentative P0 ratio0 eta j N v ≤ p) ∧
    (∀ v ∈ Finset.Ico
        (ordinaryLevelV0 (sliceA2LadderP P0 ratio0 eta j) N)
        (ordinaryLevelV1 (sliceA2LadderQ P0 ratio0 eta j) N + 1),
      ∀ p ∈ eadicCell (sliceA2LadderPrimes P0 ratio0 eta j) (2 * N) v,
        N * p ≤ (N + 1) * sliceA2LevelRepresentative P0 ratio0 eta j N v) := by
  have hPj : 1 ≤ sliceA2LadderP P0 ratio0 eta j :=
    (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans' (by norm_num)
  have hprime : ∀ p ∈ sliceA2LadderPrimes P0 ratio0 eta j, p.Prime :=
    fun p hp => sliceA2LadderPrimes_prime P0 ratio0 eta j p hp
  have hone : ∀ p ∈ sliceA2LadderPrimes P0 ratio0 eta j, 1 ≤ p :=
    fun p hp => (hprime p hp).one_le
  constructor
  · simpa [ordinaryLevelV0, ordinaryLevelV1] using
      eadicCell_biUnion_Ico_eq (sliceA2LadderPrimes P0 ratio0 eta j) (2 * N)
        (sliceA2LadderP P0 ratio0 eta j) (sliceA2LadderQ P0 ratio0 eta j)
        (by omega : 0 < 2 * N) hPj
        (fun p hp => (sliceA2LadderPrimes_bounds P0 ratio0 eta j p hp).1)
        (fun p hp => (sliceA2LadderPrimes_bounds P0 ratio0 eta j p hp).2)
  constructor
  · intro v hv
    exact qup_of_ceil_or_one (sliceA2LadderPrimes P0 ratio0 eta j) N v hN hone
  constructor
  · intro v
    exact one_le_scaleCellRepresentative
      (sliceA2LadderPrimes P0 ratio0 eta j) N v
  constructor
  · intro v hv p hp
    exact scaleCellRepresentative_le_mem hN hp
      (hprime p (mem_eadicCell.mp hp).1).one_le
  · intro v hv p hp
    exact scaleCellRepresentative_ratio_le hN hp
      (hprime p (mem_eadicCell.mp hp).1).one_le

end Tao2015

end MoltResearch
