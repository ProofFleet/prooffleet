import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2InnerSchedule

/-!
# Track R A2-V': concrete ordinary schedule data

The final two-ratio ladder now receives its actual Mertens mass envelope,
cell resolution, index range and empty-cell-safe representatives.  The two
wide legs are reduced to the finite scale inequalities which are eventually
paid by the window base.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Nonnegative Mertens envelope for one ordinary ladder level. -/
noncomputable def sliceA2LevelMass
    (P0 ratio0 eta j : ℕ) : ℝ :=
  max 0
    (Real.log (Real.log ((sliceA2LadderQ P0 ratio0 eta j : ℝ) + 1)) -
      Real.log (Real.log ((sliceA2LadderP P0 ratio0 eta j : ℝ) + 1)) + 12)

theorem sliceA2LevelMass_nonneg (P0 ratio0 eta j : ℕ) :
    0 ≤ sliceA2LevelMass P0 ratio0 eta j := by
  exact le_max_left _ _

/-- The literal prime mass is bounded by the chosen nonnegative envelope. -/
theorem sliceA2LadderPrimes_mass_le_levelMass
    (P0 ratio0 eta j : ℕ) (hP0 : 3 ≤ P0) :
    ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j, (1 : ℝ) / p ≤
      sliceA2LevelMass P0 ratio0 eta j := by
  exact (sliceA2LadderPrimes_mass_le_mertens P0 ratio0 eta j hP0).trans
    (le_max_right _ _)

/-- Resolution of the `j`-th ordinary level at relative budget floor
`rho0`. -/
noncomputable def sliceA2OrdinaryN
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) : ℕ :=
  sliceA2LevelN (sliceA2LevelMass P0 ratio0 eta j)
    (sliceA2KappaReplacement j) 1 eps rho0

noncomputable def sliceA2OrdinaryV0
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) : ℕ :=
  ordinaryLevelV0 (sliceA2LadderP P0 ratio0 eta j)
    (sliceA2OrdinaryN P0 ratio0 eta j eps rho0)

noncomputable def sliceA2OrdinaryV1
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) : ℕ :=
  ordinaryLevelV1 (sliceA2LadderQ P0 ratio0 eta j)
    (sliceA2OrdinaryN P0 ratio0 eta j eps rho0)

noncomputable def sliceA2OrdinaryRepresentative
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (v : ℕ) : ℕ :=
  sliceA2LevelRepresentative P0 ratio0 eta j
    (sliceA2OrdinaryN P0 ratio0 eta j eps rho0) v

theorem sliceA2OrdinaryN_pos
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) :
    0 < sliceA2OrdinaryN P0 ratio0 eta j eps rho0 := by
  have := sliceA2LevelN_two_le (sliceA2LevelMass P0 ratio0 eta j)
    (sliceA2KappaReplacement j) 1 eps rho0
  simpa [sliceA2OrdinaryN] using (show 0 <
    sliceA2LevelN (sliceA2LevelMass P0 ratio0 eta j)
      (sliceA2KappaReplacement j) 1 eps rho0 by omega)

/-- The complete ordinary cell interface in the notation used by the final
schedule. -/
theorem sliceA2Ordinary_cell_data
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0) :
    ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).biUnion
      (eadicCell (sliceA2LadderPrimes P0 ratio0 eta j)
        (2 * sliceA2OrdinaryN P0 ratio0 eta j eps rho0)) =
        sliceA2LadderPrimes P0 ratio0 eta j) ∧
    (∀ v ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      (sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v : ℝ) ≤
        Real.exp (((v : ℝ) + 1) /
          (2 * (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ)))) ∧
    (∀ v, 1 ≤ sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v) ∧
    (∀ v ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      ∀ p ∈ eadicCell (sliceA2LadderPrimes P0 ratio0 eta j)
          (2 * sliceA2OrdinaryN P0 ratio0 eta j eps rho0) v,
        sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v ≤ p) ∧
    (∀ v ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      ∀ p ∈ eadicCell (sliceA2LadderPrimes P0 ratio0 eta j)
          (2 * sliceA2OrdinaryN P0 ratio0 eta j eps rho0) v,
        sliceA2OrdinaryN P0 ratio0 eta j eps rho0 * p ≤
          (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 + 1) *
            sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v) := by
  simpa [sliceA2OrdinaryV0, sliceA2OrdinaryV1, sliceA2OrdinaryRepresentative]
    using sliceA2Level_cell_data P0 ratio0 eta j
      (sliceA2OrdinaryN P0 ratio0 eta j eps rho0) hP0
      (sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0)

/-- The chosen resolution closes the replacement leg once the finite
cardinality-over-scale term has entered its half allocation. -/
theorem sliceA2Ordinary_replacement_fit
    (P0 ratio0 eta j A : ℕ) (eps rho0 rho T : ℝ)
    (hP0 : 3 ≤ P0) (hA : 2 ≤ A) (hTA : T ≤ A)
    (heps : 0 < eps) (hrho0 : 0 < rho0) (hratio : rho0 ≤ rho)
    (hcard : 64 * 9 * Real.exp Real.pi *
        (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
      sliceA2KappaReplacement j * eps ^ 2 * rho0 / 16) :
    2 * replacementEnergyBoundWide A
        (sliceA2LadderPrimes P0 ratio0 eta j)
        (sliceA2OrdinaryN P0 ratio0 eta j eps rho0) T ≤
      sliceA2KappaReplacement j * bandBudget 1 eps rho := by
  apply sliceA2_replacement_fit A
    (sliceA2LadderPrimes P0 ratio0 eta j) T
    (sliceA2LevelMass P0 ratio0 eta j) (sliceA2KappaReplacement j)
    1 eps rho0 rho hA hTA
    (sliceA2LadderPrimes_mass_le_levelMass P0 ratio0 eta j hP0)
    (sliceA2LevelMass_nonneg P0 ratio0 eta j)
  · exact (sliceA2Kappa_nonneg j).2.1.lt_of_ne' (by
      unfold sliceA2KappaReplacement ordinaryLegShare
      positivity)
  · norm_num
  · exact heps
  · exact hrho0
  · exact hratio
  · simpa [sliceA2OrdinaryN] using hcard

/-- The elementary square-mass estimate closes the collision leg once its
remaining finite scale inequality is available. -/
theorem sliceA2Ordinary_collision_fit
    (P0 ratio0 eta j A : ℕ) (eps rho0 rho T : ℝ)
    (hP0 : 2 ≤ P0) (hA : 2 ≤ A) (hTA : T ≤ A)
    (hratio : rho0 ≤ rho)
    (hfit : 40 * Real.exp Real.pi *
        (2 * (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) /
            (sliceA2LadderP P0 ratio0 eta j : ℝ) ^ 2) +
          ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
      sliceA2KappaCollision j * (eps ^ 2 * rho0 / 8)) :
    8 * collisionEnergyBoundWide A
        (sliceA2LadderPrimes P0 ratio0 eta j) T ≤
      sliceA2KappaCollision j * bandBudget 1 eps rho := by
  apply collisionEnergyBoundWide_fit_of_mass_card_ratio A
    (sliceA2LadderPrimes P0 ratio0 eta j) T
    (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) /
      (sliceA2LadderP P0 ratio0 eta j : ℝ) ^ 2)
    (sliceA2KappaCollision j) 1 eps rho0 rho hA hTA
    (sliceA2LadderPrimes_sq_mass_le_card P0 ratio0 eta j hP0)
  · simpa only [one_mul] using hfit
  · norm_num
  · exact (sliceA2Kappa_nonneg j).2.2
  · exact hratio

end Tao2015

end MoltResearch
