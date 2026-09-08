import Conjectures.C0004_erdos461_smooth.src.ComponentGraph

/-!
# Erdős 461: a multiscale component-expansion interface

This file refines the open matching input from `Reduction.lean` into the
dyadic component-value expansion inequality described in
`Problems/erdos461_expansion.md`.  It does not prove that inequality.  The
only open input is isolated in `MultiscaleComponentExpansionAssumption`, and
the implication to `ProportionalComponentMatchingAssumption` is proved.
-/

namespace MoltResearch.Erdos461

open Finset

/-- The dyadic scale indices represented by smooth-component values in the
interval.  A positive value `S` has index `Nat.log2 S`. -/
noncomputable def componentValueScales (n t : ℕ) : Finset ℕ :=
  (componentValues n t).image Nat.log2

/-- The neighbours of `U` whose smooth-component values have dyadic index
`j`.  The value bands are disjoint because each component has one
`Nat.log2` index. -/
noncomputable def componentNeighborhoodAtScale (n t : ℕ) (U : Finset ℕ)
    (j : ℕ) : Finset ℕ :=
  (componentNeighborhood n t U).filter (fun S => Nat.log2 S = j)

/-- The component neighbourhood counted scale by scale. -/
noncomputable def multiscaleComponentNeighborhoodCard (n t : ℕ)
    (U : Finset ℕ) : ℕ :=
  ∑ j ∈ componentValueScales n t,
    (componentNeighborhoodAtScale n t U j).card

/-- Every component neighbour is one of the component values represented in
the interval. -/
theorem componentNeighborhood_subset_componentValues (n t : ℕ) (U : Finset ℕ) :
    componentNeighborhood n t U ⊆ componentValues n t := by
  classical
  intro S hS
  rw [componentNeighborhood, Finset.mem_biUnion] at hS
  obtain ⟨d, -, hSd⟩ := hS
  rw [componentNeighbors, Finset.mem_filter] at hSd
  exact hSd.1

/-- Summing the disjoint dyadic value bands counts the component
neighbourhood exactly.  In particular, the multiscale interface below does
not gain cardinality by counting one component at several scales. -/
theorem multiscaleComponentNeighborhoodCard_eq (n t : ℕ) (U : Finset ℕ) :
    multiscaleComponentNeighborhoodCard n t U =
      (componentNeighborhood n t U).card := by
  classical
  rw [multiscaleComponentNeighborhoodCard, componentValueScales]
  simp_rw [componentNeighborhoodAtScale]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro S hS
  exact Finset.mem_image.mpr
    ⟨S, componentNeighborhood_subset_componentValues n t U hS, rfl⟩

/-- The refined open input: after decomposing component values into dyadic
`Nat.log2` bands, every lower-half set has total neighbourhood large enough
for a matching of size `ceil(t / 4)`.

The subtraction is the finite defect-Hall slack.  No instance of this class
is declared; see `Problems/erdos461_expansion.md` for its status and the B6
obstruction checks.
-/
class MultiscaleComponentExpansionAssumption : Prop where
  defect_bound : ∀ n t : ℕ, 2 ≤ t → ∀ U ⊆ componentLeft t,
    U.card ≤ multiscaleComponentNeighborhoodCard n t U +
      ((componentLeft t).card - (t + 3) / 4)

private theorem quarterMatchingTarget_le_componentLeft_card (t : ℕ)
    (ht : 2 ≤ t) :
    (t + 3) / 4 ≤ (componentLeft t).card := by
  simp [componentLeft]
  omega

private theorem real_quarter_le_quarterMatchingTarget (t : ℕ) :
    (1 / 4 : ℝ) * t ≤ ((t + 3) / 4 : ℕ) := by
  have hround : t ≤ 4 * ((t + 3) / 4) := by omega
  have hround_real : (t : ℝ) ≤ 4 * (((t + 3) / 4 : ℕ) : ℝ) := by
    exact_mod_cast hround
  norm_num at hround_real ⊢
  linarith

/-- The multiscale defect inequality supplies a positive-proportion
component matching, with the explicit constant `1 / 4`. -/
theorem proportionalComponentMatchingAssumption_of_multiscale
    [h : MultiscaleComponentExpansionAssumption] :
    ProportionalComponentMatchingAssumption := by
  constructor
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro n t ht
  let q := (t + 3) / 4
  have hq : q ≤ (componentLeft t).card := by
    simpa [q] using quarterMatchingTarget_le_componentLeft_card t ht
  have hdefect : ∀ U ⊆ componentLeft t,
      U.card ≤ (componentNeighborhood n t U).card +
        ((componentLeft t).card - q) := by
    intro U hU
    simpa [q, multiscaleComponentNeighborhoodCard_eq] using
      h.defect_bound n t ht U hU
  obtain ⟨M, hM⟩ :=
    (exists_componentMatching_card_ge_iff_defectHall n t q hq).2 hdefect
  refine ⟨M, ?_⟩
  have hquarter : (1 / 4 : ℝ) * t ≤ (q : ℝ) := by
    simpa [q] using real_quarter_le_quarterMatchingTarget t
  have hMreal : (q : ℝ) ≤ M.domain.card := by
    exact_mod_cast hM
  exact hquarter.trans hMreal

/-- Consequently, the multiscale component-expansion assumption implies the
open Erdős 461 statement.  This remains a conditional theorem. -/
theorem erdos461_of_multiscaleComponentExpansion
    [MultiscaleComponentExpansionAssumption] : Erdos461 := by
  letI : ProportionalComponentMatchingAssumption :=
    proportionalComponentMatchingAssumption_of_multiscale
  exact erdos461_of_assumptions

end MoltResearch.Erdos461
