import Conjectures.C0004_erdos461_smooth.src.Expansion
import Conjectures.C0004_erdos461_smooth.src.KnownBound

/-!
# Erdős 461: milestone decision and exact remaining obstructions

B9 does not supply an unconditional bound.  Instead, this file closes the two
formal reductions as sharply as the preceding work permits.

* The B7 multiscale defect inequality is equivalent to a uniform matching of
  `ceil(t / 4)` lower-half divisors into distinct represented component values.
  This matching property still implies `Erdos461`, but is stronger than the
  original counting conjecture.
* The B5 simultaneous collision-loss estimate is equivalent to the reported
  `t / log t` lower bound itself, using the exact collision ledger.

No assumption instance is declared here.  See `Problems/erdos461_status.md`
for the mathematical obstructions left by the Delta/sieve investigation.
-/

namespace MoltResearch.Erdos461

/-- Every interval has a divisor-compatible component matching of size
`ceil(t / 4)`.  This is the exact matching proposition encoded by B7's
multiscale defect inequality; it is not asserted to hold. -/
def UniformQuarterComponentMatching : Prop :=
  ∀ n t : ℕ, 2 ≤ t →
    ∃ M : ComponentMatching n t, (t + 3) / 4 ≤ M.domain.card

/-- B7's multiscale expansion class is exactly the uniform quarter-matching
property.  The equivalence uses the finite defect form of Hall's theorem and
the exact identity between the dyadic band sum and the full neighbourhood. -/
theorem multiscaleComponentExpansionAssumption_iff_uniformQuarterMatching :
    MultiscaleComponentExpansionAssumption ↔ UniformQuarterComponentMatching := by
  constructor
  · intro h n t ht
    have hq : (t + 3) / 4 ≤ (componentLeft t).card := by
      simp [componentLeft]
      omega
    apply (exists_componentMatching_card_ge_iff_defectHall n t ((t + 3) / 4) hq).2
    intro U hU
    simpa [multiscaleComponentNeighborhoodCard_eq] using h.defect_bound n t ht U hU
  · intro h
    constructor
    intro n t ht U hU
    have hq : (t + 3) / 4 ≤ (componentLeft t).card := by
      simp [componentLeft]
      omega
    have hdefect :=
      (exists_componentMatching_card_ge_iff_defectHall n t ((t + 3) / 4) hq).1
        (h n t ht)
    simpa [multiscaleComponentNeighborhoodCard_eq] using hdefect U hU

/-- The exact uniform quarter-matching proposition still gives the requested
positive-proportion conclusion.  This theorem is conditional: no proof of
`UniformQuarterComponentMatching` is supplied. -/
theorem erdos461_of_uniformQuarterComponentMatching
    (h : UniformQuarterComponentMatching) : Erdos461 := by
  letI : MultiscaleComponentExpansionAssumption :=
    multiscaleComponentExpansionAssumption_iff_uniformQuarterMatching.mpr h
  exact erdos461_of_multiscaleComponentExpansion

/-- The B5 simultaneous collision-loss assumption is not merely sufficient
for the reported logarithmic estimate: by the exact collision ledger, it is
equivalent to that estimate.  This identifies the exact remaining proposition
without declaring either side as an instance. -/
theorem erdos461LogBound_iff_simultaneousFiberLossAssumption :
    Erdos461LogBound ↔ SimultaneousFiberLossAssumption := by
  constructor
  · rintro ⟨c, hc, hbound⟩
    constructor
    refine ⟨c, hc, ?_⟩
    intro n t ht
    have hledger :
        (collisionExcess n t : ℝ) + (smoothComponentCount n t : ℝ) = t := by
      exact_mod_cast collisionExcess_add_smoothComponentCount n t
    linarith [hbound n t ht]
  · intro h
    letI : SimultaneousFiberLossAssumption := h
    exact erdos461LogBound_of_simultaneousFiberLoss

/--
info: 'MoltResearch.Erdos461.erdos461_of_multiscaleComponentExpansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms erdos461_of_multiscaleComponentExpansion

/--
info: 'MoltResearch.Erdos461.erdos461LogBound_of_simultaneousFiberLoss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms erdos461LogBound_of_simultaneousFiberLoss

/--
info: 'MoltResearch.Erdos461.multiscaleComponentExpansionAssumption_iff_uniformQuarterMatching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms multiscaleComponentExpansionAssumption_iff_uniformQuarterMatching

/--
info: 'MoltResearch.Erdos461.erdos461_of_uniformQuarterComponentMatching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms erdos461_of_uniformQuarterComponentMatching

/--
info: 'MoltResearch.Erdos461.erdos461LogBound_iff_simultaneousFiberLossAssumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms erdos461LogBound_iff_simultaneousFiberLossAssumption

end MoltResearch.Erdos461
