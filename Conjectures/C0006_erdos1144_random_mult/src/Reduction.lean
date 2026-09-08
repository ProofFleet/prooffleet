import Conjectures.C0006_erdos1144_random_mult.src.Statement
import Mathlib.Probability.BorelCantelli

/-!
# A conditional block reduction for Erdős Problem 1144

This file does not prove `Erdos1144`.  It isolates three unproved inputs from the route in
`Problems/erdos1144_approach.md`: a block construction whose success events produce genuinely
positive partial sums, a local positive-maximum estimate, and a summable deterministic budget
for its failure probabilities.

The final recurrence step is unconditional.  It is an application of Mathlib's first
Borel--Cantelli lemma, followed by an elementary passage from integer heights to real heights.

A tagged external release, `saasom/Erdos1144` v1.0.0, claims an unconditional Lean proof of the
same target.  This file neither imports nor verifies that release.  Its final active route uses a
fixed-cylinder upper-envelope argument rather than the stronger summable-failure interface here;
see the status discussion in `Problems/erdos1144_approach.md` and the separate D3v verification
item on the problem card.
-/

namespace MoltResearch

open MeasureTheory
open scoped BigOperators ENNReal

/-- Data for a proposed prime-block argument.

`start k` is the left endpoint of the `k`th scale block.  `success height k` is a measurable
surrogate event, intended to be certified using the fresh prime signs in that block, which
forces the original (uncentred and one-sided) partial sum above `height` somewhere in the block.
`failureBudget height k` is a deterministic upper bound proposed for its failure probability.
The mathematical properties of this data are deliberately kept out of the structure and put
in explicit assumption classes below. -/
structure PrimeBlockScheme where
  start : ℕ → ℕ
  success : ℕ → ℕ → Set Ω
  failureBudget : ℕ → ℕ → ENNReal

/-- The deterministic and measurable part of the prime-block decomposition proposed in
`Problems/erdos1144_approach.md`, §§3--4.

This is an open interface: an instance must prove that the block endpoints escape to infinity,
that each surrogate success event is measurable, and that success really gives a positive
large value of the original completely multiplicative partial sum in that same block. -/
class PrimeBlockDecompositionAssumption (scheme : PrimeBlockScheme) : Prop where
  start_strictMono : StrictMono scheme.start
  measurable_success : ∀ height block, MeasurableSet (scheme.success height block)
  success_witness : ∀ {height block : ℕ} {omega : Ω},
    omega ∈ scheme.success height block →
      ∃ N ∈ Set.Ico (scheme.start block) (scheme.start (block + 1)),
        (height : ℝ) ≤ (partialSum omega N : ℝ) / Real.sqrt N

/-- The one-sided local maximum estimate proposed in
`Problems/erdos1144_approach.md`, §§4--5.

For every integer height and block, the failure probability must be bounded by the scheme's
explicit deterministic budget.  Together with `SummableBlockBudgetAssumption`, this is stronger
than a positive-probability estimate and is the analytic heart of the route.  In particular, it
must control the smooth remainder and preserve the sign; an absolute-value lower bound does not
provide an instance. -/
class PositiveBlockProbabilityAssumption (scheme : PrimeBlockScheme) : Prop where
  failure_probability_le : ∀ height block : ℕ,
    randomCMMeasure ((scheme.success height block)ᶜ) ≤ scheme.failureBudget height block

/-- Summability of the deterministic failure budget, as proposed in
`Problems/erdos1144_approach.md`, §5.

This is separated from `PositiveBlockProbabilityAssumption` so that choosing a sufficiently
sparse scale sequence is not hidden inside the analytic local-maximum estimate. -/
class SummableBlockBudgetAssumption (scheme : PrimeBlockScheme) : Prop where
  summable_budget : ∀ height : ℕ, (∑' block : ℕ, scheme.failureBudget height block) ≠ ∞

/-- First Borel--Cantelli turns summable block failures into eventual success at every fixed
integer height. -/
theorem eventually_primeBlock_success (scheme : PrimeBlockScheme)
    [PositiveBlockProbabilityAssumption scheme] [SummableBlockBudgetAssumption scheme]
    (height : ℕ) :
    ∀ᵐ omega ∂randomCMMeasure, ∀ᶠ block : ℕ in Filter.atTop,
      omega ∈ scheme.success height block := by
  have hsum : (∑' block : ℕ, randomCMMeasure ((scheme.success height block)ᶜ)) ≠ ∞ :=
    ne_top_of_le_ne_top
      (SummableBlockBudgetAssumption.summable_budget (scheme := scheme) height)
      (ENNReal.tsum_le_tsum fun block ↦
        PositiveBlockProbabilityAssumption.failure_probability_le
          (scheme := scheme) height block)
  simpa only [Set.mem_compl_iff, not_not] using
    (MeasureTheory.ae_eventually_notMem hsum)

/-- Conditional closure of the proposed route.

No fluctuation estimate is proved here: the three typeclass hypotheses are precisely the open
prime-block decomposition, one-sided local maximum, and summable-budget inputs.  The theorem
proves that those inputs are sufficient for the exact frequent-exceedance formulation of
`Erdos1144`. -/
theorem erdos1144_of_assumptions (scheme : PrimeBlockScheme)
    [PrimeBlockDecompositionAssumption scheme]
    [PositiveBlockProbabilityAssumption scheme]
    [SummableBlockBudgetAssumption scheme] :
    Erdos1144 := by
  have hsuccess : ∀ height : ℕ, ∀ᵐ omega ∂randomCMMeasure,
      ∀ᶠ block : ℕ in Filter.atTop, omega ∈ scheme.success height block :=
    fun height ↦ eventually_primeBlock_success scheme height
  rw [Erdos1144]
  filter_upwards [ae_all_iff.2 hsuccess] with omega homega
  intro M
  obtain ⟨height, hM⟩ := exists_nat_ge M
  have hfrequent : ∃ᶠ block : ℕ in Filter.atTop,
      omega ∈ scheme.success height block := (homega height).frequently
  rw [Filter.frequently_atTop] at hfrequent ⊢
  intro lower
  obtain ⟨block, hlower, hblock⟩ := hfrequent lower
  obtain ⟨N, ⟨hstart, _⟩, hlarge⟩ :=
    PrimeBlockDecompositionAssumption.success_witness (scheme := scheme) hblock
  refine ⟨N, ?_, hM.trans hlarge⟩
  exact hlower.trans
    ((PrimeBlockDecompositionAssumption.start_strictMono (scheme := scheme)).le_apply.trans hstart)

end MoltResearch
