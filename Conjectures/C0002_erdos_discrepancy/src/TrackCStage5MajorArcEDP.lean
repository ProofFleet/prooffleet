import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcMR
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5EDPMilestone

/-!
# Track C: Stage 5 — EDP conditional on `[mrt]` Theorem A.2 (Track R, R7-6 endpoint)

The Track R chain ends here.  `matomakiRadziwillMajorArc_of_A2` turns the `𝒮`-restricted
mean-square Prop `SliceMeanSquareA2` into the major-arc Matomäki–Radziwiłł interface, and
`edp_of_majorArcMR` (with the unconditional Vinogradov classification
`instPrimeBlockMajorArcAssumption`) turns that interface into the Erdős discrepancy theorem.
Composed: **EDP for all sign sequences, conditional on exactly `SliceMeanSquareA2`** — one
proposition of `[mrt]` (Appendix A, Theorem A.2), whose discharge is the A.2 campaign
(`Problems/tao2015_a1_r6r7_design_report.md` §8, Phase 0 / A2-IV / A2-V).

Both theorems below take the Prop as an explicit hypothesis, so their axiom footprints
(pinned in `TrackCAxiomAudit.lean`) are the three standard axioms only.
-/

namespace MoltResearch

namespace Tao2015

/-- **EDP conditional on `[mrt]` Theorem A.2** (Track R, #3044): the Erdős discrepancy
theorem for all sign sequences, assuming exactly the `𝒮`-restricted mean-square Prop
`SliceMeanSquareA2`.  Through `matomakiRadziwillMajorArc_of_A2` and `edp_of_majorArcMR`. -/
theorem edp_of_sliceMeanSquareA2 (hA2 : SliceMeanSquareA2)
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  haveI := matomakiRadziwillMajorArc_of_A2 hA2
  edp_of_majorArcMR f hf

/-- **Theorem 1.8 conditional on `[mrt]` Theorem A.2** (Track R, #3044): the second-moment
blowup for stochastic completely multiplicative functions, assuming exactly
`SliceMeanSquareA2`. -/
theorem theorem18_of_sliceMeanSquareA2 (hA2 : SliceMeanSquareA2)
    {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, sndMomentPartialSum G n ≤ C :=
  haveI := matomakiRadziwillMajorArc_of_A2 hA2
  theorem18_of_majorArcMR μ G

end Tao2015

end MoltResearch
