import MoltResearch.Discrepancy
import MoltResearch.Discrepancy.LogDifferences
import MoltResearch.Discrepancy.ZetaBound
import MoltResearch.Discrepancy.LandauLemma
import MoltResearch.Discrepancy.ZeroFreeRegion
import MoltResearch.Discrepancy.PlancherelHarness

/-!
# DiscrepancyAnalytic (analytic-layer aggregator)

The **second stable surface**: the fast-moving analytic substrate of the
Track L/R campaigns (difference calculus and the vdC cascade, the zeta strip
bounds and approximate functional equation, the Landau-lemma machinery).

Import discipline (why two surfaces): almost no Track C stage file consumes
this layer, but every stage file imports `MoltResearch.Discrepancy` — so
keeping these modules inside the core aggregator forced a full stage-tree
rebuild on every analytic-layer change.  Consumers that genuinely use the
analytic layer (`TrackCStage5VKDischarge`, future zero-free-region and
Perron files) import `MoltResearch.DiscrepancyAnalytic`; everything else
imports `MoltResearch.Discrepancy` as before and is insulated.

The regression examples for this layer live in
`MoltResearch.Discrepancy.NormalFormExamplesAnalytic`.
-/
