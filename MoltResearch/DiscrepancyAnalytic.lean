import MoltResearch.Discrepancy
import MoltResearch.Discrepancy.LogDifferences
import MoltResearch.Discrepancy.ZetaBound
import MoltResearch.Discrepancy.LandauLemma
import MoltResearch.Discrepancy.ZeroFreeRegion
import MoltResearch.Discrepancy.ZetaLandauRadius
import MoltResearch.Discrepancy.ZetaGrowthRegion
import MoltResearch.Discrepancy.ZetaGrowthLogDeriv
import MoltResearch.Discrepancy.ZetaGrowthValidation
import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.LargeValues
import MoltResearch.Discrepancy.HalaszMontgomeryLargeValues
import MoltResearch.Discrepancy.Repulsion
import MoltResearch.Discrepancy.HalaszEuler
import MoltResearch.Discrepancy.DyadicMVT
import MoltResearch.Discrepancy.RamareIdentity
import MoltResearch.Discrepancy.SmoothRankin
import MoltResearch.Discrepancy.SelbergLinear
import MoltResearch.Discrepancy.ThreeScale
import MoltResearch.Discrepancy.PerronWindow
import MoltResearch.Discrepancy.PrimeSumZeroFree
import MoltResearch.Discrepancy.PrimeLargeValuesFromRegion
import MoltResearch.Discrepancy.ZeroFreeRegionData
import MoltResearch.Discrepancy.MajorArcFreeze
import MoltResearch.Discrepancy.ParsevalBridge
import MoltResearch.Discrepancy.HalaszAssembly
import MoltResearch.Discrepancy.RieszCapstone
import MoltResearch.Discrepancy.VinogradovTypeI
import MoltResearch.Discrepancy.VinogradovMeanValue
import MoltResearch.Discrepancy.VinogradovWeylSum
import MoltResearch.Discrepancy.HalaszTriple
import MoltResearch.Discrepancy.HalaszTripleG
import MoltResearch.Discrepancy.HalaszCapstone
import MoltResearch.Discrepancy.HalaszComplex
import MoltResearch.Discrepancy.HalaszSharpSurvivors
import MoltResearch.Discrepancy.HalaszSharpWindow
import MoltResearch.Discrepancy.HalaszSharpTwist
import MoltResearch.Discrepancy.HalaszSharpEps
import MoltResearch.Discrepancy.TypicalFactorization
import MoltResearch.Discrepancy.WindowTK
import MoltResearch.Discrepancy.LargePrimePolynomialCount
import MoltResearch.Discrepancy.ExceptionalCellCover
import MoltResearch.Discrepancy.ExceptionalHalaszTwist
import MoltResearch.Discrepancy.ExceptionalHalaszSharp
import MoltResearch.Discrepancy.SmoothRankinTail
import MoltResearch.Discrepancy.LowBandTypicalS
import MoltResearch.Discrepancy.LowBandTypicalSSharp
import MoltResearch.Discrepancy.BrunIntervalSieve
import MoltResearch.Discrepancy.EadicCellBrunTitchmarsh
import MoltResearch.Discrepancy.EulerProductSharp
import MoltResearch.Discrepancy.TypicalSLadderSplit
import MoltResearch.Discrepancy.PretentiousBandSplit
import MoltResearch.Discrepancy.WindowAssembly
import MoltResearch.Discrepancy.ExplicitBumpWindow
import MoltResearch.Discrepancy.ExplicitSliceWindow
import MoltResearch.Discrepancy.ExplicitSliceEnergy
import MoltResearch.Discrepancy.ExplicitSliceBands
import MoltResearch.Discrepancy.BandCapstone
import MoltResearch.Discrepancy.BandSchedule
import MoltResearch.Discrepancy.BandScheduleShares
import MoltResearch.Discrepancy.ShortIntervalRestriction
import MoltResearch.Discrepancy.RegimeSplitEnergy
import MoltResearch.Discrepancy.PrimeMassCell
import MoltResearch.Discrepancy.LevelSizes
import MoltResearch.Discrepancy.LevelOneSchedule
import MoltResearch.Discrepancy.CollisionSchedule
import MoltResearch.Discrepancy.LaterLevelSchedule
import MoltResearch.Discrepancy.ReplacementSchedule
import MoltResearch.Discrepancy.CellHalaszSchedule
import MoltResearch.Discrepancy.CellHalaszQuotientSchedule
import MoltResearch.Discrepancy.LevelLegs
import MoltResearch.Discrepancy.WideLevelErrorLegs
import MoltResearch.Discrepancy.ScaleOnlyCellRepresentatives
import MoltResearch.Discrepancy.LaterLevelCells
import MoltResearch.Discrepancy.CellHalasz
import MoltResearch.Discrepancy.ExceptionalConstants
import MoltResearch.Discrepancy.BumpDeriv
import MoltResearch.Discrepancy.MajorArcAssembly
import MoltResearch.Discrepancy.MajorArcBlockScale
import MoltResearch.Discrepancy.SliceA2
import MoltResearch.Discrepancy.SliceWeightConversion

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
