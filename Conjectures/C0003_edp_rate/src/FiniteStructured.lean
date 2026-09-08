import Conjectures.C0003_edp_rate.src.FiniteFourierBudget
import Conjectures.C0003_edp_rate.src.StructuredThresholds

/-!
# Finite structured package: the finite-interval obstruction

## Known

The qualitative Borwein--Choi--Coons argument in Tao's Section 4 responds to a proposed
pretense bound `B` by choosing a still larger terminal scale.  A8 exposes that dependence in
`structuredTerminalScaleOfTCut`; its `t`-cut component includes the very large witness
described in `Problems/edp_rate_structured_thresholds.md`.

## Conjectured

The Erdős discrepancy-rate statement remains open.  This file does not prove a rate or
install `FiniteBorweinChoiCoonsRateAssumption`.

## Our audit and exact obstruction

`FinitePersistentPretentious` only asks for a package on the finite interval `X₀ ≤ X ≤ L`,
where `L = edpAnalysisCutoff x`, while allowing `(Q,T,B,X₀)` to be chosen after `x`.  Taking
`X₀ = L` leaves one scale.  At that scale every unimodular sample is within the uniform bound

`2 * ∑ p ∈ L.primesBelow, 1 / p`

of the trivial character twist.  Since stochastic samples are unimodular almost everywhere,
the resulting finite pretentious event has probability one.  The theorems below prove that
`FinitePersistentPretentious` is therefore automatic whenever `1 ≤ L`, and that the revised
cutoff has this property for every `x > edpRateStart`.

**Blocked:** A9 asks for the negation of an automatic conclusion.  In particular, whenever a
`FiniteSecondMomentBound` witness is supplied, the requested structured instance would yield
both `FinitePersistentPretentious` and its negation.  The structured terminal scale cannot
repair this quantifier-order obstruction: increasing `B` at the sole finite endpoint merely
makes its dependent terminal scale exceed the available interval.  The interface must keep a
tail cofinal after `(Q,T,B,X₀)` are fixed, or otherwise require the terminal scale itself to
fit before the package is accepted.
-/

namespace MoltResearch

open MeasureTheory

/-- A sample-independent upper bound for pretentious distance at one finite truncation. -/
noncomputable def finitePretentiousUniversalBound (L : ℕ) : ℝ :=
  2 * ∑ p ∈ L.primesBelow, (1 : ℝ) / p

theorem finitePretentiousUniversalBound_nonneg (L : ℕ) :
    0 ≤ finitePretentiousUniversalBound L := by
  unfold finitePretentiousUniversalBound
  positivity

/-- Every unimodular function is within the universal finite bound of the trivial twist. -/
theorem pretentiousDistSq_trivialTwist_le_universalBound
    (g : ℕ → ℂ) (hg : Unimodular g) (L : ℕ) :
    pretentiousDistSq g (charTwist 1 1 0) L ≤ finitePretentiousUniversalBound L := by
  have htail := pretentiousDistSq_le_add_mass g (charTwist 1 1 0)
    (fun p => (hg p).le) (charTwist_norm_le_one 1 1 0) (Nat.zero_le L)
  simpa [finitePretentiousUniversalBound] using htail

/-- On any nonempty finite cutoff, the current persistent-pretense target is automatic:
choose its starting scale to be the terminal scale itself. -/
theorem finitePersistentPretentious_of_one_le_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ)
    (hL : 1 ≤ edpAnalysisCutoff x) :
    FinitePersistentPretentious μ G x := by
  let L := edpAnalysisCutoff x
  let B := finitePretentiousUniversalBound L
  refine ⟨0, le_rfl, ?_⟩
  intro ε hε0 hε1
  refine ⟨1, 1, B, le_rfl, le_rfl, finitePretentiousUniversalBound_nonneg L,
    L, ?_, le_rfl, ?_⟩
  · simpa [L] using hL
  · intro X hLX hXL
    have hX : X = L := Nat.le_antisymm hXL hLX
    subst X
    have hmono : μ Set.univ ≤ μ (finitePretentiousEvent G 1 1 B L) := by
      apply measure_mono_ae
      filter_upwards [G.unimodular_ae] with ω hω
      intro _
      refine ⟨1, 1, 0, by norm_num, by simp, ?_⟩
      exact pretentiousDistSq_trivialTwist_le_universalBound (G.g ω) hω L
    have hfull : (1 : ENNReal) ≤ μ (finitePretentiousEvent G 1 1 B L) := by
      simpa only [measure_univ] using hmono
    simpa using hfull

/-- The source-budget-safe cutoff is nonempty throughout the large-`x` branch. -/
theorem one_le_edpAnalysisCutoff_of_rateStart_lt {x : ℝ} (hx : edpRateStart < x) :
    1 ≤ edpAnalysisCutoff x := by
  have hstart : (1 : ℝ) < edpRateStart := by
    unfold edpRateStart
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp (Real.exp (Real.exp 1)) :=
        Real.exp_lt_exp.mpr (Real.exp_pos (Real.exp 1))
  have hxone : (1 : ℝ) ≤ x := (hstart.trans hx).le
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hxone)
  apply le_edpAnalysisCutoff_of_scheduledBudget hfloor
  change 1 ≤ ⌊x⌋₊
  exact hfloor

/-- Hence finite persistent pretense holds for every stochastic law in the entire branch on
which the proposed finite structured instance is meant to refute it. -/
theorem finitePersistentPretentious_of_rateStart_lt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {x : ℝ} (hx : edpRateStart < x) :
    FinitePersistentPretentious μ G x :=
  finitePersistentPretentious_of_one_le_cutoff μ G x
    (one_le_edpAnalysisCutoff_of_rateStart_lt hx)

/-- Exact contradiction produced by the requested A9 instance at any actual finite
second-moment witness. -/
theorem finiteStructured_target_contradiction
    [FiniteBorweinChoiCoonsRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {x : ℝ} (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) : False := by
  apply finiteBorweinChoiCoonsRate (μ := μ) G x hx hG
  exact finitePersistentPretentious_of_rateStart_lt (μ := μ) G hx

end MoltResearch
