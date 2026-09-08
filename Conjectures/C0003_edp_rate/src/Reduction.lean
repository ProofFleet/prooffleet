import Conjectures.C0003_edp_rate.src.Statement
import Conjectures.C0003_edp_rate.src.SourceBudget
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.StochasticMultiplicative

/-!
# A finite-scale reduction for an explicit Erdős-discrepancy rate

This file records the conditional interface selected in
`Problems/edp_rate_approach.md` and repaired in
`Problems/edp_rate_interface_repair.md`.  It replaces the compact limiting law in Tao's
Section 2 with one law used only up to an explicit cutoff.  The three unproved inputs are
deliberately named `*Assumption`; the theorem at the end is only their logical composition
and does not claim an unconditional discrepancy rate.

The rate is a conservative, concrete version of the triple-logarithmic product-scale rate
obtained by reparameterizing McNamara's quantitative rectangle.  The exponent `1/500` stays
strictly below the published `1/484-o(1)` exponent.  The analysis cutoff is calibrated to the
exact source budget of the finite exponent-box construction; see
`Problems/edp_rate_fourier_redesign.md`.
-/

namespace MoltResearch

open MeasureTheory

/-- The fixed scale below which the elementary one-term progression supplies the rate. -/
noncomputable def edpRateStart : ℝ :=
  Real.exp (Real.exp (Real.exp 1))

/-- The exact terminal source budget of the exponent-box construction at analysis scale `X`,
using the least positive modulus that pays for the wraparound error. -/
def edpScheduledSourceBudget (X : ℕ) : ℕ :=
  spectralSourceBudget X
    (max 1 (Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2)) X

/-- The finite analytic window available at product scale `x`: the greatest `X ≤ ⌊x⌋₊`
whose exact scheduled source budget fits below `⌊x⌋₊`.

This replaces the overlarge A3 schedule.  It makes the Fourier source-budget inequality true
by construction, while every fixed `X` is eventually admitted once the outer budget exceeds
the fixed natural number `max X (edpScheduledSourceBudget X)`.
-/
noncomputable def edpAnalysisCutoff (x : ℝ) : ℕ :=
  Nat.findGreatest
    (fun X => edpScheduledSourceBudget X ≤ ⌊x⌋₊) ⌊x⌋₊

/-- A concrete first-rate target.  Past `edpRateStart` it is a fixed positive multiple of
`(log log log x)^(1/500)`; before that scale it is `1`, so the progression `(d,m) = (1,1)`
suffices.

The triple logarithm comes from converting McNamara's rectangular range to the product budget;
`1/500 < 1/484` leaves room for his lower-order iterated-log losses.  The coefficient `10^-7`
is the A5' recalibration after replacing the A3 cutoff by the source-budget-safe schedule.  See
`Problems/edp_rate_fourier_redesign.md`.
-/
noncomputable def edpTripleLogRate (x : ℝ) : ℝ :=
  if x ≤ edpRateStart then 1
  else (1 / 10 ^ 7 : ℝ) *
    Real.rpow (Real.log (Real.log (Real.log x))) ((1 : ℝ) / 500)

/-- A law has the finite second-moment bound needed by the effective analytic stages at
product scale `x`.  Unlike `exists_limit_law`, this asks for bounds only through the explicit
cutoff `edpAnalysisCutoff x`.
-/
def FiniteSecondMomentBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ edpAnalysisCutoff x →
    sndMomentPartialSum G n ≤ edpTripleLogRate x ^ 2 + 1

/-- The finite-scale version of Tao's pretentious event: at truncation `X`, a sample lies
within squared pretentious distance `B` of some character twist of modulus at most `Q` and
frequency at most `T * X`.
-/
noncomputable def finitePretentiousEvent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (G : StochasticMultiplicative μ)
    (Q T B : ℝ) (X : ℕ) : Set Ω :=
  {ω : Ω | ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    (q : ℝ) ≤ Q ∧ |t| ≤ T * X ∧
      pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B}

/-- Which finite-endpoint contract a conditional rate assumption uses.

`historical` preserves the A3 statement so the checked A7/A9 obstruction artifacts remain
buildable.  The active reduction uses `budgeted`; its window and parameter restrictions are
the A3' repair. -/
inductive FiniteEndpointPolicy where
  | historical
  | budgeted

/-- Historical A3 persistent-pretense target.  It is retained only as the subject of the
checked obstruction artifacts in `FiniteVanDerCorput.lean` and `FiniteStructured.lean`.
New rate assumptions must use `FiniteEndpointPolicy.budgeted`. -/
def HistoricalFinitePersistentPretentious {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ Q T B : ℝ, 1 ≤ Q ∧ 1 ≤ T ∧ 0 ≤ B ∧
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ X₀ ≤ edpAnalysisCutoff x ∧
          ∀ X : ℕ, X₀ ≤ X → X ≤ edpAnalysisCutoff x →
            ENNReal.ofReal (1 - K * ε) ≤ μ (finitePretentiousEvent G Q T B X)

/-! ## Repaired finite-endpoint controls -/

/-- Cofinal modulus cap fixed by the cutoff before a pretentious package is selected. -/
noncomputable def edpPretentiousModulusCap (L : ℕ) : ℝ :=
  max 1 (Real.log ((L : ℝ) + 1))

/-- Cofinal frequency cap fixed by the cutoff before a pretentious package is selected. -/
noncomputable def edpPretentiousFrequencyCap (L : ℕ) : ℝ :=
  max 1 (Real.log ((L : ℝ) + 1))

/-- A deliberately slow cofinal distance cap.  Unlike the historical interface, the
package cannot enlarge `B` to the universal finite-truncation bound after seeing `L`. -/
noncomputable def edpPretentiousDistanceCap (L : ℕ) : ℝ :=
  max 0 ((1 / 4 : ℝ) * Real.log (Real.log ((L : ℝ) + 3)))

/-- The largest moment shift reserved for the A6 van-der-Corput window at accuracy `ε`.
This is definitionally the A6 function `edpVdCWindowLength` at the moment cap
`edpTripleLogRate x ^ 2 + 1`, but is defined here to avoid a downstream import cycle. -/
noncomputable def edpPersistentWindowLength (x ε : ℝ) : ℕ :=
  max 1 ⌈8 * max (edpTripleLogRate x ^ 2 + 1) 1 / ε⌉₊

theorem one_le_edpPersistentWindowLength (x ε : ℝ) :
    1 ≤ edpPersistentWindowLength x ε := by
  simp [edpPersistentWindowLength]

/-- The repaired finite persistent-pretense target.

Only one accuracy is requested: this is exactly what the structured contradiction consumes.
It must give probability loss at most `1/4`, reserve every A6 moment through `X + H`, and
choose `(Q,T,B)` under cutoff-dependent caps fixed before the package.  The estimate then
holds throughout the entire nonempty interval ending at `edpAnalysisCutoff x - H`.

The caps are cofinal functions, so a fixed qualitative package is eventually admitted, but
no package can diagonalize by choosing an arbitrarily large `B` at the last finite endpoint.
See `Problems/edp_rate_interface_repair.md`. -/
noncomputable def BudgetedFinitePersistentPretentious
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ K * ε ≤ 1 / 4 ∧
      ∃ Q T B : ℝ,
        1 ≤ Q ∧ Q ≤ edpPretentiousModulusCap (edpAnalysisCutoff x) ∧
        1 ≤ T ∧ T ≤ edpPretentiousFrequencyCap (edpAnalysisCutoff x) ∧
        0 ≤ B ∧ B ≤ edpPretentiousDistanceCap (edpAnalysisCutoff x) ∧
          ∃ X₀ : ℕ, 1 ≤ X₀ ∧
            X₀ + edpPersistentWindowLength x ε ≤ edpAnalysisCutoff x ∧
              ∀ X : ℕ, X₀ ≤ X →
                X + edpPersistentWindowLength x ε ≤ edpAnalysisCutoff x →
                  ENNReal.ofReal (1 - K * ε) ≤
                    μ (finitePretentiousEvent G Q T B X)

/-- Policy-indexed finite persistent pretense.

The default is historical solely so the two merged obstruction files remain compile-time
regressions.  All three active rate classes and the glue theorem explicitly select
`.budgeted`; future consumers should do the same. -/
noncomputable def FinitePersistentPretentious {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ)
    (policy : FiniteEndpointPolicy := .historical) : Prop :=
  match policy with
  | .historical => HistoricalFinitePersistentPretentious μ G x
  | .budgeted => BudgetedFinitePersistentPretentious μ G x

/-- A budgeted package always leaves the positive A6 window inside the moment cutoff. -/
theorem budgetedFinitePersistentPretentious_has_slack
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : StochasticMultiplicative μ) (x : ℝ)
    (h : FinitePersistentPretentious μ G x .budgeted) :
    ∃ ε : ℝ, ∃ X₀ : ℕ, 0 < ε ∧ 1 ≤ X₀ ∧
      X₀ + edpPersistentWindowLength x ε ≤ edpAnalysisCutoff x := by
  change BudgetedFinitePersistentPretentious μ G x at h
  rcases h with ⟨K, hK, ε, hε0, hε1, hKε, Q, T, B, hQ1, hQcap,
    hT1, hTcap, hB0, hBcap, X₀, hX₀1, hfit, hpersistent⟩
  exact ⟨ε, X₀, hε0, hX₀1, hfit⟩

/-- **Finite Fourier-reduction input.**  If every homogeneous sum inside the product budget
`dm ≤ x` is smaller than `edpTripleLogRate x`, produce a stochastic completely multiplicative
law whose second moments are small through `edpAnalysisCutoff x`.

This is the precise replacement for `exists_limit_law` proposed in
`Problems/edp_rate_approach.md`.  The tree already constructs exact completely multiplicative
finite spectral samples; the new mathematical obligation is to keep every translating dilation
inside the source budget instead of assuming a global discrepancy bound.  The policy index
keeps that same Fourier payload synchronized with the repaired downstream contract; see
`Problems/edp_rate_interface_repair.md`.
-/
class FiniteFourierReductionAssumption
    (policy : FiniteEndpointPolicy := .historical) : Prop where
  reduce :
    ∀ (f : ℕ → ℤ), IsSignSequence f →
      ∀ x : ℝ, edpRateStart < x →
        (∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
          |(apSum f d m : ℝ)| < edpTripleLogRate x) →
          ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
            (_ : @IsProbabilityMeasure Ω mΩ μ)
            (G : @StochasticMultiplicative Ω mΩ μ),
            @FiniteSecondMomentBound Ω mΩ μ G x

/-- Historical consumer-facing projection, retained for the merged A5 obstruction. -/
theorem finiteFourierReduction [inst : FiniteFourierReductionAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) (x : ℝ) (hx : edpRateStart < x)
    (hsmall : ∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
      |(apSum f d m : ℝ)| < edpTripleLogRate x) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (_ : @IsProbabilityMeasure Ω mΩ μ)
      (G : @StochasticMultiplicative Ω mΩ μ),
      @FiniteSecondMomentBound Ω mΩ μ G x :=
  inst.reduce f hf x hx hsmall

/-- Consumer-facing projection of the repaired Fourier interface. -/
theorem finiteFourierReduction_budgeted
    [inst : FiniteFourierReductionAssumption .budgeted]
    (f : ℕ → ℤ) (hf : IsSignSequence f) (x : ℝ) (hx : edpRateStart < x)
    (hsmall : ∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
      |(apSum f d m : ℝ)| < edpTripleLogRate x) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (_ : @IsProbabilityMeasure Ω mΩ μ)
      (G : @StochasticMultiplicative Ω mΩ μ),
      @FiniteSecondMomentBound Ω mΩ μ G x :=
  inst.reduce f hf x hx hsmall

/-- **Finite van-der-Corput/Elliott input.**  A finite second-moment bound forces persistent
pretentiousness before the same explicit cutoff.

At policy `.budgeted`, the intended proof is a threshold-tracked version of the tree's
`TrackCStage5VanDerCorputProof.lean`, consuming the nonasymptotic Elliott estimate and fitting
all choices of `H`, `A`, `w`, and the terminal truncation below the shortened endpoint
`edpAnalysisCutoff x - edpPersistentWindowLength x ε`; see
`Problems/edp_rate_interface_repair.md`, Sections 4 and 7.
-/
class FiniteVanDerCorputRateAssumption
    (policy : FiniteEndpointPolicy := .historical) : Prop where
  pretentious :
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : @Measure Ω mΩ)
      [@IsProbabilityMeasure Ω mΩ μ]
      (G : @StochasticMultiplicative Ω mΩ μ) (x : ℝ),
      edpRateStart < x → FiniteSecondMomentBound μ G x →
        FinitePersistentPretentious μ G x policy

/-- Historical consumer-facing projection, retained for the merged A7 obstruction. -/
theorem finiteVanDerCorputRate [inst : FiniteVanDerCorputRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    FinitePersistentPretentious μ G x :=
  inst.pretentious μ G x hx hG

/-- Consumer-facing projection of the repaired van-der-Corput interface. -/
theorem finiteVanDerCorputRate_budgeted
    [inst : FiniteVanDerCorputRateAssumption .budgeted]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    FinitePersistentPretentious μ G x .budgeted :=
  inst.pretentious μ G x hx hG

/-- **Finite Borwein--Choi--Coons input.**  The structured branch defeats the finite
persistent-pretentiousness conclusion while the same second-moment cap is in force.

At policy `.budgeted`, the intended proof effectivizes the present Section 4 wrapper using the
tree's explicit Mertens, repulsion, zero-free-region, and Euler-product bounds.  It must handle
every `(Q,T,B)` below the fixed cutoff caps and fit its dependent terminal scale below the
shortened endpoint; no limit in `x` is available.  See
`Problems/edp_rate_interface_repair.md`, Sections 4, 5, and 7.
-/
class FiniteBorweinChoiCoonsRateAssumption
    (policy : FiniteEndpointPolicy := .historical) : Prop where
  not_pretentious :
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : @Measure Ω mΩ)
      [@IsProbabilityMeasure Ω mΩ μ]
      (G : @StochasticMultiplicative Ω mΩ μ) (x : ℝ),
      edpRateStart < x → FiniteSecondMomentBound μ G x →
        ¬ FinitePersistentPretentious μ G x policy

/-- Historical consumer-facing projection, retained for the merged A9 obstruction. -/
theorem finiteBorweinChoiCoonsRate [inst : FiniteBorweinChoiCoonsRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    ¬ FinitePersistentPretentious μ G x :=
  inst.not_pretentious μ G x hx hG

/-- Consumer-facing projection of the repaired structured interface. -/
theorem finiteBorweinChoiCoonsRate_budgeted
    [inst : FiniteBorweinChoiCoonsRateAssumption .budgeted]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    ¬ FinitePersistentPretentious μ G x .budgeted :=
  inst.not_pretentious μ G x hx hG

/-- Conditional first EDP rate: the finite Fourier reduction, finite Elliott/van-der-Corput
stage, and finite structured branch compose to `HasDiscrepancyRateBy edpTripleLogRate`.

This theorem proves only the glue.  Its three `.budgeted` typeclass inputs are open obligations
listed as Phase-2 nodes in `Problems/edp_rate_interface_repair.md`; only the Fourier input is
instantiated separately in `FiniteFourierBudget.lean`.
-/
theorem discrepancyRate_of_assumptions
    [FiniteFourierReductionAssumption .budgeted]
    [FiniteVanDerCorputRateAssumption .budgeted]
    [FiniteBorweinChoiCoonsRateAssumption .budgeted] :
    HasDiscrepancyRateBy edpTripleLogRate := by
  intro f hf x hx
  by_cases hsmallx : x ≤ edpRateStart
  · refine ⟨1, 1, by norm_num, ?_, ?_⟩
    · norm_num
      linarith
    · rw [edpTripleLogRate, if_pos hsmallx]
      rcases hf 1 with h | h <;> simp [apSum, h]
  · have hlarge : edpRateStart < x := lt_of_not_ge hsmallx
    by_contra hwitness
    have hsmall : ∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
        |(apSum f d m : ℝ)| < edpTripleLogRate x := by
      intro d m hd hdm
      exact lt_of_not_ge fun hrate => hwitness ⟨d, m, hd, hdm, hrate⟩
    obtain ⟨Ω, mΩ, μ, hμ, G, hG⟩ :=
      finiteFourierReduction_budgeted f hf x hlarge hsmall
    have hpersistent :=
      finiteVanDerCorputRate_budgeted (μ := μ) G x hlarge hG
    exact (finiteBorweinChoiCoonsRate_budgeted (μ := μ) G x hlarge hG)
      hpersistent

end MoltResearch
