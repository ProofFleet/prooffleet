import Conjectures.C0003_edp_rate.src.Statement
import Conjectures.C0003_edp_rate.src.SourceBudget
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.StochasticMultiplicative

/-!
# A finite-scale reduction for an explicit Erdős-discrepancy rate

This file records the conditional interface selected in
`Problems/edp_rate_approach.md`.  It replaces the compact limiting law in Tao's Section 2
with one law used only up to an explicit cutoff.  The three unproved inputs are deliberately
named `*Assumption`; the theorem at the end is only their logical composition and does not
claim an unconditional discrepancy rate.

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

/-- A finite persistent-pretentiousness conclusion.  The threshold `X₀` must fit below the
available cutoff, and the probability estimate is required only on the nonempty finite range
`X₀ ≤ X ≤ edpAnalysisCutoff x`.

This is the finite counterpart of the conclusion of Tao's Proposition 1.11.  Its quantifier
order keeps `K` independent of `ε`, as required by the existing qualitative interface.
-/
def FinitePersistentPretentious {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ Q T B : ℝ, 1 ≤ Q ∧ 1 ≤ T ∧ 0 ≤ B ∧
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ X₀ ≤ edpAnalysisCutoff x ∧
          ∀ X : ℕ, X₀ ≤ X → X ≤ edpAnalysisCutoff x →
            ENNReal.ofReal (1 - K * ε) ≤ μ (finitePretentiousEvent G Q T B X)

/-- **Finite Fourier-reduction input.**  If every homogeneous sum inside the product budget
`dm ≤ x` is smaller than `edpTripleLogRate x`, produce a stochastic completely multiplicative
law whose second moments are small through `edpAnalysisCutoff x`.

This is the precise replacement for `exists_limit_law` proposed in
`Problems/edp_rate_approach.md`.  The tree already constructs exact completely multiplicative
finite spectral samples; the new mathematical obligation is to keep every translating dilation
inside the source budget instead of assuming a global discrepancy bound.
-/
class FiniteFourierReductionAssumption : Prop where
  reduce :
    ∀ (f : ℕ → ℤ), IsSignSequence f →
      ∀ x : ℝ, edpRateStart < x →
        (∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
          |(apSum f d m : ℝ)| < edpTripleLogRate x) →
          ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
            (_ : @IsProbabilityMeasure Ω mΩ μ)
            (G : @StochasticMultiplicative Ω mΩ μ),
            @FiniteSecondMomentBound Ω mΩ μ G x

/-- Consumer-facing projection of `FiniteFourierReductionAssumption`. -/
theorem finiteFourierReduction [inst : FiniteFourierReductionAssumption]
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

The intended proof is a threshold-tracked version of the tree's
`TrackCStage5VanDerCorputProof.lean`, consuming the nonasymptotic Elliott estimate and fitting
all choices of `H`, `A`, `w`, and the terminal truncation below `edpAnalysisCutoff x`; see
`Problems/edp_rate_approach.md`, Section 4.
-/
class FiniteVanDerCorputRateAssumption : Prop where
  pretentious :
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : @Measure Ω mΩ)
      [@IsProbabilityMeasure Ω mΩ μ]
      (G : @StochasticMultiplicative Ω mΩ μ) (x : ℝ),
      edpRateStart < x → FiniteSecondMomentBound μ G x →
        FinitePersistentPretentious μ G x

/-- Consumer-facing projection of `FiniteVanDerCorputRateAssumption`. -/
theorem finiteVanDerCorputRate [inst : FiniteVanDerCorputRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    FinitePersistentPretentious μ G x :=
  inst.pretentious μ G x hx hG

/-- **Finite Borwein--Choi--Coons input.**  The structured branch defeats the finite
persistent-pretentiousness conclusion while the same second-moment cap is in force.

The intended proof effectivizes the present Section 4 wrapper using the tree's explicit
Mertens, repulsion, zero-free-region, and Euler-product bounds.  All thresholds must fit below
`edpAnalysisCutoff x`; no limit in `x` is available.  See
`Problems/edp_rate_approach.md`, Section 5.
-/
class FiniteBorweinChoiCoonsRateAssumption : Prop where
  not_pretentious :
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : @Measure Ω mΩ)
      [@IsProbabilityMeasure Ω mΩ μ]
      (G : @StochasticMultiplicative Ω mΩ μ) (x : ℝ),
      edpRateStart < x → FiniteSecondMomentBound μ G x →
        ¬ FinitePersistentPretentious μ G x

/-- Consumer-facing projection of `FiniteBorweinChoiCoonsRateAssumption`. -/
theorem finiteBorweinChoiCoonsRate [inst : FiniteBorweinChoiCoonsRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    ¬ FinitePersistentPretentious μ G x :=
  inst.not_pretentious μ G x hx hG

/-- Conditional first EDP rate: the finite Fourier reduction, finite Elliott/van-der-Corput
stage, and finite structured branch compose to `HasDiscrepancyRateBy edpTripleLogRate`.

This theorem proves only the glue.  Its three typeclass inputs are open obligations listed as
Phase-2 nodes in `Problems/edp_rate_approach.md`; no instance is declared here.
-/
theorem discrepancyRate_of_assumptions
    [FiniteFourierReductionAssumption]
    [FiniteVanDerCorputRateAssumption]
    [FiniteBorweinChoiCoonsRateAssumption] :
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
    obtain ⟨Ω, mΩ, μ, hμ, G, hG⟩ := finiteFourierReduction f hf x hlarge hsmall
    have hpersistent :=
      finiteVanDerCorputRate (μ := μ) G x hlarge hG
    exact (finiteBorweinChoiCoonsRate (μ := μ) G x hlarge hG) hpersistent

end MoltResearch
