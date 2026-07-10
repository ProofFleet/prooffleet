import MoltResearch.Discrepancy.MultiplicativeC

/-!
# Discrepancy: stochastic completely multiplicative functions

Language-layer module for derivation (C) (`Problems/tao2015_derivation_c.md`): the
measure-theoretic packaging of Tao's *stochastic completely multiplicative functions*
(arXiv:1509.05363, Theorem 1.9 phrasing — a probability space and a measurable family of
completely multiplicative unimodular functions), together with the second-moment functional
`𝔼|∑_{j≤n} 𝐠(j)|²` that Theorem 1.8 says is unbounded.

Design notes (from the card's gotchas):
- Randomness is load-bearing in the derivation, and Theorem 1.9's measure-theoretic phrasing is
  the Lean-friendly formulation — a `structure` bundling the family, measurability, and
  almost-everywhere pointwise properties, parametrized by an arbitrary measure (probability
  assumptions are placed on lemmas, not baked into the structure).
- The multiplicativity/unimodularity fields are `∀ᵐ` (almost everywhere), matching "for almost
  every ω, g(ω) is completely multiplicative" in Theorem 1.9.
- `ofDeterministic` embeds a single completely multiplicative unimodular `g` as a constant
  family, so deterministic statements are literal special cases of stochastic ones.
-/

namespace MoltResearch

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stochastic completely multiplicative unimodular function (Tao 2015, Theorem 1.9 style):
a measurable family `ω ↦ g ω` of ℂ-valued sequences over a measure space, almost every member
of which is completely multiplicative and unimodular. -/
structure StochasticMultiplicative (μ : Measure Ω) where
  /-- The underlying random sequence. -/
  g : Ω → ℕ → ℂ
  /-- Coordinatewise measurability of the family. -/
  measurable : ∀ n : ℕ, Measurable fun ω => g ω n
  /-- Almost every member is completely multiplicative. -/
  mul_ae : ∀ᵐ ω ∂μ, CompletelyMultiplicativeC (g ω)
  /-- Almost every member is unimodular. -/
  unimodular_ae : ∀ᵐ ω ∂μ, Unimodular (g ω)

variable {μ : Measure Ω}

/-- Second moment of the step-one partial sums: `𝔼|∑_{j≤n} 𝐠(j)|²`.

Theorem 1.8 of Tao 2015 states that this is unbounded in `n` for every stochastic completely
multiplicative function; a *bounded* second moment is the standing hypothesis of the
van der Corput argument (Proposition 1.11).
-/
noncomputable def sndMomentPartialSum (G : StochasticMultiplicative μ) (n : ℕ) : ℝ :=
  ∫ ω, ‖apSumC (G.g ω) 1 n‖ ^ 2 ∂μ

/-- Degenerate length: the empty partial sum has second moment `0`. -/
@[simp] theorem sndMomentPartialSum_zero (G : StochasticMultiplicative μ) :
    sndMomentPartialSum G 0 = 0 := by
  simp [sndMomentPartialSum]

/-- The second moment is nonnegative (it is an integral of squares). -/
theorem sndMomentPartialSum_nonneg (G : StochasticMultiplicative μ) (n : ℕ) :
    0 ≤ sndMomentPartialSum G n :=
  integral_nonneg fun ω => by positivity

namespace StochasticMultiplicative

/-- A single completely multiplicative unimodular `g` as a constant (deterministic) stochastic
family over any measure space. -/
def ofDeterministic (μ : Measure Ω) (g : ℕ → ℂ)
    (hmul : CompletelyMultiplicativeC g) (hg : Unimodular g) :
    StochasticMultiplicative μ where
  g := fun _ => g
  measurable := fun _ => measurable_const
  mul_ae := ae_of_all μ fun _ => hmul
  unimodular_ae := ae_of_all μ fun _ => hg

/-- Over a probability measure, the deterministic embedding's second moment is the squared
partial-sum norm itself — deterministic statements are literal special cases of stochastic
ones. -/
@[simp] theorem sndMomentPartialSum_ofDeterministic [IsProbabilityMeasure μ] (g : ℕ → ℂ)
    (hmul : CompletelyMultiplicativeC g) (hg : Unimodular g) (n : ℕ) :
    sndMomentPartialSum (ofDeterministic μ g hmul hg) n = ‖apSumC g 1 n‖ ^ 2 := by
  simp [sndMomentPartialSum, ofDeterministic]

end StochasticMultiplicative

end MoltResearch
