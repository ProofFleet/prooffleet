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

/-- Coordinatewise measurability extends to the partial sums. -/
theorem measurable_apSumC (G : StochasticMultiplicative μ) (d n : ℕ) :
    Measurable fun ω => apSumC (G.g ω) d n := by
  unfold apSumC
  exact Finset.measurable_sum _ fun i _ => G.measurable ((i + 1) * d)

/-- Coordinatewise measurability extends to the window sums. -/
theorem measurable_windowSumC (G : StochasticMultiplicative μ) (n H : ℕ) :
    Measurable fun ω => windowSumC (G.g ω) n H := by
  unfold windowSumC
  exact Finset.measurable_sum _ fun h _ => G.measurable (n + h)

/-- Almost every sample's step-one partial sum is bounded by its length. -/
theorem ae_norm_apSumC_le (G : StochasticMultiplicative μ) (d n : ℕ) :
    ∀ᵐ ω ∂μ, ‖apSumC (G.g ω) d n‖ ≤ n := by
  filter_upwards [G.unimodular_ae] with ω hω
  exact norm_apSumC_le _ (fun k => (hω k).le) d n

/-- The squared partial-sum norms are integrable over a finite measure (bounded measurable). -/
theorem integrable_normSq_apSumC [IsFiniteMeasure μ] (G : StochasticMultiplicative μ)
    (d n : ℕ) :
    MeasureTheory.Integrable (fun ω => ‖apSumC (G.g ω) d n‖ ^ 2) μ := by
  refine (MeasureTheory.integrable_const ((n : ℝ) ^ 2)).mono'
    ((((G.measurable_apSumC d n).norm).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [G.ae_norm_apSumC_le d n] with ω hω
  have h0 : (0 : ℝ) ≤ ‖apSumC (G.g ω) d n‖ := norm_nonneg _
  simpa [abs_of_nonneg (pow_nonneg h0 2)] using pow_le_pow_left₀ h0 hω 2

end StochasticMultiplicative

/-- **Van der Corput input** (Tao 2015 §3, first step): if the partial-sum second moments are
uniformly bounded by `C`, every window second moment is bounded by `4·C` — the window sum is
an increment of partial sums, and `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²`.

This is the standing bound the van der Corput expansion contradicts: the squared window sum
expands into `H` diagonal terms plus shift correlations, so a bound independent of `H` forces
large negative correlations. -/
theorem windowSndMoment_le [IsProbabilityMeasure μ] (G : StochasticMultiplicative μ)
    {C : ℝ} (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C) (n H : ℕ) :
    ∫ ω, ‖windowSumC (G.g ω) n H‖ ^ 2 ∂μ ≤ 4 * C := by
  have hpt : ∀ ω : Ω, ‖windowSumC (G.g ω) n H‖ ^ 2
      ≤ 2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2 := by
    intro ω
    rw [windowSumC_eq_apSumC_sub]
    set a := apSumC (G.g ω) 1 (n + H)
    set b := apSumC (G.g ω) 1 n
    have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  have hint : MeasureTheory.Integrable
      (fun ω => 2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2) μ :=
    ((G.integrable_normSq_apSumC 1 (n + H)).const_mul 2).add
      ((G.integrable_normSq_apSumC 1 n).const_mul 2)
  calc ∫ ω, ‖windowSumC (G.g ω) n H‖ ^ 2 ∂μ
      ≤ ∫ ω, (2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2) ∂μ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
        · exact Filter.Eventually.of_forall fun ω => sq_nonneg _
        · exact Filter.Eventually.of_forall hpt
    _ = 2 * sndMomentPartialSum G (n + H) + 2 * sndMomentPartialSum G n := by
        rw [MeasureTheory.integral_add ((G.integrable_normSq_apSumC 1 (n + H)).const_mul 2)
          ((G.integrable_normSq_apSumC 1 n).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        rfl
    _ ≤ 2 * C + 2 * C := by
        have h1 := hC (n + H)
        have h2 := hC n
        nlinarith
    _ = 4 * C := by ring

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
