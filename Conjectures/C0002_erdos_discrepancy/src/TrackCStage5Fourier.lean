import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 interface — Fourier reduction assumption (Tao 2015, input (A))

This file is **Conjectures-only** glue: the typed statement of the first deep input of
Tao's Erdős-discrepancy proof, as an interface class in the Track C stub discipline
(`Problems/tao2015_analytic_core.md`, interface layer).

**(A) Fourier reduction** (arXiv:1509.05363 §2, building on Polymath5), deterministic first
cut: to prove EDP it suffices to show that every completely multiplicative unimodular
`g : ℕ → ℂ` has unbounded partial sums. Stated conditionally, exactly as on the card:
if the universal-multiplicative unboundedness statement holds, then every sign sequence has
unbounded discrepancy.

Axiom hygiene (issue #2843 / card §6): these are `class`es with **no unconditional instance and
no axiom** — consumers take them as explicit hypotheses or instance arguments. An instance may
only ever be provided by an actual proof of the reduction.

**Strength warning (corrects an earlier docstring and the blueprint card's §6 record):** the
paper's §2 reduction is *stochastic* — a bounded-discrepancy sequence yields a random completely
multiplicative function with bounded second moment of partial sums
(`FourierReductionStochasticAssumption` below). The deterministic form
(`FourierReductionAssumption`) is **stronger**, not weaker: it implies the stochastic form via
the point-mass embedding (`instance` below), while the converse is not derivable — a stochastic
counterexample with bounded second moments need not concentrate on any single deterministic
sequence with bounded partial sums. Since the deterministic conditional is not a named theorem
of the paper, derivation-(C) work must consume `FourierReductionStochasticAssumption` only; the
deterministic class is retained as a convenience for toy consumers.
-/

namespace MoltResearch

namespace Tao2015

/-- **Fourier reduction assumption** (Tao 2015, arXiv:1509.05363 §2; deterministic first cut).

If every completely multiplicative unimodular `g : ℕ → ℂ` has unbounded partial sums
`‖∑_{j ≤ n} g j‖`, then every sign sequence has unbounded discrepancy (EDP).

No instance of this class is (or may be) declared in this repository until the reduction is
actually proved; consumers must carry it as a hypothesis.
-/
class FourierReductionAssumption : Prop where
  reduce :
    (∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
        ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖) →
      ∀ f : ℕ → ℤ, IsSignSequence f → ¬ BoundedDiscrepancy f

/-- Consumer-facing restatement of the reduction as a plain theorem, so call sites can use it
without projecting the class field. -/
theorem fourierReduction_notBounded [inst : FourierReductionAssumption]
    (huniv : ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
      ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖)
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  inst.reduce huniv f hf

-- Consumer example (compile-only): from the interface plus a hypothesized
-- universal-multiplicative witness, EDP for any sign sequence is one application.
example [FourierReductionAssumption]
    (huniv : ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
      ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖)
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  fourierReduction_notBounded huniv f hf

/-- **Stochastic Fourier reduction assumption** (Tao 2015, arXiv:1509.05363 §2, faithful form).

If EDP fails — some sign sequence has bounded discrepancy — then there is a probability space
carrying a stochastic completely multiplicative unimodular function whose partial sums have
uniformly bounded second moment `𝔼|∑_{j≤n} 𝐠(j)|² ≤ C`. This is the exact §2 output (the
contrapositive of "Theorem 1.8 implies Theorem 1.1"); derivation (C) must consume this class,
not the stronger deterministic one.

The reduction is now formalized: `TrackCStage5FourierProof.lean` declares the unconditional
instance from the nucleus chain (`MoltResearch/Discrepancy/`, P1-P8 of issue #2920).
-/
class FourierReductionStochasticAssumption : Prop where
  reduce :
    ∀ f : ℕ → ℤ, IsSignSequence f → BoundedDiscrepancy f →
      ∃ (Ω : Type) (m : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω m)
        (_ : @MeasureTheory.IsProbabilityMeasure Ω m μ)
        (G : @StochasticMultiplicative Ω m μ) (C : ℝ),
        ∀ n : ℕ, @sndMomentPartialSum Ω m μ G n ≤ C

/-- The deterministic reduction implies the stochastic one: if the deterministic conditional
holds and some sign sequence has bounded discrepancy, then (contrapositive) some completely
multiplicative unimodular `g` has uniformly bounded partial sums, and its point-mass embedding
is a stochastic counterexample with the same (squared) bound.

This records the strength ordering deterministic ⇒ stochastic; the converse is not derivable.
-/
instance FourierReductionStochasticAssumption.ofDeterministic [inst : FourierReductionAssumption] :
    FourierReductionStochasticAssumption where
  reduce f hf hb := by
    have hnu : ¬ (∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
        ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖) := by
      intro h
      exact inst.reduce h f hf hb
    push_neg at hnu
    obtain ⟨g, hmul, hg, C, hC⟩ := hnu
    refine ⟨Unit, inferInstance, MeasureTheory.Measure.dirac (), inferInstance,
      StochasticMultiplicative.ofDeterministic _ g hmul hg, C ^ 2, ?_⟩
    intro n
    rw [StochasticMultiplicative.sndMomentPartialSum_ofDeterministic, apSumC_one_d]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC n) 2

-- Consumer example (compile-only): the stochastic interface hands derivation-(C) work a
-- probability-space counterexample package from any hypothesized bounded-discrepancy sequence.
example [FourierReductionStochasticAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) (hb : BoundedDiscrepancy f) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω m)
      (_ : @MeasureTheory.IsProbabilityMeasure Ω m μ)
      (G : @StochasticMultiplicative Ω m μ) (C : ℝ),
      ∀ n : ℕ, @sndMomentPartialSum Ω m μ G n ≤ C :=
  FourierReductionStochasticAssumption.reduce f hf hb

end Tao2015

end MoltResearch
