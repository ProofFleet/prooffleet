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

Axiom hygiene (issue #2843 / card §6): this is a `class` with **no instance and no axiom** —
consumers take it as an explicit hypothesis or instance argument. An instance may only ever be
provided by an actual proof of the reduction. The paper's reduction is *stochastic* (bounded
second moment of a random multiplicative function); this deterministic form is implied by it
and intentionally simpler — when the language layer gains probability packaging, the stochastic
form becomes the primary and this one is re-derived (card §6, "Deterministic vs stochastic").
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

end Tao2015

end MoltResearch
