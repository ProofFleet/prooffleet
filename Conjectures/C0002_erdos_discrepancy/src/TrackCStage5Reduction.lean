import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Multiplicative
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Fourier

/-!
# Track C: Stage 5 reduction — fixed-step content on the reduced class

This file is **Conjectures-only** glue: the first piece of derivation (C) of the analytic-core
card (`Problems/tao2015_analytic_core.md`) — the fixed-step statement formerly isolated by the
Stage-2 stub, derived (with no nonstandard axioms) on the
**completely multiplicative subclass** from the universal-multiplicative hypothesis of the
Fourier-reduction interface (A) plus the verified multiplicative Stage-2 constructors.

Shape of the derivation:
1. The antecedent of `FourierReductionAssumption.reduce` — every completely multiplicative
   unimodular `g : ℕ → ℂ` has unbounded partial sums — instantiated at the coerced sequence
   `g := fun n => (f n : ℂ)` (via the language-layer bridges `CompletelyMultiplicative.toC`
   and `IsSignSequence.unimodularC`),
2. transferred back to ℤ by the norm-level cast bridge
   `norm_sum_Icc_intCast_eq_natAbs_apSum_one`, yields `UnboundedDiscrepancy f 1`,
3. which flows through the verified constructor `Stage2Output.ofUnboundedDiscrepancyOne` and
   the boundary packaging `Stage2Output.exists_params_one_le_unboundedDiscOffset`.

Historically, this made precise what remained for retiring the stub: discharge the
universal-multiplicative hypothesis and route the general-`f` case through the Fourier reduction.
The unconditional Track-R proof now completes that route independently of the legacy Stage-2 plane.
-/

namespace MoltResearch

namespace Tao2015

variable {f : ℕ → ℤ}

/-- Step-one unbounded discrepancy for a completely multiplicative sign sequence, from the
universal-multiplicative hypothesis (the antecedent of `FourierReductionAssumption.reduce`),
instantiated at the coerced sequence and transferred back to ℤ by the norm-level cast bridge. -/
theorem unboundedDiscrepancy_one_of_univ_multiplicative
    (huniv : ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
      ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖)
    (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f) :
    UnboundedDiscrepancy f 1 := by
  intro B
  rcases huniv (fun n => (f n : ℂ)) hmul.toC hf.unimodularC (B : ℝ) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hn' : (B : ℝ) < ((apSum f 1 n).natAbs : ℝ) := by
    have hn0 : (B : ℝ) < ‖∑ j ∈ Finset.Icc 1 n, ((f j : ℂ))‖ := hn
    rwa [norm_sum_Icc_intCast_eq_natAbs_apSum_one f n] at hn0
  rw [discrepancy_eq_natAbs_apSum]
  exact_mod_cast hn'

/-- **Fixed-step content on the reduced class** (first piece of derivation (C); standard axioms
only): for a completely multiplicative sign sequence, the universal-multiplicative hypothesis
yields

`∃ d m, 1 ≤ d ∧ UnboundedDiscOffset f d m`.
-/
theorem stage2StubContent_of_univ_multiplicative
    (huniv : ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
      ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖)
    (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m :=
  (Stage2Output.ofUnboundedDiscrepancyOne (f := f) hf
      (unboundedDiscrepancy_one_of_univ_multiplicative huniv hmul hf)).exists_params_one_le_unboundedDiscOffset

-- Consumer example (compile-only): on the multiplicative subclass, the analytic-core
-- hypothesis feeds the whole verified Stage-2 boundary — EDP out the other side, no stub.
example (huniv : ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
      ∀ C : ℝ, ∃ n : ℕ, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖)
    (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f :=
  (Stage2Output.ofUnboundedDiscrepancyOne (f := f) hf
      (unboundedDiscrepancy_one_of_univ_multiplicative huniv hmul hf)).notBoundedOriginal

end Tao2015

end MoltResearch
