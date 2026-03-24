import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file houses the Stage-2 conjecture/axiom stub.

Keeping the stub separate lets `TrackCStage2.lean` remain mostly “API + wiring”, while the
non-verified analytic content stays isolated behind a dedicated import.
-/

namespace MoltResearch

namespace Tao2015

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, produce a Stage-1 reduction output and show that the reduced sequence
has unbounded discrepancy along its associated fixed step.

This is an axiom stub for now; it serves as the typed seam between Stage 1 (pure index gymnastics)
and later analytic/combinatorial stages.
-/
axiom stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f

/-- Stage 2 yields some concrete parameters `d, m` such that the bundled offset discrepancy family
`discOffset f d m` is unbounded.

This existential packaging is often more convenient for later analytic stages than working
directly with the stage record fields.
-/
theorem stage2_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  simpa using
    (Stage2Output.exists_params_unboundedDiscOffset (f := f) (stage2 (f := f) (hf := hf)))

/-- Stage 2 yields concrete parameters `d, m` such that the affine-tail nucleus
`apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is the explicit witness family form often consumed by later analytic stages.
-/
theorem stage2_exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, C < Int.natAbs (apSumFrom f (m * d) d n)) := by
  simpa using
    (Stage2Output.exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (stage2 (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 2 already yields the global conclusion `¬ BoundedDiscrepancy f`.

This is a thin wrapper around the proved lemma `Stage2Output.notBoundedOriginal`.
-/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact Stage2Output.notBoundedOriginal (f := f) (stage2 (f := f) (hf := hf))

/-- Stage 2 output implies the usual "∀ C, HasDiscrepancyAtLeast f C" surface statement.

This is a thin wrapper around `Stage2Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2 (f := f) (hf := hf)))

/-- Stage 2 yields the most pipeline-friendly global witness form:

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around `Stage2Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  simpa using
    (Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) (stage2 (f := f) (hf := hf)))

end Tao2015

end MoltResearch
