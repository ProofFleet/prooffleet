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

/-- Stage 2 yields unbounded discrepancy for the reduced sequence, stated using the verified core
predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around `Stage2Output.unboundedDiscrepancyAlong_core`.
-/
theorem stage2_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong (Stage2Output.g (stage2 (f := f) (hf := hf)))
      (Stage2Output.d (stage2 (f := f) (hf := hf))) := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.unboundedDiscrepancyAlong_core (f := f) out)

/-- Stage 2 yields unboundedness of the bundled offset discrepancy family
`discOffset f d m`, for the concrete parameters coming from Stage 1.

This is a thin wrapper around the proved lemma `Stage2Output.unboundedDiscOffset`.
-/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2 (f := f) (hf := hf)).out1.d (stage2 (f := f) (hf := hf)).out1.m := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.unboundedDiscOffset (f := f) out)

/-- Stage 2 yields some concrete parameters `d, m` such that the bundled offset discrepancy family
`discOffset f d m` is unbounded.

This existential packaging is often more convenient for later analytic stages than working
directly with the stage record fields.
-/
theorem stage2_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.exists_params_unboundedDiscOffset (f := f) out)

/-- Stage 2 yields some concrete parameters `d, m` with `1 ≤ d` such that the bundled offset discrepancy family
`discOffset f d m` is unbounded.

Many later stages use the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem stage2_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.exists_params_one_le_unboundedDiscOffset (f := f) out)

/-- Stage 2 yields some concrete parameters `d, m` such that the bundled offset discrepancy family
`discOffset f d m` has arbitrarily large values.

This is the explicit witness-family form of `stage2_exists_params_unboundedDiscOffset`.
-/
theorem stage2_exists_params_forall_exists_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.exists_params_forall_exists_discOffset_gt (f := f) out)

/-- Stage 2 yields an explicit unbounded witness family for the bundled offset discrepancy
`discOffset f d m`, for the concrete parameters `d, m` coming from the Stage-1 reduction record.

This is a small normal-form convenience lemma: later analytic stages often want to stay at the
`discOffset` level rather than unpacking `Stage2Output` fields.
-/
theorem stage2_forall_exists_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ,
      B < discOffset f (Stage2Output.d (stage2 (f := f) (hf := hf)))
        (Stage2Output.m (stage2 (f := f) (hf := hf))) n := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out, Stage2Output.d, Stage2Output.m] using (Stage2Output.forall_exists_discOffset_gt (f := f) out)

/-- Inequality-direction variant of `stage2_forall_exists_discOffset_gt`, written as
`discOffset f d m n > B`.

Many analytic consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem stage2_forall_exists_discOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ,
      discOffset f (Stage2Output.d (stage2 (f := f) (hf := hf)))
        (Stage2Output.m (stage2 (f := f) (hf := hf))) n > B := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out, Stage2Output.d, Stage2Output.m] using (Stage2Output.forall_exists_discOffset_gt' (f := f) out)

/-- Stage 2 yields bundled offset nucleus witnesses at the concrete parameters coming from Stage 1.

This is the same unboundedness witness as `stage2_forall_exists_discOffset_gt'`, but expanded to the
raw nucleus `apSumOffset`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs (apSumOffset f (Stage2Output.d (stage2 (f := f) (hf := hf)))
        (Stage2Output.m (stage2 (f := f) (hf := hf))) n) > B := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out, Stage2Output.d, Stage2Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt' (f := f) out)

/-- Stage 2 yields concrete parameters `d, m` such that the affine-tail nucleus
`apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is the explicit witness family form often consumed by later analytic stages.
-/
theorem stage2_exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f := f) out)

/-- Consumer-facing shortcut: Stage 2 already yields the global conclusion `¬ BoundedDiscrepancy f`.

This is a thin wrapper around the proved lemma `Stage2Output.notBoundedOriginal`.
-/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.notBoundedOriginal (f := f) out)

/-- Stage 2 output implies the usual "∀ C, HasDiscrepancyAtLeast f C" surface statement.

This is a thin wrapper around `Stage2Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.forall_hasDiscrepancyAtLeast (f := f) out)

/-- Stage 2 yields the most pipeline-friendly global witness form:

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around `Stage2Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out] using (Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) out)

/-- Negation-normal-form boundedness statement for the concrete Stage-2 parameters.

This is a thin wrapper around `Stage2Output.not_exists_boundedDiscOffset`.
-/
theorem stage2_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        BoundedDiscOffset f (Stage2Output.d (stage2 (f := f) (hf := hf)))
          (Stage2Output.m (stage2 (f := f) (hf := hf))) B := by
  let out := stage2 (f := f) (hf := hf)
  simpa [out, Stage2Output.d, Stage2Output.m] using (Stage2Output.not_exists_boundedDiscOffset (f := f) out)

end Tao2015

end MoltResearch
