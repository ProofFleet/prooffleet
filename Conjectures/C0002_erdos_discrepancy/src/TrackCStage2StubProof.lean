import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 2 stub derived normal forms (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains proved normal-form wrappers derived from the single Stage-2 axiom stub
`stage2Stub_unboundedDiscOffset_params`, specialized to the default stub parameters `d = 1`,
`m = 0`.

We keep these lemmas out of `TrackCStage2Stub.lean` so that hard-gate consumers (Stage 3,
`ErdosDiscrepancy.lean`) only compile the axiom stub and the construction of `stage2Out`.
-/

namespace MoltResearch

namespace Tao2015

/-- Parameter-normal form of the Stage-2 stub assumption as fixed-step unboundedness.

This is `stage2Stub_unboundedDiscOffset_params` transported across the Stage-1 contract
`ReductionOutput.unboundedDiscrepancyAlong_iff_unboundedDiscOffset`, then simplified using the
stub parameters `g = f` and `d = 1`.
-/
theorem stage2Stub_unboundedDiscrepancyAlong_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscrepancyAlong f 1 := by
  have hunb :
      Tao2015.UnboundedDiscrepancyAlong
        (stage2Stub_out1 (f := f) (hf := hf)).g
        (stage2Stub_out1 (f := f) (hf := hf)).d := by
    exact
      ((stage2Stub_out1 (f := f) (hf := hf)).unboundedDiscrepancyAlong_iff_unboundedDiscOffset
            (f := f)).2
        (stage2Stub_unboundedDiscOffset (f := f) (hf := hf))
  simpa using hunb

/-- Discrepancy-wrapper witness form of the Stage-2 stub assumption.

Normal form:
`∀ B, ∃ n, n > 0 ∧ discrepancy f 1 n > B`.

This is `stage2Stub_unboundedDiscrepancyAlong_params` rewritten using the generic witness-positivity
lemma `UnboundedDiscrepancyAlong.forall_exists_discrepancy_gt'_witness_pos`.
-/
theorem stage2Stub_forall_exists_discrepancy_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ discrepancy f 1 n > B := by
  -- Delegate to the generic unboundedness witness form.
  exact
    UnboundedDiscrepancyAlong.forall_exists_discrepancy_gt'_witness_pos
      (g := f) (d := 1) (stage2Stub_unboundedDiscrepancyAlong_params (f := f) (hf := hf))

/-- Stable boundedness-negation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, BoundedDiscOffset f 1 0 B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset`.
-/
theorem stage2Stub_not_exists_boundedDiscOffset_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f 1 0 B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := 1) (m := 0)).1
      hunb

/-- Stable `discOffset` boundedness-negation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, discOffset f 1 0 n ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem stage2Stub_not_exists_forall_discOffset_le_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f 1 0 n ≤ B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f) (d := 1) (m := 0)).1
      hunb

/-- Stable `apSumFrom` normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f 0 1 n) ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem stage2Stub_not_exists_forall_natAbs_apSumFrom_zero_one_le (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f 0 1 n) ≤ B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  -- `m*d` simplifies to `0` at the stub parameters `m = 0`, `d = 1`.
  simpa using
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le
        (f := f) (d := 1) (m := 0)).1
      hunb

/-- Witness form of the Stage-2 stub assumption for the affine-tail nuclei `apSumFrom f 0 1 n`.

Normal form:
`∀ B, ∃ n, n > 0 ∧ Int.natAbs (apSumFrom f 0 1 n) > B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten using
`Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2Stub_forall_exists_natAbs_apSumFrom_zero_one_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f 0 1 n) > B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  -- `m*d` simplifies to `0` at the stub parameters `m = 0`, `d = 1`.
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
        (f := f) (d := 1) (m := 0) hunb)

/-- Paper-notation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, Int.natAbs ((Finset.Icc 1 n).sum (fun i => f i)) ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le`.
-/
theorem stage2Stub_not_exists_forall_natAbs_sum_Icc_one_le (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs ((Finset.Icc 1 n).sum (fun i => f i)) ≤ B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  -- Rewrite the general `Icc (m+1) (m+n)` form at the stub parameters `m = 0`, `d = 1`.
  simpa using
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le
        (f := f) (d := 1) (m := 0)).1
      hunb

end Tao2015

end MoltResearch
