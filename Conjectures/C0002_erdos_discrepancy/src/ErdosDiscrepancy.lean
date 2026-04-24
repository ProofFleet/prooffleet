import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file is **Conjectures-only**: it may rely on axiom stubs (notably the Stage-2 stub). Verified,
reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- Trivial base case: any sign sequence has discrepancy at least 0. -/
theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  exact IsSignSequence.hasDiscrepancyAtLeast_zero (hf := hf)

-- Tao 2015 proof skeleton lives in `Conjectures.C0002_erdos_discrepancy.src.Tao2015`.

/-- Erdős discrepancy theorem in boundedness-negation normal form.

This is the core Track C output: it is the minimal statement from which the usual witness forms
follow.
-/
theorem erdos_discrepancy_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  -- Delegate to the minimal Stage-3 entry-point API.
  exact Tao2015.stage3_notBounded (f := f) (hf := hf)

/-- Stable boundedness-negation packaging of the Stage-3 offset-discrepancy witness.

Normal form:
`¬ ∃ B, BoundedDiscOffset f (stage3Out ...).d (stage3Out ...).m B`.

This is a small convenience wrapper around `Tao2015.stage3_not_exists_boundedDiscOffset`.
-/
theorem erdos_discrepancy_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (Tao2015.stage3Out (f := f) (hf := hf)).d
        (Tao2015.stage3Out (f := f) (hf := hf)).m B := by
  exact Tao2015.stage3_not_exists_boundedDiscOffset (f := f) (hf := hf)

/-- Negation-normal-form packaging of the Stage-3 offset-discrepancy witness family.

Normal form:
`¬ ∃ B, ∀ n, discOffset f (stage3Out ...).d (stage3Out ...).m n ≤ B`.

This is a small convenience wrapper around `Tao2015.stage3_unboundedDiscOffset` and the
equivalence `Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem erdos_discrepancy_not_exists_forall_discOffset_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      ∀ n : ℕ,
        discOffset f
          (Tao2015.stage3Out (f := f) (hf := hf)).d
          (Tao2015.stage3Out (f := f) (hf := hf)).m n ≤ B := by
  set out := Tao2015.stage3Out (f := f) (hf := hf) with hout
  have hunb : Tao2015.UnboundedDiscOffset f out.d out.m := by
    simpa [hout] using (Tao2015.stage3_unboundedDiscOffset (f := f) (hf := hf))
  simpa [hout] using
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f) (d := out.d) (m := out.m)).1
      hunb

/-- Existential packaging of `erdos_discrepancy_not_exists_boundedDiscOffset`.

Normal form:
`∃ d m, 1 ≤ d ∧ ¬ ∃ B, BoundedDiscOffset f d m B`.

This is a small convenience wrapper around
`Tao2015.stage3_exists_params_one_le_not_exists_boundedDiscOffset`.
-/
theorem erdos_discrepancy_exists_params_one_le_not_exists_boundedDiscOffset (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  exact Tao2015.stage3_exists_params_one_le_not_exists_boundedDiscOffset (f := f) (hf := hf)

/-- Stable packaging of the Stage-3 offset-discrepancy unboundedness witness.

Normal form:
`UnboundedDiscOffset f (stage3Out ...).d (stage3Out ...).m`.

This is a small convenience wrapper around `Tao2015.stage3_unboundedDiscOffset`.
-/
theorem erdos_discrepancy_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscOffset f
      (Tao2015.stage3Out (f := f) (hf := hf)).d
      (Tao2015.stage3Out (f := f) (hf := hf)).m := by
  exact Tao2015.stage3_unboundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging of `erdos_discrepancy_unboundedDiscOffset`.

Normal form:
`∃ d m, d > 0 ∧ UnboundedDiscOffset f d m`.

This is a small convenience wrapper around `Tao2015.stage3_exists_params_unboundedDiscOffset`.
-/
theorem erdos_discrepancy_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ Tao2015.UnboundedDiscOffset f d m := by
  exact Tao2015.stage3_exists_params_unboundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging of `erdos_discrepancy_unboundedDiscOffset`.

Normal form:
`∃ d m, 1 ≤ d ∧ UnboundedDiscOffset f d m`.

This is a small convenience wrapper around
`Tao2015.stage3_exists_params_one_le_unboundedDiscOffset`.
-/
theorem erdos_discrepancy_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ Tao2015.UnboundedDiscOffset f d m := by
  exact Tao2015.stage3_exists_params_one_le_unboundedDiscOffset (f := f) (hf := hf)

/-- Negation-normal-form packaging of the Stage-3 affine-tail witness.

Normal form:
`∃ d m, 1 ≤ d ∧ ¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f (m*d) d n) ≤ B`.

This is `erdos_discrepancy_exists_params_one_le_unboundedDiscOffset` rewritten using
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem erdos_discrepancy_exists_params_one_le_not_exists_forall_natAbs_apSumFrom_mul_le
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ B := by
  rcases erdos_discrepancy_exists_params_one_le_unboundedDiscOffset (f := f) (hf := hf) with
    ⟨d, m, hd, hunb⟩
  refine ⟨d, m, hd, ?_⟩
  exact
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le (f := f)
        (d := d) (m := m)).1
      hunb

/-- Track C pipeline witness: Stage 3 yields unbounded discrepancy along the reduced sequence,
stated using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a small convenience wrapper around
`Tao2015.Stage3Output.unboundedDiscrepancyAlong_core`.
-/
theorem erdos_discrepancy_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscrepancyAlong
      (Tao2015.stage3Out (f := f) (hf := hf)).g
      (Tao2015.stage3Out (f := f) (hf := hf)).d := by
  exact Tao2015.stage3_unboundedDiscrepancyAlong_core (f := f) (hf := hf)

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is the usual surface statement `∀ C, HasDiscrepancyAtLeast f C` derived from the core
Track-C output `¬ BoundedDiscrepancy f`.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Delegate to the minimal Stage-3 entry-point API.
  exact Tao2015.stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)

/-- Witness form of `erdos_discrepancy` directly in terms of the nucleus `apSum`.

Normal form:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly witness normal form: it avoids the `discrepancy` wrapper.
-/
theorem erdos_discrepancy_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact Tao2015.stage3_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf)

/-- Witness form of `erdos_discrepancy`, stated using the `discrepancy` wrapper.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is the most direct discrepancy-wrapper witness form.
-/
theorem erdos_discrepancy_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  exact Tao2015.stage3_forall_exists_discrepancy_gt (f := f) (hf := hf)

/-- Positive-length witness form of `erdos_discrepancy_forall_exists_discrepancy_gt`.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ discrepancy f d n > C`.

We keep this lemma in the hard-gate file since it is a common consumption pattern, and it does not
require importing the larger witness-corollary module.
-/
theorem erdos_discrepancy_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  exact Tao2015.stage3_forall_exists_discrepancy_gt_witness_pos (f := f) (hf := hf)

/-- Specialization of `erdos_discrepancy` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem erdos_discrepancy_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (erdos_discrepancy (f := f) (hf := hf)) C

/-!
Additional witness-form corollaries live in
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancyWitnesses`.

We keep this file minimal so the Track-C hard-gate build can compile quickly.
-/

end MoltResearch
