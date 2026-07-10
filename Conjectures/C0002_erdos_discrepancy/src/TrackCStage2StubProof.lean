import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 2 stub derived normal forms (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains proved normal-form wrappers derived from the single Stage-2 axiom stub
`stage2Stub_exists_params_one_le_unboundedDiscOffset`, stated at the chosen stub parameters
`stage2Stub_d` / `stage2Stub_m`.

Historical note: an earlier version of these wrappers was specialized to hard-wired parameters
`d = 1`, `m = 0`. That specialization was only provable because the old axiom (unbounded plain
partial sums for *every* sign sequence) was false; with the honest existential axiom the
parameters are opaque chosen values, so every wrapper below is stated at
`stage2Stub_d f hf` / `stage2Stub_m f hf`.

We keep these lemmas out of `TrackCStage2Stub.lean` so that hard-gate consumers (Stage 3,
`ErdosDiscrepancy.lean`) only compile the axiom stub and the construction of `stage2Out`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Stub reduction definitional rewrites

These simp lemmas were previously in `TrackCStage2Stub.lean`, but they are not needed by the
hard-gate Stage-3 pipeline. We keep them here so `TrackCStage2Stub` stays minimal.
-/

/-- The reduced sequence in the default stub reduction is the original sequence shifted by the
chosen affine-tail start `stage2Stub_m * stage2Stub_d`.

This is the `g_eq` contract of `ReductionOutput.ofShift` at the chosen stub parameters.
-/
@[simp] theorem stage2Stub_out1_g (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    (stage2Stub_out1 (f := f) (hf := hf)).g k =
      f (k + stage2Stub_m (f := f) (hf := hf) * stage2Stub_d (f := f) (hf := hf)) := by
  simp [stage2Stub_out1, Tao2015.ReductionOutput.ofShift]

/-- Function-level rewrite for the reduced sequence in the default stub reduction.

This is `stage2Stub_out1_g` bundled as an equality of functions; it is convenient when rewriting
a whole `g` argument (rather than pointwise applications `g k`).
-/
@[simp] theorem stage2Stub_out1_g_fun (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out1 (f := f) (hf := hf)).g =
      fun k => f (k + stage2Stub_m (f := f) (hf := hf) * stage2Stub_d (f := f) (hf := hf)) := by
  funext k
  simp [stage2Stub_out1_g]

/-- The default stub reduction uses the chosen step size `stage2Stub_d`. -/
@[simp] theorem stage2Stub_out1_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out1 (f := f) (hf := hf)).d = stage2Stub_d (f := f) (hf := hf) := by
  simp [stage2Stub_out1, Tao2015.ReductionOutput.ofShift]

/-- The default stub reduction uses the chosen offset parameter `stage2Stub_m`. -/
@[simp] theorem stage2Stub_out1_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out1 (f := f) (hf := hf)).m = stage2Stub_m (f := f) (hf := hf) := by
  simp [stage2Stub_out1, Tao2015.ReductionOutput.ofShift]

/-- The Stage-1 reduction packaged inside the default Stage-2 stub output is `stage2Stub_out1`.

This lemma is intentionally tiny: it lets downstream code reason about the reduction parameters
(`d`, `m`, `g`) carried by the stub without unfolding `stage2Stub_out`.
-/
@[simp] theorem stage2Stub_out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out (f := f) (hf := hf)).out1 = stage2Stub_out1 (f := f) (hf := hf) := by
  classical
  simp [stage2Stub_out]

/-- The default stub Stage-2 output uses the chosen step size `stage2Stub_d` in its Stage-1
reduction. -/
@[simp] theorem stage2Stub_out_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out (f := f) (hf := hf)).out1.d = stage2Stub_d (f := f) (hf := hf) := by
  simp

/-- The reduced sequence in the default stub Stage-2 output is the original sequence shifted by
the chosen affine-tail start. -/
@[simp] theorem stage2Stub_out_g (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    (stage2Stub_out (f := f) (hf := hf)).out1.g k =
      f (k + stage2Stub_m (f := f) (hf := hf) * stage2Stub_d (f := f) (hf := hf)) := by
  simp [stage2Stub_out1_g]

/-- The default stub Stage-2 output uses the chosen offset parameter `stage2Stub_m` in its Stage-1
reduction. -/
@[simp] theorem stage2Stub_out_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out (f := f) (hf := hf)).out1.m = stage2Stub_m (f := f) (hf := hf) := by
  simp [stage2Stub_out1_m]

/-!
## Derived normal forms at the chosen stub parameters
-/

/-- Fixed-step unboundedness form of the Stage-2 stub assumption, along the reduced sequence.

This is `stage2Stub_unboundedDiscOffset` transported across the Stage-1 contract
`ReductionOutput.unboundedDiscrepancyAlong_iff_unboundedDiscOffset`.
-/
theorem stage2Stub_unboundedDiscrepancyAlong_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscrepancyAlong
      (stage2Stub_out1 (f := f) (hf := hf)).g
      (stage2Stub_out1 (f := f) (hf := hf)).d := by
  exact
    ((stage2Stub_out1 (f := f) (hf := hf)).unboundedDiscrepancyAlong_iff_unboundedDiscOffset
          (f := f)).2
      (stage2Stub_unboundedDiscOffset (f := f) (hf := hf))

/-- Discrepancy-wrapper witness form of the Stage-2 stub assumption.

Normal form:
`∀ B, ∃ n, n > 0 ∧ discrepancy (stage2Stub_out1 ...).g (stage2Stub_out1 ...).d n > B`.

This is `stage2Stub_unboundedDiscrepancyAlong_params` rewritten using the generic
witness-positivity lemma `UnboundedDiscrepancyAlong.forall_exists_discrepancy_gt'_witness_pos`.
-/
theorem stage2Stub_forall_exists_discrepancy_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      discrepancy (stage2Stub_out1 (f := f) (hf := hf)).g
        (stage2Stub_out1 (f := f) (hf := hf)).d n > B := by
  -- Delegate to the generic unboundedness witness form.
  exact
    UnboundedDiscrepancyAlong.forall_exists_discrepancy_gt'_witness_pos
      (g := (stage2Stub_out1 (f := f) (hf := hf)).g)
      (d := (stage2Stub_out1 (f := f) (hf := hf)).d)
      (stage2Stub_unboundedDiscrepancyAlong_params (f := f) (hf := hf))

/-- Stable boundedness-negation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, BoundedDiscOffset f (stage2Stub_d ...) (stage2Stub_m ...) B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset`.
-/
theorem stage2Stub_not_exists_boundedDiscOffset_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) B := by
  have hunb :
      Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f)
          (d := stage2Stub_d (f := f) (hf := hf)) (m := stage2Stub_m (f := f) (hf := hf))).1
      hunb

/-- Stable `discOffset` boundedness-negation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, discOffset f (stage2Stub_d ...) (stage2Stub_m ...) n ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem stage2Stub_not_exists_forall_discOffset_le_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ,
      discOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) n ≤ B := by
  have hunb :
      Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f)
          (d := stage2Stub_d (f := f) (hf := hf)) (m := stage2Stub_m (f := f) (hf := hf))).1
      hunb

/-- Witness-positivity normal form of the Stage-2 stub assumption, stated directly for the bundled
offset discrepancy wrapper `discOffset`.

Normal form:
`∀ B, ∃ n, n > 0 ∧ discOffset f (stage2Stub_d ...) (stage2Stub_m ...) n > B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via the generic witness-positivity lemma
`Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos`.
-/
theorem stage2Stub_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      discOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) n > B := by
  have hunb :
      Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos
      (f := f) (d := stage2Stub_d (f := f) (hf := hf))
      (m := stage2Stub_m (f := f) (hf := hf)) hunb)

/-- Stable `apSumFrom` normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f (stage2Stub_m ... * stage2Stub_d ...) (stage2Stub_d ...) n) ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem stage2Stub_not_exists_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ,
      Int.natAbs
          (apSumFrom f
            (stage2Stub_m (f := f) (hf := hf) * stage2Stub_d (f := f) (hf := hf))
            (stage2Stub_d (f := f) (hf := hf)) n) ≤ B := by
  have hunb :
      Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le
        (f := f) (d := stage2Stub_d (f := f) (hf := hf))
        (m := stage2Stub_m (f := f) (hf := hf))).1
      hunb

/-- Witness form of the Stage-2 stub assumption for the affine-tail nuclei at the chosen
parameters.

Normal form:
`∀ B, ∃ n, n > 0 ∧ Int.natAbs (apSumFrom f (stage2Stub_m ... * stage2Stub_d ...) (stage2Stub_d ...) n) > B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten using
`Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2Stub_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      Int.natAbs
          (apSumFrom f
            (stage2Stub_m (f := f) (hf := hf) * stage2Stub_d (f := f) (hf := hf))
            (stage2Stub_d (f := f) (hf := hf)) n) > B := by
  have hunb :
      Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
        (f := f) (d := stage2Stub_d (f := f) (hf := hf))
        (m := stage2Stub_m (f := f) (hf := hf)) hunb)

/-- Paper-notation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, Int.natAbs ((Finset.Icc (m+1) (m+n)).sum (fun i => f (i * d))) ≤ B`
at the chosen parameters `d = stage2Stub_d ...`, `m = stage2Stub_m ...`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le`.
-/
theorem stage2Stub_not_exists_forall_natAbs_sum_Icc_offset_le (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ,
      Int.natAbs
          ((Finset.Icc (stage2Stub_m (f := f) (hf := hf) + 1)
            (stage2Stub_m (f := f) (hf := hf) + n)).sum
            (fun i => f (i * stage2Stub_d (f := f) (hf := hf)))) ≤ B := by
  have hunb :
      Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
        (stage2Stub_m (f := f) (hf := hf)) :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  simpa using
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le
        (f := f) (d := stage2Stub_d (f := f) (hf := hf))
        (m := stage2Stub_m (f := f) (hf := hf))).1
      hunb

end Tao2015

end MoltResearch
