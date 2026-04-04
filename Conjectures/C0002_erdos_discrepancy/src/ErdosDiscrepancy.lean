import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file is **Conjectures-only**: it may rely on axiom stubs (and, if needed, `sorry`). Verified, reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- Trivial base case: any sign sequence has discrepancy at least 0. -/
theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  simpa using IsSignSequence.hasDiscrepancyAtLeast_zero (hf := hf)

-- Tao 2015 proof skeleton lives in `Conjectures.C0002_erdos_discrepancy.src.Tao2015`.

/-- Track C pipeline package: Stage-3 output for a sign sequence `f`. -/
noncomputable abbrev erdos_discrepancy_stage3Output (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.Stage3Output f :=
  Tao2015.stage3 (f := f) (hf := hf)

/-- Erdős discrepancy theorem in boundedness-negation normal form.

This is the core Track C output: it is the minimal statement from which the usual witness forms
follow.
-/
theorem erdos_discrepancy_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  -- Prefer consuming the Stage-3 output record API.
  exact (erdos_discrepancy_stage3Output (f := f) (hf := hf)).notBounded

/-- Track C pipeline witness: Stage 3 yields unbounded discrepancy along the reduced sequence,
stated using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a small convenience wrapper around
`Tao2015.Stage3Output.unboundedDiscrepancyAlong_core`.
-/
theorem erdos_discrepancy_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)).g
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)).d := by
  simpa using
    (Tao2015.Stage3Output.unboundedDiscrepancyAlong_core (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is the usual surface statement `∀ C, HasDiscrepancyAtLeast f C` exposed directly from the
Track-C Stage-3 pipeline.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Prefer the Stage-3 record API (`Stage3Output`) rather than the `stage3_...` wrappers.
  simpa using
    (Tao2015.Stage3Output.forall_hasDiscrepancyAtLeast (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Witness form of `erdos_discrepancy` directly in terms of the nucleus `apSum`.

This is the most pipeline-friendly surface statement:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ |apSum f d n| > C`.
-/
theorem erdos_discrepancy_apSum (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a thin wrapper around the Stage-3 packaging.
-/
theorem erdos_discrepancy_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ Tao2015.UnboundedDiscOffset f d m := by
  simpa using
    (Tao2015.Stage3Output.exists_params_unboundedDiscOffset (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_exists_params_unboundedDiscOffset` packaging the step-size side
condition as `1 ≤ d`.

Many later stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ Tao2015.UnboundedDiscOffset f d m := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_unboundedDiscOffset (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the bundled offset discrepancy family `discOffset f d m` takes arbitrarily large values.

This is the explicit witness-family form of `erdos_discrepancy_exists_params_unboundedDiscOffset`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_discOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_forall_exists_discOffset_gt (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_discOffset_gt` packaging the step-size
side condition as `1 ≤ d`.

Many later stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_discOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_discOffset_gt (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Inequality-direction variant of `erdos_discrepancy_exists_params_one_le_forall_exists_discOffset_gt`,
written as `discOffset f d m n > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_discOffset_gt' (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_discOffset_gt' (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Inequality-direction variant of `erdos_discrepancy_exists_params_forall_exists_discOffset_gt`,
written as `discOffset f d m n > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem erdos_discrepancy_exists_params_forall_exists_discOffset_gt' (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_forall_exists_discOffset_gt' (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the bundled offset nucleus `apSumOffset f d m n` takes arbitrarily large absolute values.

Normal form:
`∃ d m, d > 0 ∧ ∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  -- Prefer the Stage-3 existential packaging.
  simpa using
    (Tao2015.Stage3Output.exists_params_forall_exists_natAbs_apSumOffset_gt (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Paper-notation surface form of `erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt`.

Normal form:
`∃ d m, d > 0 ∧ ∀ B, ∃ n, |∑ i ∈ Icc (m+1) (m+n), f (i*d)| > B`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  rcases
      erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt (f := f) (hf := hf) with
    ⟨d, m, hd, h⟩
  refine ⟨d, m, hd, ?_⟩
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hIcc :
      Int.natAbs (apSumOffset f d m n) =
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) := by
    exact
      congrArg Int.natAbs (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n))
  simpa [hIcc] using hn

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt` packaging the
step-size side condition as `1 ≤ d`.

Many later analytic stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is a thin wrapper around the Stage-3 packaging.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_natAbs_apSumFrom_mul_gt` packaging the
step-size side condition as `1 ≤ d`.

Many later analytic stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (erdos_discrepancy_stage3Output (f := f) (hf := hf)))

/-- Paper-notation surface form of `erdos_discrepancy`, matching `∑_{i=1}^n f (i*d)`.

This is a thin wrapper around `erdos_discrepancy_apSum`, via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem erdos_discrepancy_sum_Icc (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

/-- Variant of `erdos_discrepancy_sum_Icc` writing the step-size side condition as `d ≥ 1`.

This is often the most readable surface form when `d : ℕ`.
-/
theorem erdos_discrepancy_sum_Icc_d_ge_one (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

end MoltResearch
