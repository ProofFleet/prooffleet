import Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output

/-!
# Erdős discrepancy: witness-form corollaries

This file collects the witness-form consequences of the Track-C Stage-3 pipeline.

We keep `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy` intentionally minimal so the
Track-C hard-gate build compiles quickly.
-/

namespace MoltResearch

/-- Paper-notation witness form for the concrete Stage-3 offset parameters.

Normal form:
`∀ B, ∃ n, Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d)) > B`,
where `d = Tao2015.stage3_d f hf` and `m = Tao2015.stage3_m f hf`.

This is a thin wrapper around `Tao2015.Stage3Output.forall_exists_natAbs_sum_Icc_offset_gt`.
-/
theorem erdos_discrepancy_sum_Icc_offset_stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs
          ((Finset.Icc ((Tao2015.stage3_m (f := f) (hf := hf)) + 1)
                ((Tao2015.stage3_m (f := f) (hf := hf)) + n)).sum
              (fun i => f (i * (Tao2015.stage3_d (f := f) (hf := hf))))) > B := by
  set out := Tao2015.stage3Out (f := f) (hf := hf) with hout
  simpa [Tao2015.stage3_m, Tao2015.stage3_d, hout.symm] using
    (Tao2015.Stage3Output.forall_exists_natAbs_sum_Icc_offset_gt (f := f) out)

/-- Positive-length witness form of `erdos_discrepancy_sum_Icc_offset_stage3`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem erdos_discrepancy_sum_Icc_offset_stage3_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      Int.natAbs
          ((Finset.Icc ((Tao2015.stage3_m (f := f) (hf := hf)) + 1)
                ((Tao2015.stage3_m (f := f) (hf := hf)) + n)).sum
              (fun i => f (i * (Tao2015.stage3_d (f := f) (hf := hf))))) > B := by
  set out := Tao2015.stage3Out (f := f) (hf := hf) with hout
  simpa [Tao2015.stage3_m, Tao2015.stage3_d, hout.symm] using
    (Tao2015.Stage3Output.forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f) out)

/-- Witness form of `erdos_discrepancy` directly in terms of the nucleus `apSum`.

This is the most pipeline-friendly surface statement:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ |apSum f d n| > C`.
-/
theorem erdos_discrepancy_apSum (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

/-- Variant of `erdos_discrepancy_apSum` writing the step-size side condition as `d > 0`.

Many later analytic stages prefer strict positivity for `Nat` step sizes.
-/
theorem erdos_discrepancy_apSum_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  simpa using
    (Tao2015.Stage3Output.forall_exists_d_pos_witness_pos (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_apSum` writing the step-size side condition as `d ≠ 0`.

This is sometimes the right normal form for downstream stages that treat `d` as a denominator (or
simply want to avoid rewriting strict inequalities).
-/
theorem erdos_discrepancy_apSum_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  simpa using
    (Tao2015.Stage3Output.forall_exists_d_ne_zero_witness_pos (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Witness form of `erdos_discrepancy` using the `discrepancy` wrapper.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.
-/
theorem erdos_discrepancy_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  simpa using
    (Tao2015.Stage3Output.forall_exists_discrepancy_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_discrepancy` writing the step-size side condition as `d ≥ 1`.

Many later analytic stages prefer `d ≥ 1` rather than `d > 0` when working with `Nat` step sizes.
-/
theorem erdos_discrepancy_discrepancy_d_ge_one (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ discrepancy f d n > C := by
  simpa using
    (Tao2015.Stage3Output.forall_exists_discrepancy_gt_d_ge_one (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Strengthened witness form of `erdos_discrepancy_discrepancy` with a positive-length witness.

This is sometimes convenient when downstream stages want to rule out the degenerate case `n = 0`.
-/
theorem erdos_discrepancy_discrepancy_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  simpa using
    (Tao2015.Stage3Output.forall_exists_discrepancy_gt_witness_pos (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a thin wrapper around the Stage-3 packaging.
-/
theorem erdos_discrepancy_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ Tao2015.UnboundedDiscOffset f d m := by
  simpa using
    (Tao2015.Stage3Output.exists_params_unboundedDiscOffset (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_exists_params_unboundedDiscOffset` packaging the step-size side
condition as `1 ≤ d`.

Many later stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ Tao2015.UnboundedDiscOffset f d m := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_unboundedDiscOffset (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the bundled offset discrepancy family `discOffset f d m` takes arbitrarily large values.

This is the explicit witness-family form of `erdos_discrepancy_exists_params_unboundedDiscOffset`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_discOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_discOffset_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Positive-length witness form of `erdos_discrepancy_exists_params_forall_exists_discOffset_gt`.

The witness length `n` cannot be `0`, since `discOffset f d m 0 = 0`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_discOffset_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ B < discOffset f d m n) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_discOffset_gt_witness_pos (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_discOffset_gt` packaging the step-size
side condition as `1 ≤ d`.

Many later stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_discOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_one_le_forall_exists_discOffset_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Inequality-direction variant of `erdos_discrepancy_exists_params_one_le_forall_exists_discOffset_gt`,
written as `discOffset f d m n > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_discOffset_gt' (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_one_le_forall_exists_discOffset_gt' (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Inequality-direction variant of `erdos_discrepancy_exists_params_forall_exists_discOffset_gt`,
written as `discOffset f d m n > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem erdos_discrepancy_exists_params_forall_exists_discOffset_gt' (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_discOffset_gt' (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the bundled offset nucleus `apSumOffset f d m n` takes arbitrarily large absolute values.

Normal form:
`∃ d m, d > 0 ∧ ∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  -- Prefer the Stage-2 existential packaging (Stage 3 bundles a Stage-2 output).
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_natAbs_apSumOffset_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Paper-notation surface form of `erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt`.

Normal form:
`∃ d m, d > 0 ∧ ∀ B, ∃ n, |∑ i ∈ Icc (m+1) (m+n), f (i*d)| > B`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  -- Prefer the Stage-2 packaging lemma rather than re-proving the `apSumOffset`→`sum_Icc` rewrite.
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_natAbs_sum_Icc_offset_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Positive-length witness form of `erdos_discrepancy_exists_params_forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_natAbs_sum_Icc_offset_gt` packaging the
step-size side condition as `1 ≤ d`.

Many later analytic stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Positive-length witness form of `erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos
      (f := f) (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_natAbs_apSumOffset_gt` packaging the
step-size side condition as `1 ≤ d`.

Many later analytic stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Variant of `erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt`
with a positive-length witness `n > 0`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f d m n) > B) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos
      (f := f) (Tao2015.stage3Out (f := f) (hf := hf)))

/-- Track-C pipeline witness form (Tao 2015 plane): there exist concrete parameters `d, m` such that
  the affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is a thin wrapper around the Stage-3 packaging.
-/
theorem erdos_discrepancy_exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Variant of `erdos_discrepancy_exists_params_forall_exists_natAbs_apSumFrom_mul_gt` packaging the
step-size side condition as `1 ≤ d`.

Many later analytic stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa using
    (Tao2015.Stage2Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (Tao2015.stage3Out (f := f) (hf := hf)).out2)

/-- Variant of `erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt`
with a positive-length witness `n > 0`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.
-/
theorem erdos_discrepancy_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa using
    (Tao2015.Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
      (f := f) (Tao2015.stage3Out (f := f) (hf := hf)))

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
