import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Core
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output

/-!
# Track C: Stage 3 output lemmas (Tao 2015 plane)

This file contains the proved convenience lemmas about `Tao2015.Stage3Output`.

We keep `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3` intentionally small so the Track-C
hard-gate build for `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy` compiles quickly.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage3Output

variable {f : ℕ → ℤ}

/-!
Basic projections (`notBoundedOriginal`, `d`, `g`, `m`, `hg`, `g_eq`, `hd`, `d_ne_zero`,
`one_le_d`, `unboundedReducedAlong`, `forall_hasDiscrepancyAtLeastAlong`,
`unboundedDiscrepancyAlong_core`) live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Core`.
-/

/-- Stage 3 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 3.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) out.out2

/-- Variant of `forall_exists_d_ge_one_witness_pos` with the step-size side condition written as
`d > 0`.

Many consumers prefer the strict-positivity normal form when working with `Nat` step sizes.
-/
theorem forall_exists_d_pos_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact Stage2Output.forall_exists_d_pos_witness_pos (f := f) out.out2

/-- Variant of `forall_exists_d_pos_witness_pos` with the step-size side condition written as
`d ≠ 0`.

This is sometimes the right normal form for downstream stages that treat `d` as a denominator (or
simply want to avoid rewriting strict inequalities).
-/
theorem forall_exists_d_ne_zero_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact Stage2Output.forall_exists_d_ne_zero_witness_pos (f := f) out.out2

/-- Stage 3 output implies the discrepancy-witness normal form

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem forall_exists_discrepancy_gt (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      ((out.forall_hasDiscrepancyAtLeast (f := f)) C)

/-- Variant of `forall_exists_discrepancy_gt` writing the step-size side condition as `d ≥ 1`.

Many consumers prefer `d ≥ 1` rather than `d > 0` when working with `Nat` step sizes.
-/
theorem forall_exists_discrepancy_gt_d_ge_one (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ discrepancy f d n > C := by
  intro C
  rcases out.forall_exists_discrepancy_gt (f := f) C with ⟨d, n, hd, hdisc⟩
  refine ⟨d, n, ?_, hdisc⟩
  exact Nat.succ_le_iff.2 hd

/-- Strengthened witness form of `forall_exists_discrepancy_gt` with a positive-length witness.

This is sometimes convenient when downstream stages want to rule out the degenerate case `n = 0`.
-/
theorem forall_exists_discrepancy_gt_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases out.forall_exists_d_pos_witness_pos (f := f) C with ⟨d, n, hd, hn, h⟩
  refine ⟨d, n, hd, hn, ?_⟩
  simpa using h

/-- Stage 3 output implies the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem forall_exists_sum_Icc_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

/-- Variant of `forall_exists_sum_Icc_witness_pos` writing the step-size side condition as `d ≥ 1`.

This is often the most readable surface form when `d : ℕ`.
-/
theorem forall_exists_sum_Icc_d_ge_one_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

-- (moved to `TrackCStage3Core.lean`)

/-- Witness-family form: Stage 3 yields arbitrarily large values of the bundled offset discrepancy
family `discOffset f out.d out.m`.

Normal form: `∀ B, ∃ n, B < discOffset f out.d out.m n`.
-/
theorem forall_exists_discOffset_gt (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_discOffset_gt (f := f) out.out2)

/-- Inequality-direction variant of `forall_exists_discOffset_gt`, written as
`discOffset f out.d out.m n > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_discOffset_gt' (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_discOffset_gt' (f := f) out.out2)

/-- Positive-length witness form of `forall_exists_discOffset_gt`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem forall_exists_discOffset_gt_witness_pos (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ B < discOffset f out.d out.m n := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_discOffset_gt_witness_pos (f := f) out.out2)

/-- Positive-length witness form of `forall_exists_discOffset_gt'`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem forall_exists_discOffset_gt'_witness_pos (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ discOffset f out.d out.m n > B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_discOffset_gt'_witness_pos (f := f) out.out2)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `d > 0` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a convenience wrapper around `Stage3Output.unboundedDiscOffset`.
-/
theorem exists_params_unboundedDiscOffset (out : Stage3Output f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  simpa [Stage3Output.d, Stage3Output.m] using out.unboundedDiscOffset (f := f)

/-- Existential packaging variant of `exists_params_unboundedDiscOffset` using the side condition
`1 ≤ d`.

Many downstream consumers prefer `1 ≤ d` to avoid repeatedly rewriting `d > 0`.
-/
theorem exists_params_one_le_unboundedDiscOffset (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  simpa [Stage3Output.d, Stage3Output.m] using out.unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that there is
no bundled offset-discrepancy bound at those parameters.

Normal form: `∃ d m, 1 ≤ d ∧ ¬ ∃ B, BoundedDiscOffset f d m B`.

This is just `Stage3Output.not_exists_boundedDiscOffset` packaged under an existential quantifier.
-/
theorem exists_params_one_le_not_exists_boundedDiscOffset (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  simpa [Stage3Output.d, Stage3Output.m] using out.not_exists_boundedDiscOffset (f := f)

-- Note: `Stage3Output.not_exists_boundedDiscOffset` is defined in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3`.

/-- Negation-normal-form unboundedness statement for the bundled offset nuclei
`Int.natAbs (apSumOffset f out.d out.m n)`.

This is a thin wrapper around `Stage2Output.not_exists_forall_natAbs_apSumOffset_le`.
-/
theorem not_exists_forall_natAbs_apSumOffset_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.not_exists_forall_natAbs_apSumOffset_le (f := f) out.out2)

/-- Nucleus witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is `unboundedDiscOffset` rewritten so consumers can work directly with
`Int.natAbs (apSumOffset f d m n)` without unfolding `discOffset`.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt (f := f) out.out2)

/-- Inequality-direction variant of `forall_exists_natAbs_apSumOffset_gt`, written as
`Int.natAbs ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_natAbs_apSumOffset_gt' (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt' (f := f) out.out2)

/-- Positive-length witness form of `forall_exists_natAbs_apSumOffset_gt'`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem forall_exists_natAbs_apSumOffset_gt_witness_pos (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f out.d out.m n) > B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f) out.out2)

/-- Paper-notation witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is `forall_exists_natAbs_apSumOffset_gt'` rewritten using
`Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem forall_exists_natAbs_sum_Icc_offset_gt (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) > B := by
  -- Stage 3 bundles a Stage-2 output, so route through the already-proved Stage-2 paper-notation
  -- lemma rather than depending on optional Tao2015Extras normal forms.
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_sum_Icc_offset_gt (f := f) out.out2)

/-- Positive-length witness form of `forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) > B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f) out.out2)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` such that the paper-notation
shifted progression sums `∑ i ∈ Icc (m+1) (m+n), f (i*d)` take arbitrarily large absolute values.

This is a small wrapper around `forall_exists_natAbs_sum_Icc_offset_gt`.
-/
theorem exists_params_forall_exists_natAbs_sum_Icc_offset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  intro B
  exact out.forall_exists_natAbs_sum_Icc_offset_gt (f := f) B

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
paper-notation offset sum witness `∑ i ∈ Icc (m+1) (m+n), f (i*d)` takes arbitrarily large absolute
values.

This is a small wrapper around `forall_exists_natAbs_sum_Icc_offset_gt`.
-/
theorem exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  exact out.forall_exists_natAbs_sum_Icc_offset_gt (f := f) B

/-- Existential packaging variant of `exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt`
with a positive-length witness `n > 0`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f) B

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
offset nucleus `apSumOffset f d m n` takes arbitrarily large absolute values.

This is a small wrapper around `forall_exists_natAbs_apSumOffset_gt'`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_apSumOffset_gt' (f := f) B

/-- Existential packaging variant of `exists_params_one_le_forall_exists_natAbs_apSumOffset_gt`
with a positive-length witness `n > 0`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f d m n) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f) B

/-- Tail-nucleus witness form equivalence for the concrete Stage-1 parameters bundled in Stage 3.

This is `Stage2Output.unbounded_iff_forall_exists_natAbs_apSumFrom_mul_gt`, re-expressed at the
Stage-3 boundary.
-/
theorem unboundedReducedAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      ∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  simpa [Stage3Output.g, Stage3Output.d, Stage3Output.m] using
    (Stage2Output.unbounded_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f) out.out2)

/-- Tail-nucleus witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is the Stage-2 witness `Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt`, re-expressed
at the Stage-3 boundary.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  exact (unboundedReducedAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f) out).1
    out.unboundedReducedAlong

/-- Positive-length witness form of `forall_exists_natAbs_apSumFrom_mul_gt`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ,
      ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) out.out2)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is a thin wrapper around `forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro C
  simpa [Stage3Output.d, Stage3Output.m] using out.forall_exists_natAbs_apSumFrom_mul_gt (f := f) C

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values, with a
positive-length witness `n > 0`.

This is a thin wrapper around `forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro C
  simpa [Stage3Output.d, Stage3Output.m] using
    out.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) C

/-- Negation-normal form of `forall_exists_natAbs_apSumFrom_mul_gt`: there is no uniform bound on
the affine-tail nuclei at the concrete Stage-1 parameters bundled in Stage 3.

This is a thin wrapper around `Stage2Output.not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem not_exists_forall_natAbs_apSumFrom_mul_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.not_exists_forall_natAbs_apSumFrom_mul_le (f := f) out.out2)

end Stage3Output

end Tao2015

end MoltResearch
