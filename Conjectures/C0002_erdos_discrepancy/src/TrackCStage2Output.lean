import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core
import Conjectures.C0002_erdos_discrepancy.src.Tao2015Extras

/-!
# Track C: Stage 2 output lemmas

This file contains the proved convenience lemmas about `Tao2015.Stage2Output`.

The boundary record itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary`, which we keep intentionally thin.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage2Output

variable {f : ℕ → ℤ}

/-- Build a Stage-2 output from a Stage-1 reduction output plus unboundedness of the bundled
offset discrepancy family.

This is a small convenience constructor: many future Stage-2 proofs will naturally establish
unboundedness in the `discOffset` normal form, and then transport it to fixed-step unboundedness
via the Stage-1 contract.
-/
def ofReductionOutput_unboundedDiscOffset (out1 : Tao2015.ReductionOutput f)
    (hunb : Tao2015.UnboundedDiscOffset f out1.d out1.m) : Stage2Output f := by
  refine ⟨out1, ?_⟩
  exact (out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).2 hunb

/-!
Basic projections (`d`, `g`, `m`, `hg`, `g_eq`, `hd`, `d_ne_zero`, `one_le_d`) live in
`TrackCStage2Core.lean` so downstream stages can access them without importing this larger file.
-/

/-- Stage-2 unboundedness re-expressed as arbitrarily large affine-tail nucleus values
`apSumFrom f (m*d) d n`.

This is a wrapper around the Stage-1 boundary lemma
`ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem unbounded_iff_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage2Output f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      ∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  simpa [Stage2Output.g, Stage2Output.d, Stage2Output.m] using
    (out.out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f))

/-- (Deprecated) Unboundedness of the reduced sequence in explicit witness form (`B < discrepancy ...`).

Prefer using the field `out.unbounded` (or the more structured
`forall_hasDiscrepancyAtLeastAlong`) to keep the Stage-2 API surface small.
-/
@[deprecated "Use `out.unbounded` (or `forall_hasDiscrepancyAtLeastAlong`)." (since := "2026-03-24")]
theorem forall_exists_discrepancy_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  -- This is just the definitional witness form for `UnboundedDiscrepancyAlong`.
  simpa [Tao2015.UnboundedDiscrepancyAlong] using out.unbounded

/-- Unboundedness of the reduced sequence in explicit witness form (`discrepancy ... > B`).

This is the inequality-direction normal form of the unboundedness field `out.unbounded`.
-/
theorem forall_exists_discrepancy_gt' (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, discrepancy out.g out.d n > B := by
  simpa using
    (Tao2015.unboundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt' (g := out.g) (d := out.d)).1
      out.unbounded

/-- Equivalent packaging: arbitrarily large discrepancy witnesses along `out.d`. -/
theorem forall_hasDiscrepancyAtLeastAlong (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- `UnboundedDiscrepancyAlong` is definitionally `∀ C, HasDiscrepancyAtLeastAlong ... C`.
  simpa [Tao2015.UnboundedDiscrepancyAlong, HasDiscrepancyAtLeastAlong] using out.unbounded

/-- Stage-2 unboundedness, re-expressed using the verified core predicate.

This is a small convenience lemma: many consumers outside the `Tao2015` namespace use the core
predicate `MoltResearch.UnboundedDiscrepancyAlong` rather than the Track-C-local definition.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage2Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.unboundedDiscrepancyAlong_iff_core (g := out.g) (d := out.d)).1 out.unbounded

/-- Tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail sums
`apSumFrom f (m*d) d n`.

We phrase this in the tail-nucleus normal form because it is the most common analytic entry point
into the Tao 2015 pipeline.

Implementation note: this is just `out.unbounded` rewritten using
`unbounded_iff_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt (out : Stage2Output f) :
    ∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  simpa using
    (out.unbounded_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f)).1 out.unbounded

/-- Positive-length witness form of `forall_exists_natAbs_apSumFrom_mul_gt`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (out : Stage2Output f) :
    ∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  have hunb : UnboundedDiscOffset f out.d out.m :=
    (out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1 out.unbounded
  simpa using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) (d := out.d)
      (m := out.m) hunb)

/-- Negation-normal form of `forall_exists_natAbs_apSumFrom_mul_gt`: there is no uniform bound on
the affine-tail nuclei at the concrete Stage-1 parameters produced by Stage 2. -/
theorem not_exists_forall_natAbs_apSumFrom_mul_le (out : Stage2Output f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  have hunb : UnboundedDiscOffset f out.d out.m :=
    (out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1 out.unbounded
  -- Use the Conjectures-only normal form lemma from `Tao2015Extras`.
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_natAbs_apSumFrom_mul_le
        (f := f) (d := out.d) (m := out.m)).1
      hunb

/-- Stage 2 implies the reduced sequence is not bounded along its fixed step size. -/
theorem notBoundedReducedAlong (out : Stage2Output f) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.UnboundedDiscrepancyAlong.iff_not_boundedDiscrepancyAlong
    (g := out.g) (d := out.d)).1 out.unbounded

/-- Consumer-facing form: Stage 2 unboundedness transferred back to the original sequence as an
unbounded **offset discrepancy** witness.

This is just a wrapper around
`Tao2015.ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`.

Note the inequality direction: this produces witnesses of the form `B < discOffset ...`.
-/
theorem forall_exists_discOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  -- Unfold the Stage-2 witness form and transport it through the Stage-1 contract.
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f)).1 out.unbounded)

/-- Positive-length witness form of `forall_exists_discOffset_gt`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem forall_exists_discOffset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ B < discOffset f out.d out.m n := by
  have hunb : UnboundedDiscOffset f out.d out.m :=
    (out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1 out.unbounded
  exact UnboundedDiscOffset.forall_exists_discOffset_gt_witness_pos (hunb := hunb)

/-- Inequality-direction variant of `forall_exists_discOffset_gt`, written as `discOffset ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_discOffset_gt' (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B := by
  -- Delegate to the Stage-1 transport lemma (inequality-direction normal form).
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt' (f := f)).1 out.unbounded)

/-!
The lemma

  Stage2Output.unboundedDiscOffset (out : Stage2Output f) : UnboundedDiscOffset f out.d out.m

is proved in `TrackCStage2Core.lean` so downstream stages can use it without importing this larger
convenience-lemma file.
-/

/-- Stage 2 implies there is no uniform bound on the bundled offset discrepancy family
`discOffset f out.d out.m`.

This is the negation-normal-form version of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage2Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.d out.m B := by
  have hunb : UnboundedDiscOffset f out.d out.m :=
    out.unboundedDiscOffset (f := f)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f)
        (d := out.d) (m := out.m)).1
      hunb

/-- Negation-normal-form unboundedness statement for the bundled offset nuclei
`Int.natAbs (apSumOffset f out.d out.m n)`.

This is `not_exists_boundedDiscOffset` rewritten by unfolding `discOffset`.
-/
theorem not_exists_forall_natAbs_apSumOffset_le (out : Stage2Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  -- Use the Conjectures-only normal form lemma from `Tao2015Extras`.
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_natAbs_apSumOffset_le (f := f)
        (d := out.d) (m := out.m)).1
      hunb

/-- Negation-normal-form unboundedness statement for the paper-notation shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` at the concrete Stage-2 parameters `(out.d, out.m)`.

This is `not_exists_forall_natAbs_apSumOffset_le` rewritten using
`Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem not_exists_forall_natAbs_sum_Icc_offset_le (out : Stage2Output f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) ≤ B := by
  intro h
  have hOffset :
      ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
    rcases h with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    have hIcc :
        Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) ≤ B :=
      hB n
    simpa [Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := out.d) (m := out.m) (n := n)] using
      hIcc
  exact (out.not_exists_forall_natAbs_apSumOffset_le (f := f)) hOffset

/-- Existential packaging: Stage 2 already yields concrete parameters `d, m` such that the bundled
offset discrepancy family `discOffset f d m` is unbounded.

This is occasionally a convenient normal form for later stages that prefer not to depend on the
record fields of `Stage2Output`.
-/
theorem exists_params_unboundedDiscOffset (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  exact out.unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a small convenience variant of `exists_params_unboundedDiscOffset`: many downstream stages
use the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem exists_params_one_le_unboundedDiscOffset (out : Stage2Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  exact out.unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` such that `discOffset f d m`
has arbitrarily large values.

This is the explicit witness-family form of `exists_params_unboundedDiscOffset`.
-/
theorem exists_params_forall_exists_discOffset_gt (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  intro B
  simpa using out.forall_exists_discOffset_gt (f := f) B

/-- Inequality-direction variant of `exists_params_forall_exists_discOffset_gt`, written as
`discOffset f d m n > B`.

This is often a more convenient normal form for consumers that want to `simp [gt_iff_lt]`.
-/
theorem exists_params_forall_exists_discOffset_gt' (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  rcases out.exists_params_forall_exists_discOffset_gt (f := f) with ⟨d, m, hd, h⟩
  refine ⟨d, m, hd, ?_⟩
  intro B
  rcases h B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that
`discOffset f d m` has arbitrarily large values.

This is a small convenience variant of `exists_params_forall_exists_discOffset_gt`: many downstream
stages use the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem exists_params_one_le_forall_exists_discOffset_gt (out : Stage2Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_discOffset_gt (f := f) B

/-- Inequality-direction variant of `exists_params_one_le_forall_exists_discOffset_gt`, written as
`discOffset f d m n > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem exists_params_one_le_forall_exists_discOffset_gt' (out : Stage2Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  rcases out.exists_params_one_le_forall_exists_discOffset_gt (f := f) with ⟨d, m, hd, h⟩
  refine ⟨d, m, hd, ?_⟩
  intro B
  rcases h B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` such that the affine-tail nucleus
`apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is the explicit witness-family form often consumed by later analytic stages.
-/
theorem exists_params_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  intro C
  rcases out.forall_exists_natAbs_apSumFrom_mul_gt (f := f) C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Existential packaging variant of `exists_params_forall_exists_natAbs_apSumFrom_mul_gt` using
the side condition `1 ≤ d`.

Many downstream consumers prefer `1 ≤ d` to avoid repeatedly rewriting `d > 0`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage2Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro C
  rcases out.forall_exists_natAbs_apSumFrom_mul_gt (f := f) C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Backwards-compatible alias for `forall_exists_discOffset_gt`.

Deprecated because the suffix `_lt` was misleading: the statement is `B < ...` (i.e. “greater than B”).
-/
@[deprecated "Use `forall_exists_discOffset_gt` (the statement is `B < discOffset ...`)." (since := "2026-03-08")]
theorem forall_exists_discOffset_lt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  simpa using out.forall_exists_discOffset_gt (f := f)

/-- Sum-level variant of `forall_exists_discOffset_gt`.

This is occasionally the right normal form for later analytic stages: it exposes the raw nucleus
`apSumOffset` rather than the wrapper `discOffset`.

Implementation note: we obtain this from the packaged offset-unboundedness statement
`out.unboundedDiscOffset` using the generic normal-form lemma
`Tao2015.UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt`.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa [Stage2Output.d, Stage2Output.m] using
    (Tao2015.UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt (f := f)
      (d := out.d) (m := out.m)).1 hunb

/-- Inequality-direction variant of `forall_exists_natAbs_apSumOffset_gt`, written as
`Int.natAbs ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_natAbs_apSumOffset_gt' (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa [Stage2Output.d, Stage2Output.m] using
    (Tao2015.UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt' (f := f)
      (d := out.d) (m := out.m)).1 hunb

/-- Paper-notation normal form of `forall_exists_natAbs_apSumOffset_gt'`.

This rewrites the offset nuclei `apSumOffset f out.d out.m n` as the shifted progression sums
`∑ i ∈ Icc (out.m+1) (out.m+n), f (i*out.d)`.
-/
theorem forall_exists_natAbs_sum_Icc_offset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa using
    (Tao2015.unboundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt' (f := f)
          (d := out.d) (m := out.m)).1
      hunb

/-- Positive-length witness form of `forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) > B := by
  intro B
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  rcases
      Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt_witness_pos
        (f := f) (d := out.d) (m := out.m) hunb B with
    ⟨n, hnpos, hn⟩
  refine ⟨n, hnpos, ?_⟩
  have hn' : B <
      Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) := by
    -- Avoid a `simp` recursion-depth blowup: rewrite the `discOffset` witness directly.
    have hn' := hn
    rw [discOffset_eq_natAbs_sum_Icc (f := f) (d := out.d) (m := out.m) (n := n)] at hn'
    exact hn'
  exact (gt_iff_lt).2 hn'

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` such that the offset nucleus
`apSumOffset f d m n` takes arbitrarily large absolute values.

This is the raw-nucleus form of `exists_params_forall_exists_discOffset_gt`.
-/
theorem exists_params_forall_exists_natAbs_apSumOffset_gt (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_apSumOffset_gt' (f := f) B

/-- Paper-notation packaging: Stage 2 yields concrete parameters `d, m` such that the shifted
homogeneous progression sums

`∑ i ∈ Icc (m+1) (m+n), f (i*d)`

take arbitrarily large absolute values.

This is just `forall_exists_natAbs_sum_Icc_offset_gt` packaged existentially.
-/
theorem exists_params_forall_exists_natAbs_sum_Icc_offset_gt (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  refine ⟨out.d, out.m, out.hd, ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_sum_Icc_offset_gt (f := f) B

/-- Paper-notation packaging variant of `exists_params_forall_exists_natAbs_sum_Icc_offset_gt` using
the side condition `1 ≤ d`.

Many downstream consumers prefer `1 ≤ d` to avoid repeatedly rewriting `d > 0`.
-/
theorem exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt (out : Stage2Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_sum_Icc_offset_gt (f := f) B

/-- Existential packaging variant of `exists_params_forall_exists_natAbs_apSumOffset_gt` using
the side condition `1 ≤ d`.

Many downstream consumers prefer `1 ≤ d` to avoid repeatedly rewriting `d > 0`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (out : Stage2Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_apSumOffset_gt' (f := f) B

/-- Backwards-compatible alias for `forall_exists_natAbs_apSumOffset_gt`.

Deprecated because the suffix `_lt` was misleading: the statement is `B < ...`.
-/
@[deprecated "Use `forall_exists_natAbs_apSumOffset_gt` (the statement is `B < Int.natAbs ...`)." (since := "2026-03-08")]
theorem forall_exists_natAbs_apSumOffset_lt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  simpa using out.forall_exists_natAbs_apSumOffset_gt (f := f)

-- Core global-goal bridge lemmas live in `TrackCStage2Core.lean`.

end Stage2Output

end Tao2015

end MoltResearch

