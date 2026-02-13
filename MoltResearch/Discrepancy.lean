import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Parity
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.AffineTail
import MoltResearch.Discrepancy.Const
import MoltResearch.Discrepancy.Scale
import MoltResearch.Discrepancy.Translate
import MoltResearch.Discrepancy.Reindex
import MoltResearch.Discrepancy.Bound
import MoltResearch.Discrepancy.Witness

/-!
# Discrepancy (module aggregator)

This file is the **stable import surface** for the discrepancy scaffold.

Rule of thumb:
- New reusable discrepancy artifacts should live in `MoltResearch/Discrepancy/*.lean`.
- Downstream work should prefer `import MoltResearch.Discrepancy` unless it needs a narrower import.
- Keep this aggregator small and boring: it is the API boundary.

## Normal forms (preferred rewrite targets)

The Track B lemma library is intended to be *directed*: we want a small set of
canonical shapes that downstream files can rewrite into and then work with.

Arithmetic progression sums:
- Prefer `apSum f d n` for homogeneous AP sums. Split lengths via `apSum_add_length`.
  If an `apSumOffset` appears with `m = 0`, rewrite it back to `apSum` via
  `apSumOffset_zero_m`.
- Prefer `apSumOffset f d m n` for “tail starting after `m` steps of length `n`”.
  Rewrite between tails and differences using `apSumOffset_eq_sub` and
  `apSum_sub_apSum_eq_apSumOffset`. When you are already in the canonical `(m + n) - m` form,
  prefer `apSum_sub_eq_apSumOffset` (subtraction → tail) for rewriting.
  For “tail-of-tail” decompositions, rewrite differences of offset sums via
  `apSumOffset_sub_eq_apSumOffset_tail` (normal form) or `apSumOffset_sub_apSumOffset_eq_apSumOffset`
  (when a length inequality `n₁ ≤ n₂` is available). To split an offset sum at an intermediate
  length, use `apSumOffset_eq_add_apSumOffset_tail`.
  For paper notation, rewrite to an interval sum via `apSumOffset_eq_sum_Icc`; for the normal-form
  difference of offset sums, use `apSumOffset_sub_eq_sum_Icc`. (Or rewrite directly via
  `apSum_sub_eq_sum_Icc` when starting from a difference, and `apSum_sub_apSum_eq_sum_Icc` when
  starting from `apSum … n - apSum … m` with `m ≤ n`).
- Prefer `apSumFrom f a d n` for affine AP sums `a + d, a + 2d, …, a + nd`.
  Split lengths via `apSumFrom_add_length`.
  For tails/differences, rewrite via `apSumFrom_tail_eq_sub` (tail → difference) or
  `apSumFrom_sub_eq_apSumFrom_tail` (difference → tail, in the canonical `(m + n) - m` form).
  For differences with an inequality `m ≤ n`, use `apSumFrom_sub_apSumFrom_eq_apSumFrom`.
  If you want the canonical offset-sum normal form on the shifted sequence `k ↦ f (a + k)`, use
  `apSumFrom_sub_eq_apSumOffset_shift` for the `(m + n) - m` normal form, and
  `apSumFrom_sub_apSumFrom_eq_apSumOffset_shift` for the general `m ≤ n` case.
  For paper notation, rewrite:
  - `apSumFrom f a d n` via `apSumFrom_eq_sum_Icc`,
  - tails `apSumFrom f (a + m*d) d n` via `apSumFrom_tail_eq_sum_Icc`,
  - and differences via `apSumFrom_sub_eq_sum_Icc` / `apSumFrom_sub_apSumFrom_eq_sum_Icc`.

Discrepancy predicates / witnesses:
- Treat `HasDiscrepancyAtLeast` and `HasAffineDiscrepancyAtLeast` as normalization boundaries
  for existence statements; use the structured witness API in `Witness.lean` when convenient.
- For surface statements, rewrite `∀ C, HasDiscrepancyAtLeast f C` to an explicit witness form
  `∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ …` via
  `forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos`.
  If you want paper notation, further rewrite to an explicit interval-sum witness form via
  `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`.
- For affine discrepancy, the analogous “paper notation” witness normal form is
  `forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`.
  If you want to eliminate affine sums entirely, you can also rewrite affine unbounded discrepancy to
  “some shift has large homogeneous discrepancy” via
  `forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift`.
- When the sequence is reindexed, prefer the dedicated transforms (`…of_map_mul`, `…of_map_add`)
  instead of re-proving the bookkeeping from scratch.
- When scaling the sequence by a nonzero integer, prefer the dedicated scaling lemmas
  (`HasDiscrepancyAtLeast.mul_left_scale`, etc.) rather than unfolding definitions.

## Worked rewrite recipe (quick mental model)

When you see a sum in “paper notation”, try to normalize it into the nucleus API first,
*then* apply bounds/triangle inequality, and only at the end rewrite back to `Icc` sums.

A typical rewrite pipeline:
1. Convert paper notation to nucleus notation:
   - `∑ i ∈ Icc 1 n, f (i*d)` ↔ `apSum f d n` via `apSum_eq_sum_Icc`.
   - `∑ i ∈ Icc (m+1) (m+n), f (i*d)` ↔ `apSumOffset f d m n` via `apSumOffset_eq_sum_Icc`.
2. Normalize differences of partial sums into tails:
   - `apSum f d (m+n) - apSum f d m` ↦ `apSumOffset f d m n` via `apSum_sub_eq_apSumOffset`.
   - `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁` ↦ `apSumOffset f d (m+n₁) n₂` via
     `apSumOffset_sub_eq_apSumOffset_tail`.
3. Split sums by length (canonical “one cut” normal form):
   - `apSum_add_length`, `apSumOffset_add_length`, `apSumFrom_add_length`.
4. Only when you want to match the literature, rewrite back to interval sums:
   - `apSumOffset_eq_sum_Icc`, `apSum_sub_eq_sum_Icc`, `apSumOffset_sub_eq_sum_Icc`, etc.

The small “example” blocks below are regression tests that these normal-form lemmas remain usable
from the stable surface import `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

section NormalFormExamples

variable (f : ℕ → ℤ) (a d m n : ℕ)

example : apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  simpa using apSum_eq_sum_Icc (f := f) (d := d) (n := n)

example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

end NormalFormExamples

end MoltResearch
