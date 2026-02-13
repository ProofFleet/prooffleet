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
- Prefer `apSumOffset f d m n` for “tail starting after `m` steps of length `n`”.
  Rewrite between tails and differences using `apSumOffset_eq_sub` and
  `apSum_sub_apSum_eq_apSumOffset`. When you are already in the canonical `(m + n) - m` form,
  prefer `apSum_sub_eq_apSumOffset` (subtraction → tail) for rewriting.
  For “tail-of-tail” decompositions, rewrite differences of offset sums via
  `apSumOffset_sub_eq_apSumOffset_tail` (normal form) or `apSumOffset_sub_apSumOffset_eq_apSumOffset`
  (when a length inequality `n₁ ≤ n₂` is available).
  For paper notation, rewrite to an interval sum via `apSumOffset_eq_sum_Icc` (or directly via
  `apSum_sub_eq_sum_Icc` when starting from a difference, and `apSum_sub_apSum_eq_sum_Icc` when
  starting from `apSum … n - apSum … m` with `m ≤ n`).
- Prefer `apSumFrom f a d n` for affine AP sums `a + d, a + 2d, …, a + nd`.
  Split lengths via `apSumFrom_add_length`.
  For tails/differences, rewrite via `apSumFrom_tail_eq_sub` (tail → difference) or
  `apSumFrom_sub_eq_apSumFrom_tail` (difference → tail, in the canonical `(m + n) - m` form).
  Rewrite to an interval sum via `apSumFrom_eq_sum_Icc` when matching paper notation.

Discrepancy predicates / witnesses:
- Treat `HasDiscrepancyAtLeast` and `HasAffineDiscrepancyAtLeast` as normalization boundaries
  for existence statements; use the structured witness API in `Witness.lean` when convenient.
- When the sequence is reindexed, prefer the dedicated transforms (`…of_map_mul`, `…of_map_add`)
  instead of re-proving the bookkeeping from scratch.
- When scaling the sequence by a nonzero integer, prefer the dedicated scaling lemmas
  (`HasDiscrepancyAtLeast.mul_left_scale`, etc.) rather than unfolding definitions.
-/
