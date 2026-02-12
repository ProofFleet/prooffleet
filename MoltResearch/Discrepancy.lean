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
  `apSum_sub_apSum_eq_apSumOffset`.
- Prefer `apSumFrom f a d n` for affine AP sums `a + d, a + 2d, …, a + nd`.
  Split lengths via `apSumFrom_add_length`, and rewrite tails via `apSumFrom_tail_eq_sub`.

Discrepancy predicates / witnesses:
- Treat `HasDiscrepancyAtLeast` and `HasAffineDiscrepancyAtLeast` as normalization boundaries
  for existence statements; use the structured witness API in `Witness.lean` when convenient.
- When the sequence is reindexed, prefer the dedicated transforms (`…of_map_mul`, `…of_map_add`)
  instead of re-proving the bookkeeping from scratch.
-/
