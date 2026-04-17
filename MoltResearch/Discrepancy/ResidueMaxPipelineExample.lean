import MoltResearch.Discrepancy

/-!
# Discrepancy: residue + max-level mini-pipeline (compile-only)

Checklist item: `Problems/erdos_discrepancy.md` (Track B)

This file is intentionally **compile-only**: it provides a tiny “paper-shaped” script that
exercises the max-level residue-class inequality in its packaged stable-surface form.

It must continue to compile under:

```lean
import MoltResearch.Discrepancy
```
-/

namespace MoltResearch

section
  open scoped BigOperators

  variable (f : ℕ → ℤ) (d m q N : ℕ)

  /-!
  ## Typical flow: block-length max → residue-term sum

  Start from the max discrepancy restricted to block lengths `q*(n+1)` (for `n ≤ N`), and apply the
  stable-surface residue-class bound expressed via the packaged `discOffsetUpTo_residueTerm`.
  -/
  example (hq : q > 0) :
      discOffsetUpTo_blockLen_mul_succ f d m q N ≤
        (Finset.range q).sum (fun r => discOffsetUpTo_residueTerm f d m q r N) := by
    simpa using
      (discOffsetUpTo_blockLen_mul_succ_le_sum_range_residueTerm
        (f := f) (d := d) (m := m) (q := q) (N := N) hq)

end

end MoltResearch
