import MoltResearch.Discrepancy.Residue

/-!
# Discrepancy: residue-class splitting (deprecated nested-sum normal forms)

This file contains deprecated “nested sum” wrappers for residue-class splitting.

They are intentionally **not** part of the stable surface:

```lean
import MoltResearch.Discrepancy
```

If you need these legacy normal forms, import:

```lean
import MoltResearch.Discrepancy.Deprecated
```
-/

namespace MoltResearch

/-!
## Nested-sum residue-class splitting (reindexing normal form)

These are lightweight wrappers around the general reindexing lemma
`sum_range_mul_reindex_mod_div`, specialized to the `apSum` nucleus.

They are deprecated in favor of the head+tail / affine-tail residue split normal forms:
- `apSum_mul_len_succ_eq_sum_range`
- `apSum_mul_len_succ_eq_sum_range_mul_left`

Checklist item: Problems/erdos_discrepancy.md (Track B) — “API surface coherence” pass for residue splitting.
-/

/-- Deprecated: residue-class split for `apSum` as a **nested sum** over residues `r < q` and quotients `k < n+1`.

Prefer `apSum_mul_len_succ_eq_sum_range`.
-/
@[deprecated "Use `apSum_mul_len_succ_eq_sum_range` (head+tail normal form)." (since := "2026-04-05")]
lemma apSum_mul_len_succ_eq_sum_range_sum_range (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        (Finset.range (n + 1)).sum (fun k => f ((q * k + (r + 1)) * d))) := by
  classical
  -- Apply the generic range reindexing lemma to the summand function `i ↦ f ((i+1)*d)`.
  simpa [apSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (sum_range_mul_reindex_mod_div (q := q) (n := n + 1) (hq := hq)
      (f := fun i => f ((i + 1) * d)))

/-- Deprecated `d*i` multiplication-order variant of `apSum_mul_len_succ_eq_sum_range_sum_range`.

Prefer `apSum_mul_len_succ_eq_sum_range_mul_left`.
-/
@[deprecated "Use `apSum_mul_len_succ_eq_sum_range_mul_left` (head+tail normal form)." (since := "2026-04-05")]
lemma apSum_mul_len_succ_eq_sum_range_sum_range_mul_left (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        (Finset.range (n + 1)).sum (fun k => f (d * (q * k + (r + 1))))) := by
  -- Just commute multiplication in the summand of the previous lemma.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSum_mul_len_succ_eq_sum_range_sum_range (f := f) (d := d) (q := q) (n := n) hq)

end MoltResearch
