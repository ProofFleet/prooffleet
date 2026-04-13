import MoltResearch.Discrepancy

/-!
# Discrepancy: stable-surface mini-pipeline (max-level) regression examples

Checklist item: `Problems/erdos_discrepancy.md` (Track B)

These are intentionally **compile-only** examples that exercise a typical flow under the *stable*
import surface:

```lean
import MoltResearch.Discrepancy
```

Goal: keep a couple of high-leverage “pipeline steps” from regressing without importing any opt-in
simp bundles.
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (d m q N C : ℕ)

  /-!
  ## Paper endpoints → nucleus `discOffsetUpTo` (endpoint-style rewrite)

  This is the “paper form” (finite `sup` over `t ≤ N`) in the endpoint conventions used downstream.
  -/
  example :
      discOffsetUpTo f d m N =
        (Finset.Icc 0 N).sup
          (fun t =>
            Int.natAbs ((Finset.Icc (m + 1) (m + t)).sum (fun i => f (i * d)))) := by
    simpa using (discOffsetUpTo_eq_sup_Icc_lengths (f := f) (d := d) (m := m) (N := N))

  /-!
  ## Residue split / cut (max-level) → clean inequality

  This packages the residue-class split bound for block lengths `q*(n+1)`.
  -/
  example (hq : q > 0) :
      discOffsetUpTo_blockLen_mul_succ f d m q N ≤
        (Finset.range q).sum (fun r =>
          (Finset.range (N + 1)).sup (fun n =>
            Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n))) := by
    simpa using
      (discOffsetUpTo_blockLen_mul_succ_le_sum_range_sup_natAbs (f := f) (d := d) (m := m)
        (q := q) (N := N) hq)

end

end MoltResearch
