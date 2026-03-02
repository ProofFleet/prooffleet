import MoltResearch.Discrepancy

/-!
# Discrepancy: stable surface audit (compile-time regression tests)

This file is a tiny, explicit **API surface checklist** for the stable import surface

```lean
import MoltResearch.Discrepancy
```

It aims to enforce two things:

1. **Presence:** the normal-form “nucleus” lemmas we want downstream proofs to use remain exported.
2. **Absence:** deprecated legacy wrappers (e.g. older `*_map_add` names) are **not** exported by
   default; they live behind an explicit opt-in import.

Guiding principle: prefer a few high-leverage checks over a huge brittle list.

If you need backwards-compatible / deprecated aliases, import:

```lean
import MoltResearch.Discrepancy.Deprecated
```
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (a d m n : ℕ)

  /-!
  ## Presence checks (stable surface)

  These are the objects/lemmas we consider part of the “stable normal-form toolkit”.
  -/

  -- Nucleus objects should be present.
  #check apSum
  #check apSumOffset
  #check apSumFrom

  -- Canonical translation-friendly normal forms should be present.
  #check apSumFrom_eq_apSum_shift_add
  #check apSumFrom_eq_apSum_shift_add_left

  #check apSumOffset_eq_apSum_shift_add
  #check apSumOffset_eq_apSumOffset_shift_add

  -- Affine-tail ↔ shifted-sequence normal forms should be present.
  #check apSumFrom_tail_eq_apSumOffset_shift_add
  #check apSumOffset_shift_add_eq_apSumFrom_tail
  #check apSumOffset_shift_add_eq_apSumFrom_tail_firstTerm

  -- Differences → tails normal forms should be present.
  #check apSum_sub_eq_apSumOffset
  #check apSumFrom_sub_eq_apSumFrom_tail
  #check apSumFrom_sub_eq_apSumOffset_shift_add

  -- Additional bridge lemmas (high-leverage normal-form glue).
  #check apSumOffset_eq_sub
  #check apSumOffset_eq_apSumFrom

  -- Paper ↔ nucleus rewrite entrypoints should be present.
  #check sum_Icc_eq_apSum
  #check apSum_eq_sum_Icc

  -- Bridge lemmas for splitting paper interval sums should be present.
  #check sum_Icc_eq_apSumOffset_add_length
  #check sum_Icc_add_length

  -- Step-factorization (compare different steps) normal form should be present.
  #check apSum_mul_eq_apSum_map_mul

  /-!
  ## Absence checks (deprecated names must NOT be in the stable surface)

  We deliberately assert these names are *not* available under `import MoltResearch.Discrepancy`.
  If any of these starts typechecking here, the stable surface has regressed.
  -/

  /-- error: Unknown constant `MoltResearch.IsSignSequence.map_add` -/
  #guard_msgs in
  #check IsSignSequence.map_add

  /-- error: Unknown identifier `apSumFrom_eq_apSum_map_add` -/
  #guard_msgs in
  #check apSumFrom_eq_apSum_map_add

  /-- error: Unknown identifier `apSumFrom_map_add` -/
  #guard_msgs in
  #check apSumFrom_map_add

  /-- error: Unknown identifier `apSum_map_add` -/
  #guard_msgs in
  #check apSum_map_add
end

/-!
## Example usage (ensures the pipeline works end-to-end)

A tiny example rewriting a paper-notation interval sum into two consecutive `apSumOffset` blocks,
then expanding those blocks back into paper notation. This is a regression test that the
one-cut paper→nucleus bridge lemma is available in the stable surface.
-/
section
  variable (f : ℕ → ℤ) (d m n₁ n₂ : ℕ)

  example :
      (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
    classical
    -- Rewrite the LHS to `apSumOffset` blocks, then expand back to `Finset.Icc` sums.
    simpa [apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (sum_Icc_eq_apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
end

end MoltResearch
