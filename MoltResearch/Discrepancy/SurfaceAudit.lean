import MoltResearch.Discrepancy

/-!
# Discrepancy: stable surface audit (compile-time regression tests)

This file is intended to be a tiny, explicit checklist that the **stable import surface**

```lean
import MoltResearch.Discrepancy
```

still exposes the core normal-form rewrite pipeline we expect downstream proofs to use.

Guiding principle: prefer a few high-leverage checks over a huge brittle list.

If you need backwards-compatible / deprecated aliases (e.g. older `*_map_add` names), use

```lean
import MoltResearch.Discrepancy.Deprecated
```
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (a d m n : ℕ)

  -- Nucleus objects should be present.
  #check apSum
  #check apSumOffset
  #check apSumFrom

  -- Canonical translation-friendly normal forms should be present.
  #check apSumFrom_eq_apSum_shift_add
  #check apSumFrom_eq_apSum_shift_add_left

  #check apSumOffset_eq_apSum_shift_add
  #check apSumOffset_eq_apSumOffset_shift_add

  -- Differences → tails normal forms should be present.
  #check apSum_sub_eq_apSumOffset
  #check apSumFrom_sub_eq_apSumFrom_tail
  #check apSumFrom_sub_eq_apSumOffset_shift_add

  -- Paper ↔ nucleus rewrite entrypoints should be present.
  #check sum_Icc_eq_apSum
  #check apSum_eq_sum_Icc
end

end MoltResearch
