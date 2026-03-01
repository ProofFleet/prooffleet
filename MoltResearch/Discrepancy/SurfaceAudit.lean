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
end

end MoltResearch
