import MoltResearch.Discrepancy
import Mathlib.Init

/-!
# Discrepancy stable surface checklist (compile-time tests)

This module is a tiny API-surface regression test for:

```lean
import MoltResearch.Discrepancy
```

It should:
- expose the intended normal-form lemmas (spot-checks below)
- *not* expose deprecated legacy aliases (those live in `MoltResearch.Discrepancy.Deprecated`)

This file is built explicitly by `make ci`.
-/

namespace MoltResearch

section

-- Spot-check: a few “canonical” normal-form lemmas should be available from the stable surface.
#check apSumFrom_eq_apSum_shift_add
#check apSumFrom_eq_apSum_shift_add_left
#check apSumFrom_sub_eq_apSumOffset_shift_add

-- Deprecated legacy wrappers should *not* be in the stable surface.
-- If one of these starts typechecking, we accidentally re-exported deprecated names.

/-- error: Unknown identifier `apSumFrom_eq_apSum_map_add` -/
#guard_msgs in
#check apSumFrom_eq_apSum_map_add

/-- error: Unknown identifier `apSumFrom_eq_apSum_map_add_left` -/
#guard_msgs in
#check apSumFrom_eq_apSum_map_add_left

/-- error: Unknown identifier `apSum_map_add` -/
#guard_msgs in
#check apSum_map_add

end

end MoltResearch
