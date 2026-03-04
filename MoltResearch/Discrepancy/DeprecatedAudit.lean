import MoltResearch.Discrepancy.Deprecated

/-!
# Discrepancy: deprecated surface audit (compile-time regression tests)

This file is a companion to `MoltResearch.Discrepancy.SurfaceAudit`.

It asserts that the explicit opt-in import

```lean
import MoltResearch.Discrepancy.Deprecated
```

continues to provide the older wrapper names (so downstream legacy files can keep compiling).
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (a d m n : ℕ)

  -- Deprecated wrappers should be present when explicitly imported.
  #check IsSignSequence.map_add
  #check IsSignSequence.map_add_left

  #check apSumFrom_eq_apSum_map_add
  #check apSumFrom_eq_apSum_map_add_left

  #check apSumFrom_map_add
  #check apSumFrom_map_add_left

  #check apSum_map_add
  #check apSum_map_add_left

  #check apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left_mul_left

  #check apSumOffset_eq_apSum_step_one_mul_left
  #check apSumOffset_eq_apSum_step_one_mul_left_add_left
  #check apSum_step_one_mul_left_eq_apSumOffset
  #check apSum_step_one_mul_left_add_left_eq_apSumOffset
end

end MoltResearch
