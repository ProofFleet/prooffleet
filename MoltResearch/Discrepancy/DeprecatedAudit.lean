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

  -- Deprecated `discOffset` congruence variants (not part of the stable surface).
  #check discOffset_congr_Icc
  #check discOffset_congr_finset_Icc

  #check apSumFrom_eq_apSumOffset_step_one_zero_m
  #check apSumFrom_eq_apSumOffset_step_one_zero_m_add_left

  #check apSumFrom_eq_apSumOffset_step_one_add_left_via_shift_add
  #check apSumFrom_eq_apSumOffset_step_one_via_shift_add
  #check sum_Icc_eq_apSumOffset_step_one_via_shift_add


  #check apSumOffset_eq_apSum_step_one_mul_left
  #check apSumOffset_eq_apSum_step_one_mul_left_add_left
  #check apSum_step_one_mul_left_eq_apSumOffset
  #check apSum_step_one_mul_left_add_left_eq_apSumOffset

  -- Deprecated alias names for mul_right_cfirst families.
  #check apSum_mul_right_cfirst
  #check apSumOffset_mul_right_cfirst
  #check apSumFrom_mul_right_cfirst

  -- Deprecated alias names for mul_left argument-order variants.
  #check apSum_mul_left_ffirst
  #check apSumOffset_mul_left_ffirst
  #check apSumFrom_mul_left_ffirst

  -- Deprecated inverse-orientation step-one aliases.
  #check apSum_step_one_eq_apSum
  #check apSumOffset_step_one_eq_apSumOffset
  #check apSumOffset_step_one_zero_m_eq_apSumOffset
  #check apSumOffset_step_one_zero_m_add_left_eq_apSumOffset
  -- Note: there is no deprecated alias named `apSumOffset_step_one_eq_apSum`.
  #check apSum_step_one_eq_apSumOffset
  #check apSum_step_one_eq_apSumFrom
  #check apSum_step_one_eq_apSumFrom_tail
  #check apSumFrom_step_one_eq_apSumFrom
  #check apSumFrom_step_one_add_left_eq_apSumFrom
end

end MoltResearch
