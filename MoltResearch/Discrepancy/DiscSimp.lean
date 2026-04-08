import MoltResearch.Discrepancy.EndpointSimp
import MoltResearch.Discrepancy.DiscOffsetSimp
import MoltResearch.Discrepancy.StepOneSimp
import MoltResearch.Discrepancy.IndexSimp
import MoltResearch.Discrepancy.Offset

/-!
# `DiscSimp`: opt-in simp rules for the discrepancy normal-form pipeline

This module is **opt-in**. It collects a small set of `[simp]` rules that are useful when you want a
`simp`-first normalization workflow for the discrepancy API, combining:

- endpoint cleanup (`Nat.succ` wrappers),
- step-one normalization (`… d …` ↦ `… 1 …` with the step pushed into the summand), and
- start-shift normalization for offset sums (push `m ↦ m + k` into the summand translation).

The stable surface (`import MoltResearch.Discrepancy`) does **not** enable these simp rules by
default, since they can change global simp normal forms.

Design constraint: all simp rules in this module are oriented so that they should not create simp
loops on their own; this file merely opts into a directed normal form.
-/

namespace MoltResearch

/-! ## Start-shift normalization (opt-in `[simp]`) -/

-- Prefer pushing a start-index shift into the summand translation.
attribute [simp] apSumOffset_shift_start_add
attribute [simp] apSumOffset_shift_start_add_left
attribute [simp] apSumOffset_shift_start_add_mul_left

-- Prefer pushing a start-index shift into the summand translation (discOffset-level).
attribute [simp] discOffset_shift_start_add
attribute [simp] discOffset_shift_start_add_mul_left

end MoltResearch
