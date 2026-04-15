import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset

/-!
# `CoherenceSimp`: minimal simp surface for discrepancy API coherence

This module is part of the **stable import surface** (`import MoltResearch.Discrepancy`).
It enables only a *small* set of simp rules that normalize the most common degenerate/boilerplate
parameter patterns:

- start-index arithmetic like `m + (n + k)` (push the start shift into the summand translation),
- and the corresponding `discOffset` wrapper normalization.

Design intent:
- Keep this file small.
- Prefer simp rules that move toward the nucleus normal forms used across Track B.
- Avoid enabling the full `DiscSimp` bundle, which is intentionally opt-in.

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — API coherence simp surface.
-/

namespace MoltResearch

/-! ## Start-shift normalization (stable-surface `[simp]`) -/

-- Normalize `apSumOffset f d (m + k) n` by pushing the shift into the summand translation.
attribute [simp] apSumOffset_shift_start_add
attribute [simp] apSumOffset_shift_start_add_mul_left

-- Same normalization at the discrepancy wrapper level.
attribute [simp] discOffset_shift_start_add
attribute [simp] discOffset_shift_start_add_mul_left

end MoltResearch
