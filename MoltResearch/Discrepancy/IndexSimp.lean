import MoltResearch.Discrepancy.Basic

/-!
# `IndexSimp`: opt-in simp lemmas for common index arithmetic shapes

This module is **opt-in**: it provides a *minimal*, loop-free collection of `[simp]` lemmas that
normalize the most common index arithmetic patterns appearing in the discrepancy “nucleus” API.

Design goals:
- normalize `m + (i + 1)` into the canonical left-associated `m + i + 1`;
- normalize `d * (m + i + 1)` into `(m + i + 1) * d` (since `Nat.mul_comm` is not `[simp]` by
  default, this is still loop-free);
- keep the simp set small and non-invasive.

These lemmas are intended to be enabled via `import MoltResearch.Discrepancy.DiscSimp` (or directly
by importing this file).
-/

namespace MoltResearch

/-! ## Addition shape: `m + (i + 1)` -/

/-- Normalize `m + (i + 1)` into the canonical left-associated `m + i + 1`.

This is intentionally specialized to `+ 1` to keep the simp set small.
-/
@[simp] lemma add_add_one_eq_add_add_one_left (m i : ℕ) : m + (i + 1) = m + i + 1 := by
  -- `simp` knows how to rewrite `i + 1` as `Nat.succ i` and can close using associativity.
  simp [Nat.add_assoc]

/-! ## Multiplication shape: `d * (m + i + 1)` -/

/-- Normalize multiplication order for the common index shape `m + i + 1`.

Orientation note: we rewrite toward `(m + i + 1) * d`.
Since `Nat.mul_comm` is not in the global simp set, this does not create simp loops.
-/
@[simp] lemma mul_add_add_one_comm (d m i : ℕ) : d * (m + i + 1) = (m + i + 1) * d := by
  simpa [Nat.mul_comm]

end MoltResearch
