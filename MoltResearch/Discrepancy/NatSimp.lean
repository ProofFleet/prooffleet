import MoltResearch.Discrepancy.Basic

/-!
# Nat simp lemmas for discrepancy summands

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Minimize simp churn for `Nat` arithmetic in summands”.

Goal: provide a **tiny, loop-free** `[simp]` surface for the endpoint arithmetic that commonly
appears *inside* discrepancy summands, e.g.

- `(m + (i+1)) * d`  →  `(m + i + 1) * d`
- `a + (m + (i+1)) * d`  →  `a + (m + i + 1) * d`

Design constraints:
- Orientation is directed toward the canonical `… + i + 1` form.
- Avoid commutativity (`Nat.add_comm`) under binders.
- Keep the set small: this is for predictable simp normalization, not arithmetic automation.
-/

namespace MoltResearch

/-! ## Canonical endpoint normal forms (`Nat`) -/

/-- Normalize `m + (i+1)` into the associativity-friendly `m + i + 1` form.

We prefer this over rewriting to `Nat.succ (m+i)` since the discrepancy API tends to use `+ 1`
endpoints.
-/
@[simp] lemma add_add_one' (m i : ℕ) : m + (i + 1) = m + i + 1 := by
  simp [Nat.add_assoc]

/-- Normalize the common summand index shape `(m + (i+1)) * d`.

This lemma is intentionally *not* stated with `Nat.succ` to avoid triggering `Nat.add_succ`/
`Nat.succ_add` loops.
-/
@[simp] lemma add_add_one_mul (m i d : ℕ) : (m + (i + 1)) * d = (m + i + 1) * d := by
  simp

/-- Normalize the common affine summand index shape `a + (m + (i+1)) * d`.

This is the main “simp-churn reducer”: it keeps the binder arithmetic in a canonical associative
shape without forcing users to manually apply `Nat.add_assoc`.
-/
@[simp] lemma add_add_one_mul_add_left (a m i d : ℕ) : a + (m + (i + 1)) * d = a + (m + i + 1) * d := by
  simp

end MoltResearch
