import Mathlib

/-!
# Logic (micro-library)

This module exists to create a small, stable nucleus in `MoltResearch/` that tasks can depend on.
We intentionally keep it tiny and well-documented.

As the project grows, prefer moving reusable lemmas here (or into a more specific module).
-/

namespace MoltResearch.Logic

/-- Identity: if `P` then `P`. Useful as the simplest nontrivial example. -/
theorem id (P : Prop) : P → P := by
  intro h
  exact h

/-- Left projection of conjunction. -/
theorem and_left (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1

end MoltResearch.Logic
