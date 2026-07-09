import Mathlib

/-- Conjunction distributes over disjunction (forward direction).

Proof pattern: keep the shared component `h.1` and case-split on the disjunction `h.2`;
each branch rebuilds the pair inside the matching `Or` constructor.
-/
theorem T1_03 (P Q R : Prop) : (P ∧ (Q ∨ R)) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  cases h.2 with
  | inl hq => exact Or.inl ⟨h.1, hq⟩
  | inr hr => exact Or.inr ⟨h.1, hr⟩
