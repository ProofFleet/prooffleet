import Mathlib

/-- Conjunction commutes.

Proof pattern: an `Iff` of conjunctions is two implications (`constructor`), and each direction
just swaps the components of the anonymous constructor: `⟨h.2, h.1⟩`.
-/
theorem T1_01 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩
