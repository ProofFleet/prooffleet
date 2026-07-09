import Mathlib
/-!
Tier-1 Task 01: and commutes

-/

theorem T1_01 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) :=
by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩
