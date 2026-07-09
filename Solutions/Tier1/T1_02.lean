import Mathlib

theorem T1_02 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp
