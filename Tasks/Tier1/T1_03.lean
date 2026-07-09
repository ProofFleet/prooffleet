import Mathlib
/-!
Tier-1 Task 03: and distributes over or (→)

-/

theorem T1_03 (P Q R : Prop) : (P ∧ (Q ∨ R)) → (P ∧ Q) ∨ (P ∧ R) :=
by
  intro h
  cases h.2 with
  | inl hq => exact Or.inl ⟨h.1, hq⟩
  | inr hr => exact Or.inr ⟨h.1, hr⟩
