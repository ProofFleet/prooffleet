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

/-- Right projection of conjunction. -/
theorem and_right (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.2

/-- Transitivity of implication. -/
theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  exact hqr (hpq hp)

/-- Commutativity of conjunction. -/
theorem and_comm (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-- Associativity of conjunction. -/
theorem and_assoc (P Q R : Prop) : (P ∧ Q ∧ R) ↔ (P ∧ Q) ∧ R := by
  constructor
  · intro h
    rcases h with ⟨hp, hqr⟩
    rcases hqr with ⟨hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩
  · intro h
    rcases h with ⟨hpq, hr⟩
    rcases hpq with ⟨hp, hq⟩
    exact ⟨hp, ⟨hq, hr⟩⟩

/-- Commutativity of disjunction. -/
theorem or_comm (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

/-- Associativity of disjunction. -/
theorem or_assoc (P Q R : Prop) : (P ∨ Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
        cases hqr with
        | inl hq => exact Or.inl (Or.inr hq)
        | inr hr => exact Or.inr hr
  · intro h
    cases h with
    | inl hpq =>
        cases hpq with
        | inl hp => exact Or.inl hp
        | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)

/-- Curry a function on a conjunction. -/
theorem curry (P Q R : Prop) : ((P ∧ Q) → R) → (P → Q → R) := by
  intro h hp hq
  exact h ⟨hp, hq⟩

/-- Uncurry a curried function into one on a conjunction. -/
theorem uncurry (P Q R : Prop) : (P → Q → R) → ((P ∧ Q) → R) := by
  intro h hpq
  exact h hpq.1 hpq.2

/-- Implication distributes over conjunction. -/
theorem imp_and (P Q R : Prop) : (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  constructor
  · intro h
    exact ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩
  · intro h hp
    exact ⟨h.1 hp, h.2 hp⟩

end MoltResearch.Logic
