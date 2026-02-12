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

/-! ## Negation + distributivity -/

/-- Contrapositive: from `P → Q` we get `¬ Q → ¬ P`. -/
theorem contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro hpq hnotq hp
  exact hnotq (hpq hp)

/-- Negation of a conjunction. -/
theorem not_and (P Q : Prop) : ¬ (P ∧ Q) ↔ (P → ¬ Q) := by
  constructor
  · intro h hp hq
    apply h
    exact And.intro hp hq
  · intro h hpq
    rcases hpq with ⟨hp, hq⟩
    have hnotq : ¬ Q := h hp
    exact hnotq hq

/-- Negation of a disjunction. -/
theorem not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  · intro h
    have hnp : ¬ P := by
      intro hp
      apply h
      exact Or.inl hp
    have hnq : ¬ Q := by
      intro hq
      apply h
      exact Or.inr hq
    exact ⟨hnp, hnq⟩
  · intro h hPQ
    cases hPQ with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

/-- Distributivity of conjunction over disjunction. -/
theorem and_distrib_or (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    rcases h with ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro h
    cases h with
    | inl hpq =>
        rcases hpq with ⟨hp, hq⟩
        exact ⟨hp, Or.inl hq⟩
    | inr hpr =>
        rcases hpr with ⟨hp, hr⟩
        exact ⟨hp, Or.inr hr⟩

/-- Distributivity of disjunction over conjunction. -/
theorem or_distrib_and (P Q R : Prop) : (P ∨ (Q ∧ R)) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
        exact ⟨Or.inl hp, Or.inl hp⟩
    | inr hqr =>
        rcases hqr with ⟨hq, hr⟩
        exact ⟨Or.inr hq, Or.inr hr⟩
  · intro h
    rcases h with ⟨hpq, hpr⟩
    cases hpq with
    | inl hp =>
        exact Or.inl hp
    | inr hq =>
        cases hpr with
        | inl hp =>
            exact Or.inl hp
        | inr hr =>
            exact Or.inr ⟨hq, hr⟩

end MoltResearch.Logic
