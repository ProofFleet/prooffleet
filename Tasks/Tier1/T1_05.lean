import Mathlib
/-!
Tier-1 Task 05: forall implies not exists not

-/

theorem T1_05 {α : Type} (p : α → Prop) : (∀ x, p x) → ¬ (∃ x, ¬ p x) :=
by
  intro hall hex
  obtain ⟨x, hnx⟩ := hex
  exact hnx (hall x)
