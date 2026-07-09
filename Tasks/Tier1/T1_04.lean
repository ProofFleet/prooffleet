import Mathlib
/-!
Tier-1 Task 04: exists implies not forall not

-/

theorem T1_04 {α : Type} (p : α → Prop) : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
by
  intro hex hall
  obtain ⟨x, hx⟩ := hex
  exact hall x hx
