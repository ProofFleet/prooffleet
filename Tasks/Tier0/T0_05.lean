import Mathlib

-- Hint: right

theorem T0_05 (P Q : Prop) : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ
