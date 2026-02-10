import Mathlib

-- Hint: left

theorem T0_04 (P Q : Prop) : P → P ∨ Q := by
  intro hP
  left
  exact hP
