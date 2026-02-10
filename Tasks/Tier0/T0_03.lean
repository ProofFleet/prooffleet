import Mathlib

-- Hint: constructor

theorem T0_03 (P Q : Prop) : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ
