import Mathlib

theorem T0_12 (α : Type) (x y : α) : x = y → y = x := by
  intro h
  exact h.symm
