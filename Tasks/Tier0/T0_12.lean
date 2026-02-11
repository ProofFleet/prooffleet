import Mathlib

-- Hint: after intro h, exact h.symm

theorem T0_12 (α : Type) (x y : α) : x = y → y = x := by
  intro h
  exact h.symm
