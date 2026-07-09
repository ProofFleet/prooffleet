import Mathlib

theorem T1_18 {α} {a b : α} : a = b → b = a := by
  intro h
  exact h.symm
