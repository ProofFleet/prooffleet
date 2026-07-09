import Mathlib
/-!
Tier-1 Task 18: Eq.symm

Hint: `exact Eq.symm`

-/

theorem T1_18 {α} {a b : α} : a = b → b = a :=
by
  intro h
  exact h.symm
