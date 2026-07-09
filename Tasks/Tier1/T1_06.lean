import Mathlib
/-!
Tier-1 Task 06: Nat.add_comm

Hint: `simp` / `Nat.add_comm`

-/

theorem T1_06 (a b : Nat) : a + b = b + a :=
by
  exact Nat.add_comm a b
