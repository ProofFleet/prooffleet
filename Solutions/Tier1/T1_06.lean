import Mathlib

theorem T1_06 (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
