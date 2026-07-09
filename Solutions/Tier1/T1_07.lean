import Mathlib

theorem T1_07 (a b c : Nat) : a + b + c = a + (b + c) := by
  exact Nat.add_assoc a b c
