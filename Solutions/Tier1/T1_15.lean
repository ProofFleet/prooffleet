import Mathlib

theorem T1_15 (n : Nat) : 0 ≠ Nat.succ n := by
  exact (Nat.succ_ne_zero n).symm
