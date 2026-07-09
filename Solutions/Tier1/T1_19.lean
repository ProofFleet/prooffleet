import Mathlib

theorem T1_19 (n : Nat) : n ≤ n := by
  exact Nat.le_refl n
