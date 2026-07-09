import Mathlib
/-!
Tier-1 Task 08: Nat.mul_zero

Hint: `simp`

-/

theorem T1_08 (a : Nat) : a * 0 = 0 :=
by
  exact Nat.mul_zero a
