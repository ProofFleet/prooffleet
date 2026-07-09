import Mathlib
/-!
Tier-1 Task 14: Nat.succ_ne_zero

Hint: `simp`

-/

theorem T1_14 (n : Nat) : Nat.succ n ≠ 0 :=
by
  exact Nat.succ_ne_zero n
