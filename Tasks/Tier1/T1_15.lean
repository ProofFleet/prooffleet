import Mathlib
/-!
Tier-1 Task 15: Nat.zero_ne_succ

Hint: `simp`

-/

theorem T1_15 (n : Nat) : 0 ≠ Nat.succ n :=
by
  exact (Nat.succ_ne_zero n).symm
