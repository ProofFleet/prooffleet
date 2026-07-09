import Mathlib
/-!
Tier-1 Task 07: Nat.add_assoc

Hint: `simp [Nat.add_assoc]`

-/

theorem T1_07 (a b c : Nat) : a + b + c = a + (b + c) :=
by
  exact Nat.add_assoc a b c
