import Mathlib
/-!
Tier-1 Task 16: simp with Prod

Hint: `rfl`

-/

theorem T1_16 (a b c : Nat) : (a, b, c).2.1 = b :=
by
  simp
