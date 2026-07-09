import Mathlib
/-!
Tier-1 Task 13: Bool.not_not

Hint: `cases b <;> rfl`

-/

theorem T1_13 (b : Bool) : (!(!b)) = b :=
by
  simp
