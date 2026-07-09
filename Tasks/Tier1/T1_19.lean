import Mathlib
/-!
Tier-1 Task 19: Nat.le_refl

Hint: `exact le_rfl` or `simp`

-/

theorem T1_19 (n : Nat) : n ≤ n :=
by
  exact Nat.le_refl n
