import Mathlib
/-!
Tier-1 Task 20: Nat.le_trans

Hint: `exact le_trans`

-/

theorem T1_20 (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c :=
by
  exact Nat.le_trans
