import Mathlib
/-!
Tier-1 Task 17: Eq.trans

Hint: `intro h1 h2; exact h1.trans h2`

-/

theorem T1_17 {α} {a b c : α} : a = b → b = c → a = c :=
by
  intro h1 h2
  exact h1.trans h2
