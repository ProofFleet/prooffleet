import Mathlib
/-!
Tier-1 Task 09: List.length_append

Hint: `simp`

-/

open List

theorem T1_09 {α} (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length :=
by
  simp
