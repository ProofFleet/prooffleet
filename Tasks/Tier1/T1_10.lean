import Mathlib
/-!
Tier-1 Task 10: List.map_id

Hint: `simp`

-/

open List

theorem T1_10 {α} (xs : List α) : xs.map (fun x => x) = xs :=
by
  simp
