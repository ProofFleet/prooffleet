import Mathlib
/-!
Tier-1 Task 12: Option.map_some

Hint: `rfl`

-/

theorem T1_12 {α β} (f : α → β) (x : α) : Option.map f (some x) = some (f x) :=
by
  rfl
