import Mathlib
/-!
Tier-1 Task 11: Option.map_none

Hint: `rfl`

-/

theorem T1_11 {α β} (f : α → β) : Option.map f none = (none : Option β) :=
by
  rfl
