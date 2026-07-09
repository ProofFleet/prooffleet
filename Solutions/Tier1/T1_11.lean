import Mathlib

theorem T1_11 {α β} (f : α → β) : Option.map f none = (none : Option β) := by
  rfl
