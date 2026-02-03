import Mathlib

-- Tier-0 allowed tactics: intro, exact, apply, assumption, constructor, cases, left, right, rfl, simp

theorem T0_01 (P : Prop) : P → P := by
  intro h
  exact h
