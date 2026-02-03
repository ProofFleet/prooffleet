import Mathlib

-- Tier-0 allowed tactics: intro, exact, apply, assumption, constructor, cases, left, right, rfl, simp
-- Hint: after intro h, use h.1

theorem T0_02 (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1
