-- Tier-0 allowed tactics: intro, exact, apply, assumption, constructor, cases, left, right, rfl, simp
-- Hint: intro h; exact h

theorem T0_01 (P : Prop) : P → P := by
  intro h
  exact h
