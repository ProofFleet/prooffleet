import MoltResearch.Logic

-- Tier-0 allowed tactics: intro, exact, apply, assumption, constructor, cases, left, right, rfl, simp
-- Hint: use the lemma from MoltResearch.Logic

theorem T0_21 (P : Prop) : P → P := by
  -- your proof here should be one line
  simpa using MoltResearch.Logic.id P
