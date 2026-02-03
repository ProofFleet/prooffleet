import MoltResearch.Logic

-- Tier-0 allowed tactics: intro, exact, apply, assumption, constructor, cases, left, right, rfl, simp
-- Hint: use the lemma from MoltResearch.Logic

theorem T0_22 (P Q : Prop) : P ∧ Q → P := by
  simpa using MoltResearch.Logic.and_left P Q
