import MoltResearch.Logic

theorem T0_22 (P Q : Prop) : P ∧ Q → P := by
  exact MoltResearch.Logic.and_left P Q
