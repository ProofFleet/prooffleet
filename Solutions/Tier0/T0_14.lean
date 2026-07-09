import Mathlib

theorem T0_14 (P : Prop) : False → P := by
  intro h
  cases h
