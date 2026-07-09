import Mathlib

theorem T0_13 (a b c : Nat) : a = b → b = c → a = c := by
  intro h1 h2
  exact h1.trans h2
