import Mathlib

/-- Chaining equalities.

Proof pattern: after `intro`, `Eq.trans` (spelled `h1.trans h2`) glues `a = b` and `b = c`.
-/
theorem T1_17 {α} {a b c : α} : a = b → b = c → a = c := by
  intro h1 h2
  exact h1.trans h2
