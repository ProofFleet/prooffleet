import Mathlib

/-- Chaining order proofs.

Proof pattern: `Nat.le_trans` is exactly the two-hypothesis implication, so `exact` applies it
point-free.
-/
theorem T1_20 (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  exact Nat.le_trans
