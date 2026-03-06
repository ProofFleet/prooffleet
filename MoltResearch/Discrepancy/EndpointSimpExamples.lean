import MoltResearch.Discrepancy

/-!
# Regression examples for `MoltResearch.Discrepancy.EndpointSimp`

This module is a compile-only check that the endpoint simp lemmas remain usable
when importing the stable surface `MoltResearch.Discrepancy`.

It is intentionally **not** imported by `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

example (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (Nat.succ n) = apSumOffset f d m n + f ((m + Nat.succ n) * d) := by
  simp

example (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (Nat.succ n) = apSum f d n + f ((Nat.succ n) * d) := by
  simp

end MoltResearch
