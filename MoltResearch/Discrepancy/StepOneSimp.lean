import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Affine   -- for `apSumFrom_tail_eq_apSumOffset_step_one`

/-!
# Step-one simp rules

This module opts into a *more aggressive* `simp` normal form for arithmetic-progression sums:
we mark the “step-one” reindexing lemma for `apSumOffset` as a simp rule.

Rationale: many reindexing proofs want to *push the step size into the summand*, rewriting

`apSumOffset f d m n` ↦ `apSumOffset (fun k => f (k*d)) 1 m n`.

We do **not** enable this by default in the main discrepancy surface, because it can change
simp normal forms globally (and may require minor proof adjustments in downstream files).

Import this module when you explicitly want that simp behavior.
-/

namespace MoltResearch

-- Prefer the step-one normal form for `apSumOffset` when simplifying.
attribute [simp] apSumOffset_eq_apSumOffset_step_one

-- Also prefer the step-one offset normal form for affine tails.
attribute [simp] apSumFrom_tail_eq_apSumOffset_step_one

-- Regression test: importing this module should let `simp` push the step into the summand.
example (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
  simp

-- Regression test: importing this module should let `simp` normalize paper affine tails via the
-- step-one offset nucleus.
example (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k * d)) 1 m n := by
  simp

end MoltResearch
