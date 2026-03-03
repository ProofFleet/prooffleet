import MoltResearch.Discrepancy.Affine

/-!
# Affine endpoint simp rules

This module opts into a slightly more aggressive `simp` normal form for *affine endpoint* Nat
arithmetic.

In many rewrite pipelines we encounter expressions like:
- `a + (m+1)*d`
- `a + (m+n)*d`

The lemmas in `MoltResearch.Discrepancy.Affine` provide directed normalisation rewrites, but we
avoid enabling the stronger `(m+n)` expansion globally because it can increase simp search space
(and has caused recursion depth issues in some proofs).

Import this module when you explicitly want `simp` to expand
`a + (m+n)*d` into `a + m*d + n*d`.
-/

namespace MoltResearch

-- Enable the `(m+n)` endpoint expansion as a simp rule.
attribute [simp] add_mul_add_norm

-- Also expose the `(m+1)` endpoint normalisation as a simp rule for completeness.
-- (It is already `[simp]` in the base module; repeating the attribute here keeps this module
-- self-documenting as the place to import when you want endpoint simp normalisation.)
attribute [simp] add_mul_succ_norm

-- Regression test: importing this module should let `simp` normalize affine endpoints.
example (a m n d : ℕ) : a + (m + n) * d = a + m * d + n * d := by
  simp

-- Regression test for the `(m+1)` normalisation.
example (a m d : ℕ) : a + (m + 1) * d = a + d * (m + 1) := by
  simp

end MoltResearch
