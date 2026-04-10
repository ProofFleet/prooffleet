import MoltResearch.Discrepancy
import MoltResearch.Discrepancy.PaperSimp

/-!
# Regression examples for `MoltResearch.Discrepancy.PaperSimp`

Compile-only checks that the opt-in paper endpoint simp pipeline stays usable while
importing the stable surface `MoltResearch.Discrepancy`.

This file is intentionally **not** imported by `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

-- Homogeneous tail form: `∑_{i=m+1}^{m+n} f (i*d)`.
example (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) = discOffset f d m n := by
  simp

-- Affine endpoint form: `∑_{i=m+1}^{m+n} f (a + i*d)`.
example (f : ℕ → ℤ) (a d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d))) =
        affineDiscrepancy f (a + m * d) d n := by
  simp

end MoltResearch
