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
  -- First, use the opt-in paper endpoint simp lemma (in `PaperSimp`) to land in `discOffset`.
  have h :=
    (natAbs_sum_Icc_add_affineEndpoints_eq_discOffset' (f := f) (a := a) (d := d) (m := m)
      (n := n))
  -- Then, rewrite the `discOffset` wrapper to the affine nucleus wrapper.
  have h' : discOffset (fun k => f (a + k)) d m n = affineDiscrepancy f (a + m * d) d n := by
    rw [discOffset_def, affineDiscrepancy_def]
    -- Now it suffices to rewrite the underlying AP sum.
    simpa [apSumOffset_shift_eq_apSumFrom_tail]
  exact h.trans h'

end MoltResearch
