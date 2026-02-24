import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.AffineTail

/-!
# Discrepancy: normal-form regression examples

This file contains small `example` blocks intended as *compile-time regression tests*
for the preferred normal-form rewrite pipelines described in `MoltResearch/Discrepancy.lean`.

These are not meant to be deep theorems; they are here to keep the stable lemma names and
orientations from accidentally drifting.
-/

namespace MoltResearch

section NormalFormExamples

variable (f : ℕ → ℤ) (a d m n : ℕ)

/-- Regression: canonical affine difference normalizes to an offset sum on a shifted sequence
(translation-friendly `k + a` form). -/
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using (apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: affine tails normalize to `apSumOffset` on the shifted sequence `k ↦ f (k + a)`.

This is a common glue step when downstream lemmas are stated for `apSumOffset` only.
-/
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

end NormalFormExamples

end MoltResearch
