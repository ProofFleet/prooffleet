import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.AffineTail
import MoltResearch.Discrepancy.Translate

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

/-- Regression: “step-one” normalization for homogeneous AP sums.

This exercises `apSum_eq_apSum_step_one`.
-/
example : apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  simpa using (apSum_eq_apSum_step_one (f := f) (d := d) (n := n))

/-- Regression: “step-one” normalization for affine AP sums, using the translation-friendly
`k * d + a` summand convention.

This exercises `apSumFrom_eq_apSum_step_one_add_left`.
-/
example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using (apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n))

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

/-- Regression: eliminate the tail parameter by absorbing it into the translation constant.

This exercises `apSumFrom_tail_eq_apSumOffset_shift_add_zero_m`.
-/
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: canonical difference of offset sums normalizes to an `m = 0` offset sum on a shifted
sequence.

This exercises `apSumOffset_sub_eq_apSumOffset_shift_add`.
-/
example (n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  simpa using
    (apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Regression: “step-one” normalization for offset AP sums, using the translation-friendly
`k * d + const` summand convention.

This exercises `apSumOffset_eq_apSum_step_one_add_left`.
-/
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using
    (apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: “step-one” normalization for offset AP sums, keeping an `apSumOffset` shape and
eliminating the explicit offset parameter.

This exercises `apSumOffset_eq_apSumOffset_step_one_zero_m`.
-/
example : apSumOffset f d m n = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
  simpa using
    (apSumOffset_eq_apSumOffset_step_one_zero_m (f := f) (d := d) (m := m) (n := n))

/-- Regression: variant of the previous lemma using the translation-friendly `k * d + const`
convention.

This exercises `apSumOffset_eq_apSumOffset_step_one_zero_m_add_left`.
-/
example : apSumOffset f d m n = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  simpa using
    (apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: eliminate the explicit offset parameter by rewriting to a homogeneous `apSum` on a
shifted sequence (translation-friendly `k + const` form).

This exercises `apSumOffset_eq_apSum_shift_add`.
-/
example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Regression: compose a shift-add translation with the offset-to-homogeneous normal form.

This exercises `apSumOffset_shift_add_eq_apSum_shift_add`.
-/
example :
    apSumOffset (fun k => f (k + a)) d m n = apSum (fun k => f (k + (a + m * d))) d n := by
  simpa using
    (apSumOffset_shift_add_eq_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: inverse orientation of `apSumOffset_shift_add_eq_apSum_shift_add`.

This exercises `apSum_shift_add_eq_apSumOffset_shift_add`.
-/
example :
    apSum (fun k => f (k + (a + m * d))) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSum_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: rewrite the canonical difference `apSum f d (m+n) - apSum f d m` to the fixed-lower-endpoint
length-indexed interval-sum form over `Icc 1 n`.

This exercises `apSum_sub_eq_sum_Icc_length`.
-/
example :
    apSum f d (m + n) - apSum f d m = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using (apSum_sub_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n))

/-- Regression: rewrite the length-indexed paper interval sum back to the nucleus offset-sum API.

This exercises `sum_Icc_eq_apSumOffset_length`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset_length (f := f) (d := d) (m := m) (n := n))

/-- Regression: rewrite the paper affine-tail interval sum (translation-friendly `i*d + a`) back
into the nucleus affine tail normal form.

This exercises `sum_Icc_eq_apSumFrom_tail_add`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) = apSumFrom f (a + m * d) d n := by
  simpa using (sum_Icc_eq_apSumFrom_tail_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: rewrite the nucleus affine tail sum to the fixed-lower-endpoint (1) length-indexed
interval-sum form, using the translation-friendly `((m+i)*d + a)` summand convention.

This exercises `apSumFrom_tail_eq_sum_Icc_length_add`.
-/
example :
    apSumFrom f (a + m * d) d n = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d + a)) := by
  simpa using (apSumFrom_tail_eq_sum_Icc_length_add (f := f) (a := a) (d := d) (m := m) (n := n))

end NormalFormExamples

end MoltResearch
