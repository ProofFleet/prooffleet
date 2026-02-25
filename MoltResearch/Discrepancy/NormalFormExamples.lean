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

/-- Regression: canonical affine difference normalizes to a homogeneous sum on a shifted sequence.

This exercises `apSumFrom_sub_eq_apSum_shift_add`.
-/
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k + (a + m * d))) d n := by
  simpa using (apSumFrom_sub_eq_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: add-left variant of the previous normal form (translation constant written as `m*d + a`).

This exercises `apSumFrom_sub_eq_apSum_shift_add_left`.
-/
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    (apSumFrom_sub_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: mul-left variant of the add-left normal form (translation constant written as `d*m + a`).

This exercises `apSumFrom_sub_eq_apSum_shift_add_mul_left`.
-/
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k + (d * m + a))) d n := by
  simpa using
    (apSumFrom_sub_eq_apSum_shift_add_mul_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: commute the affine translation into the *function* (map-add normal form).

This exercises `apSumFrom_eq_apSum_map_add`.
-/
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using (apSumFrom_eq_apSum_map_add (f := f) (a := a) (d := d) (n := n))

/-- Regression: `a + x` variant of the map-add normal form.

This exercises `apSumFrom_eq_apSum_map_add_left`.
-/
example : apSumFrom f a d n = apSum (fun x => f (a + x)) d n := by
  simpa using (apSumFrom_eq_apSum_map_add_left (f := f) (a := a) (d := d) (n := n))

/-- Regression: affine tails normalize to `apSumOffset` on the shifted sequence `k ↦ f (k + a)`.

This is a common glue step when downstream lemmas are stated for `apSumOffset` only.
-/
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: tail affine AP sum as a homogeneous AP sum on a further-shifted sequence, with the
starting point written as `m*d + a`.

This exercises `apSumFrom_tail_eq_apSum_shift_add_left`.
-/
example :
    apSumFrom f (m * d + a) d n = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    (apSumFrom_tail_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

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

/-- Regression: mul-left variant of the previous normal form (translation constant written as `d*m`).

This exercises `apSumOffset_eq_apSum_shift_add_mul_left`.
-/
example : apSumOffset f d m n = apSum (fun k => f (k + d * m)) d n := by
  simpa using
    (apSumOffset_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: normalize a difference of homogeneous partial sums into an offset sum with
zero offset on a shifted sequence.

This exercises `apSum_sub_eq_apSumOffset_shift_add`.
-/
example :
    apSum f d (m + n) - apSum f d m = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  simpa using (apSum_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Regression: mul-left variant of the previous normal form (translation constant written as `d*m`).

This exercises `apSum_sub_eq_apSum_shift_add_mul_left`.
-/
example :
    apSum f d (m + n) - apSum f d m = apSum (fun k => f (k + d * m)) d n := by
  simpa using (apSum_sub_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m) (n := n))

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

/-! ### Predicate-level translation regression examples

These are tiny compile-time checks for the translation lemmas on discrepancy predicates
(`HasDiscrepancyAtLeast` / `HasAffineDiscrepancyAtLeast`).
-/

variable (C k : ℕ)

example :
    HasDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C := by
  simpa using (HasDiscrepancyAtLeast.of_map_add (f := f) (k := k) (C := C))

example :
    HasDiscrepancyAtLeast (fun x => f (k + x)) C → HasAffineDiscrepancyAtLeast f C := by
  simpa using (HasDiscrepancyAtLeast.of_map_add_left (f := f) (k := k) (C := C))

example :
    HasAffineDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C := by
  simpa using (HasAffineDiscrepancyAtLeast.of_map_add (f := f) (k := k) (C := C))

example :
    HasAffineDiscrepancyAtLeast (fun x => f (k + x)) C → HasAffineDiscrepancyAtLeast f C := by
  simpa using (HasAffineDiscrepancyAtLeast.of_map_add_left (f := f) (k := k) (C := C))

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

/-- Regression: rewrite an offset sum as an affine sum starting at a multiple of the step size.

This exercises `apSumOffset_eq_apSumFrom`.
-/
example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using (apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n))

/-- Regression: inverse orientation of `apSumOffset_eq_apSumFrom`.

This exercises `apSumFrom_mul_eq_apSumOffset`.
-/
example : apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Regression: mul-left variant of the previous lemma.

This exercises `apSumFrom_mul_left_eq_apSumOffset`.
-/
example : apSumFrom f (d * m) d n = apSumOffset f d m n := by
  simpa using (apSumFrom_mul_left_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Regression: rewrite `apSumFrom` to `apSumOffset` when the affine start is definitionally a
multiple of the step size.

This exercises `apSumFrom_eq_apSumOffset_of_eq_mul`.
-/
example (ha : a = m * d) : apSumFrom f a d n = apSumOffset f d m n := by
  simpa [ha] using
    (apSumFrom_eq_apSumOffset_of_eq_mul (f := f) (a := a) (d := d) (m := m) (n := n) (ha := ha))

/-- Regression: rewrite `apSumFrom` to an `apSumOffset` form when the affine start is a multiple of
the step size, expressed as a divisibility hypothesis.

This exercises `apSumFrom_exists_eq_apSumOffset_of_dvd`.
-/
example (h : d ∣ a) : ∃ m, apSumFrom f a d n = apSumOffset f d m n := by
  simpa using
    (apSumFrom_exists_eq_apSumOffset_of_dvd (f := f) (a := a) (d := d) (n := n) (h := h))

/-! ### Additional paper↔nucleus regression examples (`m ≤ n` normalization)

These are compile-time checks for the convenience lemmas that normalize an interval-sum with a
variable upper endpoint `n` (under a hypothesis `m ≤ n`) into the canonical nucleus offset-sum form
`apSumOffset f d m (n - m)` (and back).
-/

variable (m1 n1 : ℕ) (hmn : m1 ≤ n1)

/-- Regression: normalize a paper interval sum with variable upper endpoint into an offset sum. -/
example :
    (Finset.Icc (m1 + 1) n1).sum (fun i => f (i * d)) = apSumOffset f d m1 (n1 - m1) := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m1) (n := n1) hmn)

/-- Regression: translation-friendly `d * i` variant of the previous normalization lemma. -/
example :
    (Finset.Icc (m1 + 1) n1).sum (fun i => f (d * i)) = apSumOffset f d m1 (n1 - m1) := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m1) (n := n1) hmn)

/-- Regression: inverse orientation (offset sum → paper interval sum) under `m ≤ n`. -/
example :
    apSumOffset f d m1 (n1 - m1) = (Finset.Icc (m1 + 1) n1).sum (fun i => f (i * d)) := by
  simpa using
    (apSumOffset_eq_sum_Icc_of_le (f := f) (d := d) (m := m1) (n := n1) hmn)

/-- Regression: translation-friendly `d * i` variant of the previous inverse-orientation lemma. -/
example :
    apSumOffset f d m1 (n1 - m1) = (Finset.Icc (m1 + 1) n1).sum (fun i => f (d * i)) := by
  simpa using
    (apSumOffset_eq_sum_Icc_of_le_mul_left (f := f) (d := d) (m := m1) (n := n1) hmn)

/-! ### Mul-left paper↔nucleus regression examples

These cover the `d * i` binder convention for the core paper normal forms.
-/

/-- Regression: rewrite an offset sum to paper notation using the `d * i` summand convention.

This exercises `apSumOffset_eq_sum_Icc_mul_left`.
-/
example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using (apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: rewrite the `d * i` paper interval sum back to the nucleus offset-sum API.

This exercises `sum_Icc_eq_apSumOffset_mul_left`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: rewrite a canonical difference of partial sums to the length-indexed paper form
with the `d * (m+i)` summand convention.

This exercises `apSum_sub_eq_sum_Icc_length_mul_left`.
-/
example :
    apSum f d (m + n) - apSum f d m = (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using (apSum_sub_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n))

end NormalFormExamples

end MoltResearch
