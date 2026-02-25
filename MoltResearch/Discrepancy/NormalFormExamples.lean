import MoltResearch.Discrepancy

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

/-- Regression: `apSum` at `n = 0` (simp lemma `apSum_zero`). -/
example : apSum f d 0 = 0 := by
  simpa using (apSum_zero (f := f) (d := d))

/-- Regression: `apSumOffset` at `n = 0` (simp lemma `apSumOffset_zero`). -/
example : apSumOffset f d m 0 = 0 := by
  simpa using (apSumOffset_zero (f := f) (d := d) (m := m))

/-- Regression: `apSumFrom` at `n = 0` (simp lemma `apSumFrom_zero`). -/
example : apSumFrom f a d 0 = 0 := by
  simpa using (apSumFrom_zero (f := f) (a := a) (d := d))

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

/-- Regression: “step-one” normalization for affine AP sums directly into the `apSumOffset` API.

This exercises `apSumFrom_eq_apSumOffset_step_one_zero_m_add_left`.
-/
example : apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    (apSumFrom_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (n := n))

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

/-- Regression: mul-left translation-constant wrapper for splitting affine sums by length.

This exercises `apSumFrom_add_length_eq_add_apSum_shift_add_mul_left`.
-/
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSum (fun k => f (k + (d * m + a))) d n := by
  simpa using
    (apSumFrom_add_length_eq_add_apSum_shift_add_mul_left (f := f) (a := a) (d := d) (m := m) (n := n))

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

/-- Regression: affine AP sums normalize to homogeneous sums on a shifted sequence, using the
`a + k` summand convention.

This exercises `apSumFrom_eq_apSum_shift`.
-/
example : apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  simpa using (apSumFrom_eq_apSum_shift (f := f) (a := a) (d := d) (n := n))

/-- Regression: offset sums normalize to homogeneous sums on a shifted sequence, using the
`m*d + k` summand convention.

This exercises `apSumOffset_eq_apSum_shift`.
-/
example : apSumOffset f d m n = apSum (fun k => f (m * d + k)) d n := by
  simpa using (apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n))

/-- Regression: offset sums on a shifted sequence normalize to a homogeneous sum on a further-shifted
sequence, using the `a + k` binder convention.

This exercises `apSumOffset_shift_add_left_eq_apSum_shift_add_left`.
-/
example :
    apSumOffset (fun k => f (a + k)) d m n = apSum (fun k => f ((a + m * d) + k)) d n := by
  simpa using
    (apSumOffset_shift_add_left_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n))

/-- Regression: inverse orientation of the previous normal form.

This exercises `apSum_shift_add_left_eq_apSumOffset_shift_add_left`.
-/
example :
    apSum (fun k => f ((a + m * d) + k)) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (apSum_shift_add_left_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n))

/-- Regression: affine tails normalize to `apSumOffset` on the shifted sequence `k ↦ f (k + a)`.

This is a common glue step when downstream lemmas are stated for `apSumOffset` only.
-/
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: same affine-tail normal form, with the shifted sequence written as `k ↦ f (a + k)`.

This exercises `apSumFrom_tail_eq_apSumOffset_shift`.
-/
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: split an affine AP sum by length and normalize the tail as an offset sum on the
shifted sequence `k ↦ f (a + k)`.

This exercises `apSumFrom_add_length_eq_add_apSumOffset_shift`.
-/
example :
    apSumFrom f a d (m + n) = apSumFrom f a d m + apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (apSumFrom_add_length_eq_add_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: split off the *last* term of an affine tail sum, with the affine start written as
`m*d + a`.

This exercises `apSumFrom_tail_succ_start_add_left`.
-/
example :
    apSumFrom f (m * d + a) d (n + 1) =
      apSumFrom f (m * d + a) d n + f ((m + n + 1) * d + a) := by
  simpa using
    (apSumFrom_tail_succ_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: split off the *last* term of an affine tail sum, using the translation-friendly
`(n+1)*d + a` convention.

This exercises `apSumFrom_tail_succ_length_add_left`.
-/
example :
    apSumFrom f a d (n + 1) = apSumFrom f a d n + f ((n + 1) * d + a) := by
  simpa using
    (apSumFrom_tail_succ_length_add_left (f := f) (a := a) (d := d) (m := 0) (n := n))

/-- Regression: split off the *last* term of an affine tail sum, with the affine start written as
`m*d + a`, using the translation-friendly `(m+n+1)*d + a` convention.

This exercises `apSumFrom_tail_succ_length_start_add_left`.
-/
example :
    apSumFrom f (m * d + a) d (n + 1) =
      apSumFrom f (m * d + a) d n + f ((m + n + 1) * d + a) := by
  simpa using
    (apSumFrom_tail_succ_length_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: paper-notation affine tails normalize directly into the offset-sum nucleus API,
using the translation-friendly `i*d + a` summand convention.

This exercises `sum_Icc_eq_apSumOffset_shift_add_add`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using (sum_Icc_eq_apSumOffset_shift_add_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: inverse orientation of `sum_Icc_eq_apSumOffset_shift_add_add`.

This exercises `apSumOffset_shift_add_eq_sum_Icc_add`.
-/
example :
    apSumOffset (fun k => f (k + a)) d m n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) := by
  simpa using
    (apSumOffset_shift_add_eq_sum_Icc_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: mul-left variant of `apSumOffset_shift_add_eq_sum_Icc_add`, avoiding `i*d`.

This exercises `apSumOffset_shift_add_eq_sum_Icc_mul_left_add`.
-/
example :
    apSumOffset (fun k => f (k + a)) d m n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) := by
  simpa using
    (apSumOffset_shift_add_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: inequality-endpoint companion of the previous paper → nucleus normalization.

This exercises `sum_Icc_eq_apSumOffset_shift_add_of_le_add`.
-/
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d + a)) =
      apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    (sum_Icc_eq_apSumOffset_shift_add_of_le_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn))

/-- Regression: mul-left variant of `sum_Icc_eq_apSumOffset_shift_add_of_le_add`, avoiding `i*d`.

This exercises `sum_Icc_eq_apSumOffset_shift_add_of_le_mul_left_add`.
-/
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i + a)) =
      apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    (sum_Icc_eq_apSumOffset_shift_add_of_le_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn))

/-- Regression: add-left start variant of `apSumFrom_tail_eq_apSumOffset_shift_add`.

This exercises `apSumFrom_tail_eq_apSumOffset_shift_add_left`.
-/
example :
    apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: head+tail normal form for affine tails, with the affine start written as `m*d + a`.

This exercises `apSumFrom_tail_succ_length_eq_add_apSumOffset_shift_add_start_add_left`.
-/
example :
    apSumFrom f (m * d + a) d (n + 1) =
      f ((m + 1) * d + a) + apSumOffset (fun k => f (k + a)) d (m + 1) n := by
  simpa using
    (apSumFrom_tail_succ_length_eq_add_apSumOffset_shift_add_start_add_left
      (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: the `m = 0` inverse direction of the previous normalization (offset sum on a shifted
sequence ↦ affine sum).

This exercises `apSumOffset_shift_add_eq_apSumFrom`.
-/
example : apSumOffset (fun k => f (k + a)) d 0 n = apSumFrom f a d n := by
  simpa using (apSumOffset_shift_add_eq_apSumFrom (f := f) (a := a) (d := d) (n := n))

/-- Regression: inverse normal form for *general* offset sums on a shifted sequence.

This exercises `apSumOffset_shift_add_eq_apSumFrom_tail`.
-/
example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (a + m * d) d n := by
  simpa using
    (apSumOffset_shift_add_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: `m*d + a` wrapper of the previous inverse normal form.

This exercises `apSumOffset_shift_add_eq_apSumFrom_tail_left`.
-/
example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using
    (apSumOffset_shift_add_eq_apSumFrom_tail_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: mul-left variant of the previous normal form (affine start written as `a + d*m`).

This exercises `apSumFrom_tail_eq_apSumOffset_shift_add_mul_left`.
-/
example :
    apSumFrom f (a + d * m) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add_mul_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: split an affine tail by length, with the second part normalized as an offset sum on
`k ↦ f (k + a)`.

This exercises `apSumFrom_tail_add_length_eq_add_apSumOffset_shift_add`.
-/
example (n₁ n₂ : ℕ) :
    apSumFrom f (a + m * d) d (n₁ + n₂) =
      apSumFrom f (a + m * d) d n₁ + apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    (apSumFrom_tail_add_length_eq_add_apSumOffset_shift_add
      (f := f) (a := a) (d := d) (m := m) (n1 := n₁) (n2 := n₂))

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

/-- Regression: split an affine AP sum by length and eliminate the offset parameter by absorbing it
into the translation constant.

This exercises `apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m`.
-/
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    (apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m)
      (n := n))

/-- Regression: `m*d + a` variant of the previous normal form.

This exercises `apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m_left`.
-/
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSumOffset (fun k => f (k + (m * d + a))) d 0 n := by
  simpa using
    (apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m_left (f := f) (a := a) (d := d)
      (m := m) (n := n))

/-- Regression: canonical affine difference normal form, with the offset parameter eliminated.

This exercises `apSumFrom_sub_eq_apSumOffset_shift_add_zero_m`.
-/
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    (apSumFrom_sub_eq_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: `m*d + a` variant of the previous canonical affine difference normal form.

This exercises `apSumFrom_sub_eq_apSumOffset_shift_add_zero_m_left`.
-/
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + (m * d + a))) d 0 n := by
  simpa using
    (apSumFrom_sub_eq_apSumOffset_shift_add_zero_m_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: canonical difference of offset sums normalizes to an `m = 0` offset sum on a shifted
sequence.

This exercises `apSumOffset_sub_eq_apSumOffset_shift_add`.
-/
example (n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  simpa using
    (apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Regression: mul-left variant of the previous normal form, with the translation constant written
as `d * (m + n₁)`.

This exercises `apSumOffset_sub_eq_apSumOffset_shift_add_mul_left`.
-/
example (n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + d * (m + n₁))) d 0 n₂ := by
  simpa using
    (apSumOffset_sub_eq_apSumOffset_shift_add_mul_left (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂))

/-- Regression: mul-left normal form for the inequality version `n₁ ≤ n₂`. -/
example {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + d * (m + n₁))) d 0 (n₂ - n₁) := by
  simpa using
    (apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add_mul_left (f := f) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n₂) (hn := hn))

/-- Regression: mul-left normal form for the inequality version `n₁ ≤ n₂`, into a homogeneous sum. -/
example {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSum (fun k => f (k + d * (m + n₁))) d (n₂ - n₁) := by
  simpa using
    (apSumOffset_sub_apSumOffset_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n₂) (hn := hn))

/-- Regression: “step-one” normalization for offset AP sums, using the translation-friendly
`k * d + const` summand convention.

This exercises `apSumOffset_eq_apSum_step_one_add_left`.
-/
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using
    (apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: tail affine AP sum as a step-one offset sum that *keeps* the tail parameter.

This exercises `apSumFrom_tail_eq_apSumOffset_step_one_add_left`.
-/
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k * d + a)) 1 m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

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

/-! ### Paper ↔ nucleus regression examples (homogeneous)

These are compile-time checks that the basic paper-notation interval sums normalize cleanly
into the nucleus `apSum` API (and back).
-/

/-- Regression: normalize the paper homogeneous AP interval sum into `apSum`.

This exercises `sum_Icc_eq_apSum`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using (sum_Icc_eq_apSum (f := f) (d := d) (n := n))

/-- Regression: translation-friendly `d * i` variant of the previous normalization lemma.

This exercises `sum_Icc_eq_apSum_mul_left`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f (d * i)) = apSum f d n := by
  simpa using (sum_Icc_eq_apSum_mul_left (f := f) (d := d) (n := n))

/-- Regression: rewrite `apSum` back to paper interval-sum notation.

This exercises `apSum_eq_sum_Icc`.
-/
example :
    apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  simpa using (apSum_eq_sum_Icc (f := f) (d := d) (n := n))

/-- Regression: mul-left variant of `apSum_eq_sum_Icc`.

This exercises `apSum_eq_sum_Icc_mul_left`.
-/
example :
    apSum f d n = (Finset.Icc 1 n).sum (fun i => f (d * i)) := by
  simpa using (apSum_eq_sum_Icc_mul_left (f := f) (d := d) (n := n))

/-! ### Paper ↔ nucleus regression examples (homogeneous, `m ≤ n` offset intervals)

These are compile-time checks that the `m ≤ n` paper-notation tail interval sums normalize cleanly
into the nucleus `apSumOffset` API (and back).
-/

variable (m₁ n₁ : ℕ) (hmn₁ : m₁ ≤ n₁)

/-- Regression: `m ≤ n` paper tail interval sum normalizes to `apSumOffset`. 

This exercises `sum_Icc_eq_apSumOffset_of_le`.
-/
example :
    (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (i * d)) = apSumOffset f d m₁ (n₁ - m₁) := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m₁) (n := n₁) hmn₁)

/-- Regression: mul-left variant of the previous normalization lemma.

This exercises `sum_Icc_eq_apSumOffset_of_le_mul_left`.
-/
example :
    (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (d * i)) = apSumOffset f d m₁ (n₁ - m₁) := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m₁) (n := n₁) hmn₁)

/-- Regression: rewrite `apSumOffset` back to paper interval-sum notation.

This exercises `apSumOffset_eq_sum_Icc_of_le`.
-/
example :
    apSumOffset f d m₁ (n₁ - m₁) = (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (i * d)) := by
  simpa using
    (apSumOffset_eq_sum_Icc_of_le (f := f) (d := d) (m := m₁) (n := n₁) hmn₁)

/-- Regression: mul-left variant of the previous rewrite lemma.

This exercises `apSumOffset_eq_sum_Icc_of_le_mul_left`.
-/
example :
    apSumOffset f d m₁ (n₁ - m₁) = (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (d * i)) := by
  simpa using
    (apSumOffset_eq_sum_Icc_of_le_mul_left (f := f) (d := d) (m := m₁) (n := n₁) hmn₁)

/-! ### Paper ↔ nucleus regression examples (affine)

These are compile-time checks that the paper-notation interval sums for affine APs normalize
cleanly into the nucleus `apSumFrom` API (and back).
-/

/-- Regression: normalize the paper affine AP interval sum into `apSumFrom`.

This exercises `sum_Icc_eq_apSumFrom`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using (sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n))

/-- Regression: translation-friendly `i*d + a` variant of the previous normalization lemma.

This exercises `sum_Icc_eq_apSumFrom_add`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSumFrom f a d n := by
  simpa using (sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n))

/-- Regression: mul-left variant of the previous normalization lemma.

This exercises `sum_Icc_eq_apSumFrom_mul_left`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f (a + d * i)) = apSumFrom f a d n := by
  simpa using (sum_Icc_eq_apSumFrom_mul_left (f := f) (a := a) (d := d) (n := n))

/-- Regression: rewrite `apSumFrom` back to paper interval-sum notation.

This exercises `apSumFrom_eq_sum_Icc`.
-/
example :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
  simpa using (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n))

/-- Regression: normalize the paper affine *difference* interval sum into a difference of nucleus
`apSumFrom` partial sums.

This exercises `sum_Icc_eq_apSumFrom_sub`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using
    (sum_Icc_eq_apSumFrom_sub (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: `m ≤ n` variant of paper affine difference normalization.

This exercises `sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le`.
-/
example :
    (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (a + i * d)) =
      apSumFrom f a d n₁ - apSumFrom f a d m₁ := by
  simpa using
    (sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le (f := f) (a := a) (d := d) (m := m₁) (n := n₁) hmn₁)

/-- Regression: translation-friendly `i*d + a` variant of the `m ≤ n` paper affine difference normalization.

This exercises `sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le_add`.
-/
example :
    (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (i * d + a)) =
      apSumFrom f a d n₁ - apSumFrom f a d m₁ := by
  simpa using
    (sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le_add (f := f) (a := a) (d := d) (m := m₁) (n := n₁) hmn₁)

/-- Regression: mul-left `a + d*i` variant of the `m ≤ n` paper affine difference normalization.

This exercises `sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le_mul_left`.
-/
example :
    (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (a + d * i)) =
      apSumFrom f a d n₁ - apSumFrom f a d m₁ := by
  simpa using
    (sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le_mul_left (f := f) (a := a) (d := d) (m := m₁)
      (n := n₁) hmn₁)

/-- Regression: mul-left + translation-friendly `d*i + a` variant of the `m ≤ n` paper affine
 difference normalization.

This exercises `sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le_mul_left_add`.
-/
example :
    (Finset.Icc (m₁ + 1) n₁).sum (fun i => f (d * i + a)) =
      apSumFrom f a d n₁ - apSumFrom f a d m₁ := by
  simpa using
    (sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le_mul_left_add (f := f) (a := a) (d := d) (m := m₁)
      (n := n₁) hmn₁)

/-- Regression: normalize a paper affine-tail interval sum directly into an offset sum on the
shifted sequence `k ↦ f (a + k)`.

This exercises `sum_Icc_eq_apSumOffset_shift`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (sum_Icc_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: mul-left variant of the previous normalization lemma.

This exercises `sum_Icc_eq_apSumOffset_shift_mul_left`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + d * i)) = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (sum_Icc_eq_apSumOffset_shift_mul_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: translation-friendly `i*d + a` variant of the affine-tail normalization.

This exercises `sum_Icc_eq_apSumOffset_shift_add_add`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (sum_Icc_eq_apSumOffset_shift_add_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: mul-left + translation-friendly `d*i + a` variant of the affine-tail normalization.

This exercises `sum_Icc_eq_apSumOffset_shift_add_mul_left_add`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (sum_Icc_eq_apSumOffset_shift_add_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: inverse orientation of `apSumOffset_shift_add_eq_apSum_shift_add`.

This exercises `apSum_shift_add_eq_apSumOffset_shift_add`.
-/
example :
    apSum (fun k => f (k + (a + m * d))) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    (apSum_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: eliminate an explicit offset parameter in a shifted-sequence offset sum.

This exercises `apSumOffset_shift_add_eq_apSumOffset_shift_add`.
-/
example :
    apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    (apSumOffset_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Regression: add-left variant of the previous normal form.

This exercises `apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left`.
-/
example :
    apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f ((a + m * d) + k)) d 0 n := by
  simpa using
    (apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n))

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

/-! ### Degenerate normal form regression examples

These are tiny compile-time checks for common “degenerate” simp normal forms.
-/

/-- Regression: rewrite the `m = 0` offset sum back to the homogeneous sum.

This exercises `apSumOffset_zero_m`.
-/
example : apSumOffset f d 0 n = apSum f d n := by
  simpa using (apSumOffset_zero_m (f := f) (d := d) (n := n))

/-- Regression: simplify a homogeneous AP sum when the step size is zero.

This exercises `apSum_zero_d`.
-/
example : apSum f 0 n = n • f 0 := by
  simpa using (apSum_zero_d (f := f) (n := n))

/-- Regression: simplify an offset AP sum when the step size is zero.

This exercises `apSumOffset_zero_d`.
-/
example : apSumOffset f 0 m n = n • f 0 := by
  simpa using (apSumOffset_zero_d (f := f) (m := m) (n := n))

/-- Regression: an affine AP sum starting at `a = 0` is just a homogeneous AP sum.

This exercises `apSumFrom_zero_a`.
-/
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using (apSumFrom_zero_a (f := f) (d := d) (n := n))

/-- Regression: an affine AP sum with step size `d = 0` collapses to repeated evaluation at the start.

This exercises `apSumFrom_zero_d`.
-/
example : apSumFrom f a 0 n = n • f a := by
  simpa using (apSumFrom_zero_d (f := f) (a := a) (n := n))

/-- Regression: inverse orientation of `apSumFrom_zero_a`.

This exercises `apSum_eq_apSumFrom`.
-/
example : apSum f d n = apSumFrom f 0 d n := by
  simpa using (apSum_eq_apSumFrom (f := f) (d := d) (n := n))

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

/-- Regression: mul-left + translation-friendly variant of the previous normalization lemma.

This exercises `sum_Icc_eq_apSumFrom_tail_mul_left_add`.
-/
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) = apSumFrom f (a + m * d) d n := by
  simpa using
    (sum_Icc_eq_apSumFrom_tail_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n))

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

/-! ### Length-indexed offset-sum regression examples

These exercise the “fixed lower endpoint” normal forms for `apSumOffset`.
-/

/-- Regression: rewrite an offset sum to the length-indexed paper form using the translation-friendly
`i*d + m*d` summand convention.

This exercises `apSumOffset_eq_sum_Icc_length_add`.
-/
example :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (i * d + m * d)) := by
  simpa using (apSumOffset_eq_sum_Icc_length_add (f := f) (d := d) (m := m) (n := n))

/-- Regression: rewrite an offset sum to the length-indexed paper form using the translation-friendly
`m*d + i*d` summand convention.

This exercises `apSumOffset_eq_sum_Icc_length_add_left`.
-/
example :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (m * d + i * d)) := by
  simpa using (apSumOffset_eq_sum_Icc_length_add_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: mul-left + translation-friendly length-indexed paper form for offset sums.

This exercises `apSumOffset_eq_sum_Icc_length_mul_left_add`.
-/
example :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * i + d * m)) := by
  simpa using (apSumOffset_eq_sum_Icc_length_mul_left_add (f := f) (d := d) (m := m) (n := n))

/-- Regression: mul-left + translation-friendly length-indexed paper form for offset sums, with the
constant written on the left (`d*m + d*i`).

This exercises `apSumOffset_eq_sum_Icc_length_mul_left_add_left`.
-/
example :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * m + d * i)) := by
  simpa using
    (apSumOffset_eq_sum_Icc_length_mul_left_add_left (f := f) (d := d) (m := m) (n := n))

/-- Regression: inverse orientation of `apSumOffset_eq_sum_Icc_length_mul_left_add_left`.

This exercises `sum_Icc_eq_apSumOffset_length_mul_left_add_left`.
-/
example :
    (Finset.Icc 1 n).sum (fun i => f (d * m + d * i)) = apSumOffset f d m n := by
  simpa using
    (sum_Icc_eq_apSumOffset_length_mul_left_add_left (f := f) (d := d) (m := m) (n := n))

end NormalFormExamples

end MoltResearch
