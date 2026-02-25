import MoltResearch.Discrepancy

/-!
# Discrepancy normal-form regression examples

This module is a standalone compilation test-bed for the preferred “normal form” rewrite pipelines.

It intentionally imports only the **stable surface** `MoltResearch.Discrepancy`.
Downstream developments should not need to import this file.
-/

namespace MoltResearch

section NormalFormExamples

variable (f : ℕ → ℤ) (a d m n n₁ n₂ : ℕ)

example : apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  simpa using apSum_eq_sum_Icc (f := f) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using sum_Icc_eq_apSum (f := f) (d := d) (n := n)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example : apSum f d n = (Finset.Icc 1 n).sum (fun i => f (d * i)) := by
  simpa using apSum_eq_sum_Icc_mul_left (f := f) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (d * i)) = apSum f d n := by
  simpa using sum_Icc_eq_apSum_mul_left (f := f) (d := d) (n := n)

example : apSum f 1 n = (Finset.Icc 1 n).sum f := by
  simpa using apSum_one_d (f := f) (n := n)

-- Affine tails as offset sums (both summand conventions).

example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normal form, but with the affine start written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Switching between `a + k` and `k + a` inside the shifted-sequence view of `apSumOffset`.
example : apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumOffset_shift_comm (f := f) (a := a) (d := d) (m := m) (n := n)

-- Commuting `a + k` ↔ `k + a` under the nucleus sums.
--
-- These are small but useful “normalization” steps when you want a translation-friendly `k + const`
-- summand shape without doing a manual `funext` rewrite.
example : apSum (fun k => f (a + k)) d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSum_shift_comm (f := f) (a := a) (d := d) (n := n)

example : apSumFrom (fun x => f (a + x)) m d n = apSumFrom (fun x => f (x + a)) m d n := by
  simpa using apSumFrom_shift_comm (f := f) (a := a) (k := m) (d := d) (n := n)

-- “Push the translation into the function” normal forms.
--
-- These are mathematically the same as the `…_shift` / `…_shift_add` family, but the `map_add`
-- naming makes it easier to spot (in a proof script) that the translation has been packaged into
-- the function itself.
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSumFrom_eq_apSum_map_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun x => f (a + x)) d n := by
  simpa using apSumFrom_eq_apSum_map_add_left (f := f) (a := a) (d := d) (n := n)

-- Differences → tails (canonical normal form).

example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

-- If you prefer the canonical offset-sum normal form on the shifted sequence `k ↦ f (k + a)`,
-- rewrite the same difference directly to `apSumOffset`.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + a)) d m n := by
  -- Two-step “difference → affine tail → offset on a shifted sequence” normal form.
  --
  -- This is a regression test for the Track B glue lemma
  -- apSumFrom_sub_eq_apSumOffset_shift_add: even if that lemma gets refactored,
  -- we want this common rewrite pipeline to keep working from the stable import
  -- surface `import MoltResearch.Discrepancy`.
  calc
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
      simpa using
        apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k + a)) d m n := by
      simpa using
        apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Tail-of-tail differences → offset-sum tails (and the `m = 0` shifted-sequence normal form).
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + (a + (m + n₁) * d))) d 0 n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_zero_m_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Degenerate constant APs.
example : apSum f 0 n = n • f 0 := by
  simp

example : apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  simpa using apSum_eq_apSum_step_one (f := f) (d := d) (n := n)

example : apSum (fun k => f (k * d)) 1 n = apSum f d n := by
  simpa using apSum_step_one_eq_apSum (f := f) (d := d) (n := n)

-- Offset/tail normal forms.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Same difference normal form, but eliminate the explicit offset sum into a homogeneous AP sum
-- on a shifted sequence.
example : apSum f d (m + n) - apSum f d m = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSum_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Length-splitting normal forms for `apSumOffset`.
example : apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example :
    apSumOffset f d m (n₁ + n₂) =
      apSumOffset f d m n₁ + apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
  simpa using
    apSumOffset_add_length_eq_add_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d 0 n = apSum f d n := by
  simp

example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_a (f := f) (d := d) (n := n)

example : apSum f d n = apSumFrom f 0 d n := by
  simpa using apSum_eq_apSumFrom (f := f) (d := d) (n := n)

-- Offset sums: shifted-sequence normal forms (translation-friendly `k + const`).
example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Same normal form, but write the translation constant as `d*m` (mul-left convention).
example : apSumOffset f d m n = apSum (fun k => f (k + d * m)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m) (n := n)

-- Differences of offset sums: mul-left translation constant variant.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSum (fun k => f (k + d * (m + n₁))) d n₂ := by
  simpa using
    apSumOffset_sub_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d m n = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  simpa using apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n)

-- Same normal form, but write the translation constant as `d*m` (mul-left convention).
example : apSumOffset f d m n = apSumOffset (fun k => f (k + d * m)) d 0 n := by
  simpa using
    apSumOffset_eq_apSumOffset_shift_add_mul_left (f := f) (d := d) (m := m) (n := n)

-- Paper normal form: rewrite `Icc (m+1) (m+n)` tails to the fixed-lower-endpoint `Icc 1 n` form.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) =
      (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using sum_Icc_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * i` variant.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) =
      (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using sum_Icc_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)

-- Offset paper notation: multiplication-on-the-left variants (avoid commuting `i*d` under binders).
example : apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)

example : (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n)

-- Offset sums on a shifted sequence: return to the affine-tail nucleus API.
example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (a + m * d) d n := by
  simpa using apSumOffset_shift_add_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m)
    (n := n)

example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using apSumOffset_shift_add_eq_apSumFrom_tail_left (f := f) (a := a) (d := d) (m := m)
    (n := n)

-- Affine sums: shift-add normal form (translation-friendly `k + a`).
example : apSumFrom f a d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

-- Same affine sum, but with the translation “pushed into the function” form `x ↦ f (x + a)`.
-- This is handy when you want to reuse translation lemmas stated for homogeneous `apSum`.
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSumFrom_eq_apSum_map_add (f := f) (a := a) (d := d) (n := n)

-- Affine paper notation: multiplication-on-the-left variants (avoid commuting `i*d` under binders).
example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + d * i)) := by
  simpa using apSumFrom_eq_sum_Icc_mul_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (d * i + a)) := by
  simpa using apSumFrom_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (n := n)

-- Affine differences: normalize to an offset sum on a shifted sequence.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same difference normal form, but eliminate the tail parameter into a homogeneous AP sum.
-- Writing the translation constant as `m*d + a` avoids a commutativity rewrite.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    apSumFrom_sub_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Difference → tail, then absorb the tail offset into the translation constant so the offset is `0`.
-- This is often a good “don’t carry extra parameters” normal form before bounding/splitting.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m) (n := n)

-- Translation-friendly affine “step-one” normal forms.
example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f (a + m * d) d n = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
  simpa using
    apSumFrom_tail_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same tail step-one normal form, but with the affine start already written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSum (fun k => f (k * d + (m * d + a))) 1 n := by
  simpa using
    apSumFrom_tail_eq_apSum_step_one_add_left_start_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Regression: tail head+tail normal form (translation-friendly add-left form).
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f ((m + 1) * d + a) + apSumFrom f ((m + 1) * d + a) d n := by
  simpa using
    apSumFrom_tail_succ_length_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Regression: tail append-one-term normal form (translation-friendly add-left form).
example :
    apSumFrom f (a + m * d) d (n + 1) = apSumFrom f (a + m * d) d n + f ((m + n + 1) * d + a) := by
  simpa using
    apSumFrom_tail_succ_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Regression: tail normal forms when the affine start is already written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f (m * d + a) d n = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    apSumFrom_tail_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (m * d + a) d (n + 1) =
      f ((m + 1) * d + a) + apSumFrom f ((m + 1) * d + a) d n := by
  simpa using
    apSumFrom_tail_succ_length_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (m * d + a) d (n + 1) = apSumFrom f (m * d + a) d n + f ((m + n + 1) * d + a) := by
  simpa using
    apSumFrom_tail_succ_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Step-one normalization that stays inside the offset nucleus API (`m = 0`) in the
-- translation-friendly `k*d + const` presentation.
example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k * d + (a + m * d))) 1 0 n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Same step-one offset-sum normal form, but with the affine start already written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k * d + (m * d + a))) 1 0 n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left_start_add_left (f := f) (a := a) (d := d)
      (m := m) (n := n)

-- Step-one normalization that keeps the offset parameter `m`, with the summand written as
-- `a + k*d`.
example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k * d)) 1 m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (m := m) (n := n)

-- Offset ↔ affine normal forms.
example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Same offset normal form, but with the affine start written as `d*m` (avoids a commutativity
-- rewrite in downstream goals).
example : apSumFrom f (d * m) d n = apSumOffset f d m n := by
  simpa using apSumFrom_mul_left_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Step-one normalization that stays inside the affine nucleus API.
example : apSumFrom f a d n = apSumFrom (fun k => f (a + k * d)) 0 1 n := by
  simpa using apSumFrom_eq_apSumFrom_step_one (f := f) (a := a) (d := d) (n := n)

-- Differences of partial sums: normalize to tails early.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- If you want the *fixed lower endpoint* paper normal form (useful for splitting by length),
-- rewrite the same difference directly to an `Icc 1 n` interval sum.
example : apSum f d (m + n) - apSum f d m = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using apSum_sub_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)

-- Same paper normal form, but in the translation-friendly `d * (m+i)` binder convention.
example : apSum f d (m + n) - apSum f d m = (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using apSum_sub_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)

-- And you can normalize back into the nucleus API without carrying a variable upper endpoint.
example : (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_length (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using
    apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

-- Offset sums: additional normal forms that tend to compose well.
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Eliminate an offset parameter `m` by absorbing it into a translation constant.
example :
    apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumOffset_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Affine tails/differences as offset sums on a shifted sequence (translation-friendly `k + a`).
example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Split affine tails by length, with the second block expressed as an `apSumOffset` on the
-- shifted sequence `k ↦ f (k + a)`.
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) =
      apSumFrom f (a + m * d) d n₁ + apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_add_length_eq_add_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Same normal form, but keep the shifted sequence in the `a + k` shape.
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) =
      apSumFrom f (a + m * d) d n₁ + apSumOffset (fun k => f (a + k)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_add_length_eq_add_apSumOffset_shift (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Further normalize affine tails by absorbing `m` into the translation constant (so the offset is `0`).
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normalization, but eliminate the now-trivial offset sum (`m = 0`) into a homogeneous AP sum.
example :
    apSumFrom f (a + m * d) d n = apSum (fun k => f (k + (a + m * d))) d n := by
  simpa using
    apSumFrom_tail_eq_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same idea, but for the standard `m+n` splitting normal form.
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Same splitting normal form, but eliminate the now-trivial offset sum (`m = 0`) into a
-- homogeneous AP sum on a shifted sequence.
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSum (fun k => f (k + (a + m * d))) d n := by
  simpa using
    apSumFrom_add_length_eq_add_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same, with the translation constant written as `m*d + a` (often avoids commutativity rewrites).
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSum (fun k => f (k + (m * d + a))) d n := by
  -- `AffineTail` has the main lemma in the `(a + m*d)` presentation; this wrapper just
  -- reassociates/commutes the translation constant.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumFrom_add_length_eq_add_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

-- Same normal form, but with the affine start written as `m*d + a` (avoids a commutativity rewrite).
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normalization, but eliminate the tail parameter entirely into a homogeneous AP sum.
example : apSumFrom f (m * d + a) d n = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    apSumFrom_tail_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- If you prefer to keep the shifted summand in the `a + k` form, use the corresponding wrappers.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (a + k)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using
    apSumOffset_shift_eq_apSumFrom_tail_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k + a)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (n := n)

-- If you have already shifted the summand `k ↦ f (k + a)`, normalize back to the canonical
-- `apSumFrom f a d n` form.
example : apSumFrom (fun k => f (k + a)) 0 d n = apSumFrom f a d n := by
  simpa using apSumFrom_shift_add_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

-- Same normal form, but with the shifted summand written as `a + k` (avoids a commutativity rewrite
-- under binders).
example : apSumFrom f a d n = apSumFrom (fun k => f (a + k)) 0 d n := by
  simpa using apSumFrom_eq_apSumFrom_shift_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom (fun k => f (a + k)) 0 d n = apSumFrom f a d n := by
  simpa using apSumFrom_shift_add_left_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

-- Translation (additive reindexing) normal forms.
-- These are lightweight but practical: they let you commute a shift through the nucleus APIs
-- without needing to unfold `apSumFrom` and fight `Nat.add_*` under binders.

-- Commute a translation in the binder convention for `apSum` (normal-form helper).
example : apSum (fun x => f (a + x)) d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSum_shift_comm (f := f) (a := a) (d := d) (n := n)

-- Same commutation normal form, but inside `apSumOffset`.
example : apSumOffset (fun x => f (a + x)) d m n = apSumOffset (fun x => f (x + a)) d m n := by
  simpa using apSumOffset_shift_comm (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same commutation normal form, but inside `apSumFrom`.
example : apSumFrom (fun x => f (a + x)) m d n = apSumFrom (fun x => f (x + a)) m d n := by
  simpa using apSumFrom_shift_comm (f := f) (a := a) (k := m) (d := d) (n := n)

example : apSumFrom (fun x => f (x + m)) a d n = apSumFrom f (a + m) d n := by
  simpa using apSumFrom_map_add (f := f) (k := m) (a := a) (d := d) (n := n)

example : apSumFrom (fun x => f (m + x)) a d n = apSumFrom f (m + a) d n := by
  simpa using apSumFrom_map_add_left (f := f) (k := m) (a := a) (d := d) (n := n)

-- Translation under the homogeneous nucleus API.
example : apSum (fun x => f (x + a)) d n = apSumFrom f a d n := by
  simpa using apSum_map_add (f := f) (k := a) (d := d) (n := n)

example : apSum (fun x => f (a + x)) d n = apSumFrom f a d n := by
  simpa using apSum_map_add_left (f := f) (k := a) (d := d) (n := n)

-- Translation under the offset nucleus API.
example : apSumOffset (fun x => f (x + a)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using apSumOffset_map_add (f := f) (k := a) (d := d) (m := m) (n := n)

-- Inverse orientation: normalize an affine tail with start `m*d + a` back into an offset sum
-- on a shifted sequence.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun x => f (x + a)) d m n := by
  simpa using apSumFrom_start_add_left_eq_apSumOffset_map_add (f := f) (k := a) (d := d) (m := m)
    (n := n)

example : apSumOffset (fun x => f (a + x)) d m n = apSumFrom f (a + m * d) d n := by
  simpa using apSumOffset_map_add_left (f := f) (k := a) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Step-one normal form: package the step size `d` into the summand.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
  simpa using
    apSumFrom_sub_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Inequality normal form: subtracting two affine partial sums as a tail sum.
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSumFrom f (a + m * d) d (n - m) := by
  simpa using apSumFrom_sub_apSumFrom_eq_apSumFrom (f := f) (a := a) (d := d) (m := m) (n := n)
    hmn

-- Paper-notation fixed-length tail → nucleus offset normal form: rewrite
-- `∑ i ∈ Icc (m+1) (m+n), f (i*d + a)` directly to an `apSumOffset` on the shifted sequence.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Mul-left + translation-friendly variant: `f (d*i + a)`.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Paper-notation inequality normal form: `Icc (m+1) n` tails for affine sums.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d + a)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

-- Mul-left variants: `d * i` binder form.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + d * i)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_mul_left (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i + a)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example : apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  simpa using apSum_succ (f := f) (d := d) (n := n)

example : apSum f d (n + 1) = f d + apSumOffset f d 1 n := by
  simpa using apSum_succ_length (f := f) (d := d) (n := n)

example : apSumOffset f d 0 n = apSum f d n := by
  simp

example : apSumOffset f d m 0 = 0 := by
  simp

-- Single-term normal forms (useful when you want to peel a tail down to one summand).
example : apSumOffset f d m 1 = f ((m + 1) * d) := by
  simpa using apSumOffset_one (f := f) (d := d) (m := m)

example : apSumFrom f a d 1 = f (a + d) := by
  -- `apSumFrom` is the affine AP sum over `a + d, a + 2d, ...`.
  simpa using apSumFrom_one (f := f) (a := a) (d := d)

-- Degenerate constant AP tails.
example : apSumOffset f 0 m n = n • f 0 := by
  simp

example : apSumOffset f d m (n + 1) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  simpa using apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  simpa using apSumOffset_succ (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  simpa using apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)

-- Canonical “difference of partial sums” normal form: rewrite subtraction into a tail.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)).symm

-- Variable upper endpoints often appear in surface statements. When `m ≤ n`, normalize
-- `∑ i ∈ Icc (m+1) n, ...` into the canonical tail length `n - m`.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc_of_le (f := f) (d := d) (m := m) (n := n) hmn

-- Translation-friendly `d * i` variants (avoid commuting multiplication under binders).
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
  simpa using apSumOffset_eq_sum_Icc_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn

-- If you want to eliminate `apSumOffset` entirely, normalize paper tails directly into an
-- `apSum` on a shifted sequence.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum (fun k => f (k + m * d)) d (n - m) := by
  simpa using sum_Icc_eq_apSum_shift_add_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSum (fun k => f (k + m * d)) d (n - m) := by
  simpa using sum_Icc_eq_apSum_shift_add_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn

-- Same difference normal form, but rewrite the tail into a homogeneous AP sum on a shifted sequence.
example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSum (fun k => f (k + m * d)) d (n - m) := by
  simpa using apSum_sub_apSum_eq_apSum_shift_add_of_le (f := f) (d := d) (m := m) (n := n) hmn

-- Same difference normal form, but eliminate the offset parameter by shifting the underlying
-- sequence so the offset is `0`.
example (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSumOffset (fun k => f (k + m * d)) d 0 (n - m) := by
  simpa using
    apSum_sub_apSum_eq_apSumOffset_shift_add_of_le (f := f) (d := d) (m := m) (n := n) hmn

example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
  simpa using apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (k * d)) 1 m n = apSumOffset f d m n := by
  simpa using apSumOffset_step_one_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)

-- Multiplication-on-the-left variant (avoids commuting `(_ * d)` under binders).
example : apSumOffset f d m n = apSum (fun k => f (d * (m + k))) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one_mul_left (f := f) (d := d) (m := m) (n := n)

-- Multiplication-on-the-left + translation-friendly variant: `k ↦ f (d*k + d*m)`.
example : apSumOffset f d m n = apSum (fun k => f (d * k + d * m)) 1 n := by
  simpa using
    apSumOffset_eq_apSum_step_one_mul_left_add_left (f := f) (d := d) (m := m) (n := n)

example : apSum (fun k => f ((m + k) * d)) 1 n = apSumOffset f d m n := by
  simpa using apSum_step_one_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- A translation-friendly variant of the step-one form: `k ↦ f (k*d + m*d)`.
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
  simpa using apSumOffset_eq_apSumOffset_step_one_zero_m (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  simpa using
    apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n)

-- Multiplication-on-the-left, translation-friendly step-one normal form that stays inside the
-- offset nucleus API (`m = 0`).
example : apSumOffset f d m n = apSumOffset (fun k => f (d * k + d * m)) 1 0 n := by
  simpa using
    apSumOffset_eq_apSumOffset_step_one_zero_m_mul_left_add_left (f := f) (d := d) (m := m)
      (n := n)

example : apSumOffset f d m n = apSum (fun k => f (m * d + k)) d n := by
  simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- A convenient normal form: eliminate the explicit offset parameter by shifting the underlying
-- sequence and resetting the offset to `0`.
example : apSumOffset f d m n = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  simpa using apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (k + m * d)) d 0 n = apSumOffset f d m n := by
  simpa using apSumOffset_shift_add_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Splitting a paper-notation tail sum into consecutive blocks matches the nucleus split lemma.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    sum_Icc_add_length_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Paper difference normal form: subtracting the first block leaves the tail block.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Paper difference → nucleus normal form: convert directly to an `apSumOffset` tail.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
      apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
      apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Variable upper endpoints often appear in surface statements. When `m ≤ k ≤ n`, split the
-- interval sum at `k`. 
example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (i * d)) +
        (Finset.Icc (k + 1) n).sum (fun i => f (i * d)) := by
  simpa using sum_Icc_split_of_le (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (d * i)) +
        (Finset.Icc (k + 1) n).sum (fun i => f (d * i)) := by
  simpa using
    sum_Icc_split_of_le_mul_left (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

-- Nucleus counterpart: when `m ≤ k ≤ n`, split the tail `apSumOffset f d m (n - m)` at `k`.
example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    apSumOffset f d m (n - m) =
      apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
  simpa using
    apSumOffset_eq_add_apSumOffset_of_le (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

-- Affine paper splitting: mul-left form `a + d*i`.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (a + d * i)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + d * i)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (a + d * i)) := by
  simpa using
    sum_Icc_add_length_affine_mul_left (f := f) (a := a) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Affine paper splitting: mul-left + translation-friendly form `d*i + a`.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i + a)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i + a)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i + a)) := by
  simpa using
    sum_Icc_add_length_affine_mul_left_add (f := f) (a := a) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂)

-- Normal form: a later tail as a difference of a longer tail and its initial segment.
example :
    apSumOffset f d (m + n₁) n₂ = apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ := by
  simpa using apSumOffset_tail_eq_sub (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Normal form: difference of offset sums with the same `m` becomes a later tail.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Same difference normal form, but eliminate the tail offset parameter by shifting the underlying
-- sequence and resetting the offset to `0`.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  simpa using
    apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Same difference normal form, but eliminate the explicit `apSumOffset` into an `apSum` on a
-- shifted sequence.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
  simpa using apSumOffset_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Same inequality normal form, but eliminate the offset parameter by shifting the underlying
-- sequence and resetting the offset to `0`.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Same inequality normal form, but eliminate the explicit `apSumOffset` into an `apSum` on a
-- shifted sequence.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSum (fun k => f (k + (m + n₁) * d)) d (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Splitting a longer tail into an initial segment plus a (normalized) later tail.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_eq_add_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)

example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (i * d)) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)

-- Translation-friendly `d * i` variants (avoid commuting multiplication under binders).
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    apSumOffset_sub_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using apSum_sub_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)

-- Fixed-lower-endpoint (“length-indexed”) paper notation.
example : apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_length (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * (m+i)` variant.
example : apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using apSumOffset_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_length_mul_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f 1 m n = (Finset.Icc (m + 1) (m + n)).sum f := by
  simpa using apSumOffset_one_d (f := f) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSum f d (m + n) - apSum f d m := by
  simpa using sum_Icc_eq_apSum_sub (f := f) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum f d n - apSum f d m := by
  simpa using sum_Icc_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = apSum f d n - apSum f d m := by
  simpa using apSumOffset_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_apSum_eq_sum_Icc (f := f) (d := d) (m := m) (n := n) hmn

example :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)

-- Translation-friendly paper notation: avoid commuting `a + …` under binders.
example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (i * d + a)) := by
  simpa using apSumFrom_eq_sum_Icc_add (f := f) (a := a) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n)

-- Affine start `a = 0` recovers the homogeneous AP sum.
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_a (f := f) (d := d) (n := n)

example : apSumFrom f a 1 n = (Finset.Icc 1 n).sum (fun i => f (a + i)) := by
  simpa using apSumFrom_one_d (f := f) (a := a) (n := n)

example : apSumFrom f a d (n + 1) = apSumFrom f a d n + f (a + (n + 1) * d) := by
  simpa using apSumFrom_succ (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d 0 = 0 := by
  simp

example : apSumFrom f a d (n + 1) = f (a + d) + apSumFrom f (a + d) d n := by
  simpa using apSumFrom_succ_length (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (n₁ + n₂) = apSumFrom f a d n₁ + apSumFrom f (a + n₁ * d) d n₂ := by
  simpa using apSumFrom_add_length (f := f) (a := a) (d := d) (m := n₁) (n := n₂)

example : apSumFrom f a d (m + n) = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_add_length (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f a 0 n = n • f a := by
  simp

-- Affine sums at `a = 0` are just homogeneous AP sums.
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_a (f := f) (d := d) (n := n)

example : apSum f d n = apSumFrom f 0 d n := by
  simpa using apSum_eq_apSumFrom (f := f) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  simpa using apSumFrom_eq_apSum_shift (f := f) (a := a) (d := d) (n := n)

-- Sometimes you want to package the translation as a map on the sequence `f` itself.
-- These lemmas commute the `+ a` past the multiplication inside the binder.
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSumFrom_eq_apSum_map_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun x => f (a + x)) d n := by
  simpa using apSumFrom_eq_apSum_map_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (a + k * d)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  simpa using
    apSumFrom_eq_apSumOffset_step_one_zero_m (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    apSumFrom_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (n := n)

example : apSum (fun k => f (a + k * d)) 1 n = apSumFrom f a d n := by
  simpa using apSum_step_one_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n)

-- Canonical affine difference `(m+n) - m` as an offset sum on the shifted sequence.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Variable upper endpoints appear in surface statements.
-- When `m ≤ n`, normalize the difference `apSumFrom … n - apSumFrom … m` into the canonical tail
-- length `n - m` (in translation-friendly `k + a` form).
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn)

-- Inverse orientation: normalize an `apSumOffset` tail sum on a shifted sequence back into a
-- difference of affine partial sums.
example (hmn : m ≤ n) :
    apSumOffset (fun k => f (k + a)) d m (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using
    apSumOffset_shift_add_eq_apSumFrom_sub_apSumFrom_of_le (f := f) (a := a) (d := d) (m := m)
      (n := n) (hmn := hmn)

-- Splitting an affine partial sum at an intermediate point, with the tail normalized into the
-- `apSumOffset` API on a shifted sequence.
example (hmn : m ≤ n) :
    apSumFrom f a d n = apSumFrom f a d m + apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    apSumFrom_eq_add_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn)

-- “Paper notation” for affine tails, in the translation-friendly `i*d + a` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same tail paper notation, but in the mul-left `a + d*i` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + d * i)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_mul_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same tail paper notation, in the mul-left + translation-friendly `d*i + a` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) := by
  simpa using
    apSumFrom_tail_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Length-indexed paper notation for affine tails (fixed lower endpoint `1`).
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc 1 n).sum (fun i => f (a + (m + i) * d)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_length (f := f) (a := a) (d := d) (m := m) (n := n)

-- Translation-friendly length-indexed variant, with the summand written as `(m+i)*d + a`.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc 1 n).sum (fun i => f ((m + i) * d + a)) := by
  simpa using
    apSumFrom_tail_eq_sum_Icc_length_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Variable upper endpoints appear often in surface statements.
-- When `m ≤ n`, normalize `∑ i ∈ Icc (m+1) n, f (i*d + a)` into the canonical tail length `n - m`.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d + a)) =
      apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example : apSumFrom f (a + m * d) d n = apSum (fun k => f (a + (m + k) * d)) 1 n := by
  simpa using apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSum (fun k => f (a + (m + k) * d)) 1 n = apSumFrom f (a + m * d) d n := by
  simpa using apSum_step_one_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

-- Head+tail normal form for affine tails: increment the tail parameter `m`.
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f (a + (m + 1) * d) + apSumFrom f (a + (m + 1) * d) d n := by
  simpa using apSumFrom_tail_succ_length (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same head+tail normal form, but with the remaining tail expressed as an `apSumOffset`.
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f (a + (m + 1) * d) + apSumOffset (fun k => f (a + k)) d (m + 1) n := by
  simpa using
    apSumFrom_tail_succ_length_eq_add_apSumOffset_shift (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Translation-friendly variant (`k + a` inside binders, and `(m+1)*d + a` for the head term).
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f ((m + 1) * d + a) + apSumOffset (fun k => f (k + a)) d (m + 1) n := by
  simpa using
    apSumFrom_tail_succ_length_eq_add_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m)
      (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (a + k)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k + a)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (a + m * d) d n = apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d n := by
  simpa using sum_Icc_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ m + n) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (a + i * d)) +
        (Finset.Icc (k + 1) (m + n)).sum (fun i => f (a + i * d)) := by
  simpa using
    (sum_Icc_split_affine_of_le (f := f) (a := a) (d := d) (m := m) (k := k) (n := m + n) hmk hkn)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_sub_eq_sum_Icc (f := f) (a := a) (d := d) (m := m) (n := n)

-- Translation-friendly `d*i + a` surface form (avoid commuting multiplication under binders).
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) := by
  simpa using
    apSumFrom_sub_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) =
      apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using
    sum_Icc_eq_apSumFrom_sub_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using sum_Icc_eq_apSumFrom_sub (f := f) (a := a) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    (sum_Icc_eq_apSumFrom_tail_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn)

example (hmn : m ≤ n) :
    apSumFrom f (a + m * d) d (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_sub_apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using
    sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumFrom f (a + (m + n₁) * d) d n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n1 := n₁)
      (n2 := n₂)

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (a + k)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_tail (f := f) (a := a) (d := d) (m := m) (n1 := n₁)
      (n2 := n₂)

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Further normalize tail-of-tail differences by absorbing the explicit offset into the translation.
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + (a + (m + n₁) * d))) d 0 n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_zero_m_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ (∀ C : ℕ, Nonempty (DiscrepancyWitnessPos f C)) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, Nonempty (AffineDiscrepancyWitnessPos f C)) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  simpa using
    forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  simpa using
    forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ a : ℕ, HasDiscrepancyAtLeast (fun k => f (a + k)) C) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift (f := f)

/-! ### Transform / reindexing regression tests -/

example (k : ℕ) : apSum (fun x => f (x * k)) d n = apSum f (d * k) n := by
  simpa using apSum_map_mul (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSum (fun x => f (x + k)) d n = apSumFrom f k d n := by
  simpa using apSum_map_add (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSum (fun x => f (k + x)) d n = apSumFrom f k d n := by
  simpa using apSum_map_add_left (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSumOffset (fun x => f (x + k)) d m n = apSumFrom f (k + m * d) d n := by
  simpa using apSumOffset_map_add_start_add_left (f := f) (k := k) (d := d) (m := m) (n := n)

example (k : ℕ) : apSumOffset (fun x => f (k + x)) d m n = apSumFrom f (k + m * d) d n := by
  simpa using apSumOffset_map_add_left (f := f) (k := k) (d := d) (m := m) (n := n)

-- Regression: compose a shift-add reindexing with the offset→shift normal form.
example (k : ℕ) :
    apSumOffset (fun x => f (x + k)) d m n = apSum (fun x => f (x + (k + m * d))) d n := by
  simpa using apSumOffset_shift_add_eq_apSum_shift_add (f := f) (a := k) (d := d) (m := m)
    (n := n)

-- Add-left (`k + x`) variant of the same regression.
example (k : ℕ) :
    apSumOffset (fun x => f (k + x)) d m n = apSum (fun x => f ((k + m * d) + x)) d n := by
  simpa using
    apSumOffset_shift_add_left_eq_apSum_shift_add_left (f := f) (a := k) (d := d) (m := m) (n := n)

-- Regression: inverse orientation (rewrite a shifted homogeneous sum back into an offset sum).
example (k : ℕ) :
    apSum (fun x => f (x + (k + m * d))) d n = apSumOffset (fun x => f (x + k)) d m n := by
  simpa using apSum_shift_add_eq_apSumOffset_shift_add (f := f) (a := k) (d := d) (m := m) (n := n)

example (k C : ℕ) (hk : k > 0) :
    HasDiscrepancyAtLeast (fun x => f (x * k)) C → HasDiscrepancyAtLeast f C := by
  intro h
  exact HasDiscrepancyAtLeast.of_map_mul (f := f) (hk := hk) (h := h)

example (k C : ℕ) :
    HasDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C := by
  intro h
  exact HasDiscrepancyAtLeast.of_map_add (f := f) (k := k) (C := C) h

example (c : ℤ) (hc : c ≠ 0) (C : ℕ) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => c * f n) C := by
  intro h
  exact HasDiscrepancyAtLeast.mul_left_of_ne_zero (f := f) (C := C) c hc h



-- A few regression-test examples for the affine/offset “glue” normal forms.
-- These are intentionally small: they protect the stable import surface
-- `import MoltResearch.Discrepancy` against accidental breakage.

variable (a d m n : ℕ)

example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  simpa using apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
end NormalFormExamples

end MoltResearch
