import MoltResearch.Discrepancy

/-!
# Discrepancy: deprecated aliases

This module provides backwards-compatible names that used to be part of the main discrepancy
surface.

The stable surface is:

```lean
import MoltResearch.Discrepancy
```

If you need older names (e.g. `*_map_add` wrappers), import this file explicitly.
-/

namespace MoltResearch

/-- Deprecated name for `IsSignSequence.shift_add`. -/
@[deprecated "Use `IsSignSequence.shift_add`." (since := "2026-02-28")]
lemma IsSignSequence.map_add {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (n + k)) :=
  IsSignSequence.shift_add (f := f) k hf

/-- Deprecated name for `IsSignSequence.shift_add_left`. -/
@[deprecated "Use `IsSignSequence.shift_add_left`." (since := "2026-02-28")]
lemma IsSignSequence.map_add_left {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (k + n)) :=
  IsSignSequence.shift_add_left (f := f) k hf

/-- Deprecated wrapper for the older `apSumFrom_eq_apSum_shift_add_left` naming. -/
@[deprecated "Use `apSumFrom_eq_apSum_shift_add_left`." (since := "2026-02-28")]
lemma apSumFrom_eq_apSum_shift (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  simpa using (apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := n))

/-- Deprecated wrapper for the older `*_map_add` naming.

Use `apSumFrom_eq_apSum_shift_add` instead.
-/
@[deprecated "Use `apSumFrom_eq_apSum_shift_add`." (since := "2026-02-28")]
lemma apSumFrom_eq_apSum_map_add (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using (apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n))

/-- Deprecated wrapper for the older `*_map_add_left` naming.

Use `apSumFrom_eq_apSum_shift_add_left` instead.
-/
@[deprecated "Use `apSumFrom_eq_apSum_shift_add_left`." (since := "2026-02-28")]
lemma apSumFrom_eq_apSum_map_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSum (fun x => f (a + x)) d n := by
  simpa using (apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := n))

/-- Deprecated name for `apSumFrom_shift_add`. -/
@[deprecated "Use `apSumFrom_shift_add`." (since := "2026-02-28")]
lemma apSumFrom_map_add (f : ℕ → ℤ) (k a d n : ℕ) :
  apSumFrom (fun x => f (x + k)) a d n = apSumFrom f (a + k) d n := by
  simpa using (apSumFrom_shift_add (f := f) (k := k) (a := a) (d := d) (n := n))

/-- Deprecated name for `apSumFrom_shift_add_left`. -/
@[deprecated "Use `apSumFrom_shift_add_left`." (since := "2026-02-28")]
lemma apSumFrom_map_add_left (f : ℕ → ℤ) (k a d n : ℕ) :
  apSumFrom (fun x => f (k + x)) a d n = apSumFrom f (k + a) d n := by
  simpa using (apSumFrom_shift_add_left (f := f) (k := k) (a := a) (d := d) (n := n))

/-- Deprecated name for `apSum_shift_add`. -/
@[deprecated "Use `apSum_shift_add`." (since := "2026-02-28")]
lemma apSum_map_add (f : ℕ → ℤ) (k d n : ℕ) :
  apSum (fun x => f (x + k)) d n = apSumFrom f k d n := by
  simpa using (apSum_shift_add (f := f) (k := k) (d := d) (n := n))

/-- Deprecated name for `apSum_shift_add_left`.

Note: the core normal-form lemma is `apSum_shift_add` (in the `x + k` binder convention).
This wrapper keeps the older `k + x` convention by commuting addition under the binder.
-/
@[deprecated "Use `apSum_shift_add` (after rewriting `fun x => f (k + x)` to `fun x => f (x + k)`)." (since := "2026-02-28")]
lemma apSum_map_add_left (f : ℕ → ℤ) (k d n : ℕ) :
  apSum (fun x => f (k + x)) d n = apSumFrom f k d n := by
  have hfun : (fun x => f (k + x)) = fun x => f (x + k) := by
    funext x
    simp [Nat.add_comm]
  simpa [hfun] using (apSum_shift_add (f := f) (k := k) (d := d) (n := n))

/-- Deprecated name for `HasDiscrepancyAtLeast.of_shift_add`. -/
@[deprecated "Use `HasDiscrepancyAtLeast.of_shift_add`." (since := "2026-02-28")]
lemma HasDiscrepancyAtLeast.of_map_add {f : ℕ → ℤ} {k C : ℕ} :
  HasDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C :=
  HasDiscrepancyAtLeast.of_shift_add (f := f) (k := k) (C := C)

/-- Deprecated name for `HasDiscrepancyAtLeast.of_shift_add_left`. -/
@[deprecated "Use `HasDiscrepancyAtLeast.of_shift_add_left`." (since := "2026-02-28")]
lemma HasDiscrepancyAtLeast.of_map_add_left {f : ℕ → ℤ} {k C : ℕ} :
  HasDiscrepancyAtLeast (fun x => f (k + x)) C → HasAffineDiscrepancyAtLeast f C :=
  HasDiscrepancyAtLeast.of_shift_add_left (f := f) (k := k) (C := C)

/-- Deprecated name for `HasAffineDiscrepancyAtLeast.of_shift_add`. -/
@[deprecated "Use `HasAffineDiscrepancyAtLeast.of_shift_add`." (since := "2026-02-28")]
lemma HasAffineDiscrepancyAtLeast.of_map_add {f : ℕ → ℤ} {k C : ℕ} :
  HasAffineDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C :=
  HasAffineDiscrepancyAtLeast.of_shift_add (f := f) (k := k) (C := C)

/-- Deprecated name for `HasAffineDiscrepancyAtLeast.of_shift_add_left`. -/
@[deprecated "Use `HasAffineDiscrepancyAtLeast.of_shift_add_left`." (since := "2026-02-28")]
lemma HasAffineDiscrepancyAtLeast.of_map_add_left {f : ℕ → ℤ} {k C : ℕ} :
  HasAffineDiscrepancyAtLeast (fun x => f (k + x)) C → HasAffineDiscrepancyAtLeast f C :=
  HasAffineDiscrepancyAtLeast.of_shift_add_left (f := f) (k := k) (C := C)

/-- Deprecated name for `apSumOffset_shift_add_left`. -/
@[deprecated "Use `apSumOffset_shift_add_left`." (since := "2026-03-03")]
lemma apSumOffset_shift_add_left_start_mul (f : ℕ → ℤ) (k d m n : ℕ) :
    apSumOffset (fun x => f (k + x)) d m n = apSumFrom f (m * d + k) d n := by
  simpa using
    (apSumOffset_shift_add_left (f := f) (k := k) (d := d) (m := m) (n := n))


/-! ## Mul-left paper-notation deprecated wrappers -/

/-- Deprecated wrapper around `apSum_eq_sum_Icc` writing the summand as `f (d * i)`.

Prefer `apSum_eq_sum_Icc` and rewrite with `Nat.mul_comm` as needed.
-/
@[deprecated "Use `apSum_eq_sum_Icc` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSum_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = (Finset.Icc 1 n).sum (fun i => f (d * i)) := by
  simpa [Nat.mul_comm] using (apSum_eq_sum_Icc (f := f) (d := d) (n := n))

/-- Deprecated inverse-orientation wrapper around `apSum_eq_sum_Icc_mul_left`.

Prefer `sum_Icc_eq_apSum` and rewrite with `Nat.mul_comm` as needed.
-/
@[deprecated "Use `sum_Icc_eq_apSum` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma sum_Icc_eq_apSum_mul_left (f : ℕ → ℤ) (d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (d * i)) = apSum f d n := by
  simpa [Nat.mul_comm] using (sum_Icc_eq_apSum (f := f) (d := d) (n := n))

/-- Deprecated wrapper around `apSumFrom_eq_sum_Icc` writing the summand as `f (a + d * i)`.

Prefer `apSumFrom_eq_sum_Icc` and rewrite with `Nat.mul_comm` as needed.
-/
@[deprecated "Use `apSumFrom_eq_sum_Icc` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSumFrom_eq_sum_Icc_mul_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + d * i)) := by
  simpa [Nat.mul_comm] using (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n))

/-- Deprecated inverse-orientation wrapper around `apSumFrom_eq_sum_Icc_mul_left`.

Prefer `sum_Icc_eq_apSumFrom` and rewrite with `Nat.mul_comm` as needed.
-/
@[deprecated "Use `sum_Icc_eq_apSumFrom` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma sum_Icc_eq_apSumFrom_mul_left (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (a + d * i)) = apSumFrom f a d n := by
  simpa [Nat.mul_comm] using (sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n))

/-- Deprecated wrapper around `apSumFrom_eq_sum_Icc_add` writing the summand as `f (d * i + a)`.

Prefer `apSumFrom_eq_sum_Icc_add` and rewrite with `Nat.mul_comm` as needed.
-/
@[deprecated "Use `apSumFrom_eq_sum_Icc_add` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSumFrom_eq_sum_Icc_mul_left_add (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (d * i + a)) := by
  simpa [Nat.mul_comm] using (apSumFrom_eq_sum_Icc_add (f := f) (a := a) (d := d) (n := n))

/-- Deprecated inverse-orientation wrapper around `apSumFrom_eq_sum_Icc_mul_left_add`.

Prefer `sum_Icc_eq_apSumFrom_add` and rewrite with `Nat.mul_comm` as needed.
-/
@[deprecated "Use `sum_Icc_eq_apSumFrom_add` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma sum_Icc_eq_apSumFrom_mul_left_add (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (d * i + a)) = apSumFrom f a d n := by
  simpa [Nat.mul_comm] using (sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n))

/-- Deprecated argument-order variant of `apSumFrom_mul_right`.

The stable surface standardizes on the `(f, c, a, d, n)` argument order, consistent with
`apSum_mul_right` and `apSumOffset_mul_right`.
-/
@[deprecated "Use `apSumFrom_mul_right` (with arguments ordered as `(f, c, a, d, n)`)." (since := "2026-03-04")]
lemma apSumFrom_mul_right_cfirst (c : ℤ) (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom (fun k => f k * c) a d n = apSumFrom f a d n * c := by
  simpa using (apSumFrom_mul_right (f := f) (c := c) (a := a) (d := d) (n := n))

/-- Deprecated mul-left wrapper around `sum_Icc_eq_apSumOffset_shift_add_left`.

Prefer the canonical lemma and rewrite `i * d` to `d * i` using `Nat.mul_comm` as needed.
-/
@[deprecated "Use `sum_Icc_eq_apSumOffset_shift_add_left` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma sum_Icc_eq_apSumOffset_shift_add_left_mul_left (f : ℕ → ℤ) (a d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + d * i)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa [Nat.mul_comm] using
    (sum_Icc_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n))


/-! ## Step-one deprecated wrappers -/

/-- Deprecated name for `apSumFrom_eq_apSumOffset_step_one`.

This lemma used to be a thin “`m = 0`” wrapper for the step-one offset-sum normal form.
-/
@[deprecated "Use `apSumFrom_eq_apSumOffset_step_one`." (since := "2026-03-03")]
lemma apSumFrom_eq_apSumOffset_step_one_zero_m (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  simpa using
    (apSumFrom_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n))

/-- Deprecated name for `apSumFrom_eq_apSumOffset_step_one_add_left`.

This lemma used to be a thin “`m = 0`” wrapper for the translation-friendly step-one offset-sum
normal form.
-/
@[deprecated "Use `apSumFrom_eq_apSumOffset_step_one_add_left`." (since := "2026-03-03")]
lemma apSumFrom_eq_apSumOffset_step_one_zero_m_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    (apSumFrom_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (n := n))


/-- Deprecated convenience wrapper around
`apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left` with the constant written as `a + d*m`.

Prefer using the canonical lemma and rewriting the constant as needed.
-/
@[deprecated "Use `apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left` (and rewrite `m*d+a` / `a+d*m` as needed)." (since := "2026-03-03")]
lemma apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left_mul_left (f : ℕ → ℤ) (a d : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m =
      apSum (fun k => f (d * k + (a + d * m))) 1 (n - m) := by
  simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left (f := f) (a := a) (d := d)
      (m := m) (n := n) hmn)



/-- Deprecated multiplication-on-the-left wrapper around `apSumOffset_eq_apSum_step_one`.

Prefer `apSumOffset_eq_apSum_step_one` and rewrite `((m + k) * d)` to `d * (m + k)` as needed.
-/
@[deprecated "Use `apSumOffset_eq_apSum_step_one` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSumOffset_eq_apSum_step_one_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (d * (m + k))) 1 n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n))

/-- Deprecated multiplication-on-the-left wrapper around `apSumOffset_eq_apSum_step_one_add_left`.

Prefer `apSumOffset_eq_apSum_step_one_add_left` and rewrite `k * d + m * d` to `d * k + d * m`
using `Nat.mul_comm` as needed.
-/
@[deprecated "Use `apSumOffset_eq_apSum_step_one_add_left` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSumOffset_eq_apSum_step_one_mul_left_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (d * k + d * m)) 1 n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n))

/-- Deprecated inverse-orientation wrapper around `apSumOffset_eq_apSum_step_one_mul_left`.

Prefer `apSum_step_one_eq_apSumOffset` (and rewrite with `Nat.mul_comm` as needed).
-/
@[deprecated "Use `apSum_step_one_eq_apSumOffset` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSum_step_one_mul_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (d * (m + k))) 1 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSum_step_one_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Deprecated inverse-orientation wrapper around `apSumOffset_eq_apSum_step_one_mul_left_add_left`.

Prefer `apSum_step_one_add_left_eq_apSumOffset` (and rewrite with `Nat.mul_comm` as needed).
-/
@[deprecated "Use `apSum_step_one_add_left_eq_apSumOffset` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSum_step_one_mul_left_add_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (d * k + d * m)) 1 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSum_step_one_mul_left_add_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Deprecated multiplication-on-the-left wrapper around
`apSumOffset_eq_apSumOffset_step_one_zero_m_add_left`.

Prefer `apSumOffset_eq_apSumOffset_step_one_zero_m_add_left` and rewrite `k*d + m*d` to
`d*k + d*m` as needed.
-/
@[deprecated "Use `apSumOffset_eq_apSumOffset_step_one_zero_m_add_left` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSumOffset_eq_apSumOffset_step_one_zero_m_mul_left_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (d * k + d * m)) 1 0 n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n))

/-- Deprecated inverse orientation of `apSumOffset_eq_apSumOffset_step_one_zero_m_mul_left_add_left`.

Prefer `apSumOffset_step_one_zero_m_add_left_eq_apSumOffset` and rewrite as needed.
-/
@[deprecated "Use `apSumOffset_step_one_zero_m_add_left_eq_apSumOffset` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSumOffset_step_one_zero_m_mul_left_add_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (d * k + d * m)) 1 0 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSumOffset_step_one_zero_m_mul_left_add_left (f := f) (d := d) (m := m)
      (n := n)).symm

/-- Deprecated multiplication-on-the-left wrapper around
`apSum_sub_eq_apSumOffset_step_one_zero_m_add_left`.

Prefer the canonical lemma and rewrite the summand index using `Nat.mul_comm` as needed.
-/
@[deprecated "Use `apSum_sub_eq_apSumOffset_step_one_zero_m_add_left` (and rewrite with `Nat.mul_comm` as needed)." (since := "2026-03-04")]
lemma apSum_sub_eq_apSumOffset_step_one_zero_m_mul_left_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSumOffset (fun k => f (d * k + d * m)) 1 0 n := by
  simpa [Nat.mul_comm] using
    (apSum_sub_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n))

end MoltResearch
