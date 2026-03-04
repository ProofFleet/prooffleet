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

end MoltResearch
