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

end MoltResearch
