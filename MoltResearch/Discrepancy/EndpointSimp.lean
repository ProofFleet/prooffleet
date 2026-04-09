import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.AffineTail

/-!
# Endpoint simp lemmas (nucleus sums)

This module provides a tiny collection of `[simp]` lemmas for normalizing
`Nat.succ` / `Nat.pred`-style endpoints that frequently appear when working with
the nucleus API (`apSumOffset`).

Design goal: keep the rewrite orientation *translation-friendly* and avoid
introducing `Nat.add_comm` churn under binders.

These are small wrappers around existing nucleus lemmas.
-/

namespace MoltResearch

/-! ## Endpoint algebra normal forms -/

/-- Normalize a common endpoint shape produced by rewriting `Nat.succ` as `+ 1`.

This lemma exists so downstream proofs can `simp` without having to add
`Nat.add_assoc` by hand.
-/
@[simp] lemma add_add_one (m n : ℕ) : m + (n + 1) = m + n + 1 := by
  simp [Nat.add_assoc]

/-- Normalize another common endpoint shape: `m + 1 + n` → `m + n + 1`.

Again, this is intentionally a tiny, directed simp lemma to avoid ad-hoc
`Nat.add_assoc`/`Nat.add_left_comm` noise in downstream `simp` calls.
-/
@[simp] lemma add_one_add (m n : ℕ) : m + 1 + n = m + n + 1 := by
  calc
    m + 1 + n = m + (1 + n) := by
      simp [Nat.add_assoc]
    _ = m + (n + 1) := by
      simp [Nat.add_comm, Nat.add_assoc]
    _ = m + n + 1 := by
      simp [Nat.add_assoc]

/-! ## `Nat.succ` endpoints -/

/-- `Nat.succ` wrapper for `apSumOffset_succ`.

This avoids having to rewrite `Nat.succ n` into `n + 1` in downstream simp steps.
-/
@[simp] lemma apSumOffset_succ_succ (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (Nat.succ n) = apSumOffset f d m n + f ((m + Nat.succ n) * d) := by
  -- `apSumOffset_succ` is stated with `(n + 1)` and the endpoint `(m + n + 1)`.
  -- We keep the endpoint in the directed form `m + succ n`.
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
    (apSumOffset_succ (f := f) (d := d) (m := m) (n := n))

/-- `Nat.succ` wrapper for `apSumOffset_succ_length`.

This splits off the *first* term of an offset sum when the length is written as `Nat.succ n`.
-/
@[simp] lemma apSumOffset_succ_length_succ (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (Nat.succ n) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  simpa [Nat.succ_eq_add_one] using
    (apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n))

/-! ## `Nat.pred` endpoints -/

/-- A tiny convenience simp lemma: cancel a `Nat.pred (Nat.succ _)` length.

This can show up after rewriting goals that express “remove the last element” using `Nat.pred`.
-/
@[simp] lemma apSumOffset_pred_succ (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (Nat.pred (Nat.succ n)) = apSumOffset f d m n := by
  simp

@[simp] lemma apSum_pred_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (Nat.pred (Nat.succ n)) = apSum f d n := by
  simp

/-! ## `Nat.succ` wrappers for homogeneous sums -/

/-- `Nat.succ` wrapper for `apSum_succ`.

This avoids having to rewrite `Nat.succ n` into `n + 1` in downstream simp steps.
-/
@[simp] lemma apSum_succ_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (Nat.succ n) = apSum f d n + f ((Nat.succ n) * d) := by
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
    (apSum_succ (f := f) (d := d) (n := n))

/-- `Nat.succ` wrapper for `apSum_succ_length`.

This splits off the *first* term of an `apSum` when the length is written as `Nat.succ n`.
The tail is naturally expressed as an `apSumOffset` starting at `m = 1`.
-/
@[simp] lemma apSum_succ_length_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (Nat.succ n) = f d + apSumOffset f d 1 n := by
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
    (apSum_succ_length (f := f) (d := d) (n := n))

/-!
## Paper↔nucleus endpoint bridge (simp surface)

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Paper↔nucleus endpoint bridge (simp surface)”.

These are *simp wrappers* that rewrite paper-style interval endpoints `Icc (m+1) (m+n)` into the
nucleus API (`apSumOffset`, affine tail `apSumFrom … (a+m*d) …`, and `discOffset`).

Design constraints:
- Orientation is paper → nucleus to avoid simp loops.
- Keep the statements small and predictable; they should be usable by `simp` in downstream proofs.
-/

/-- `simp` wrapper: rewrite the paper-notation interval sum
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` into the nucleus tail sum `apSumOffset f d m n`. -/
@[simp] lemma sum_Icc_add_one_add_len_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- `simp` wrapper: mul-left variant of `sum_Icc_add_one_add_len_eq_apSumOffset`, rewriting
`∑ i ∈ Icc (m+1) (m+n), f (d*i)` into `apSumOffset f d m n`. -/
@[simp] lemma sum_Icc_add_one_add_len_eq_apSumOffset_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n))

/-- `simp` wrapper: rewrite the paper-notation affine tail interval sum
`∑ i ∈ Icc (m+1) (m+n), f (a + i*d)` into the nucleus affine tail `apSumFrom f (a+m*d) d n`. -/
@[simp] lemma sum_Icc_add_one_add_len_eq_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d n := by
  simpa using (sum_Icc_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n))

/-- `simp` wrapper: rewrite the paper-notation discrepancy object
`Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d))` into `discOffset f d m n`. -/
@[simp] lemma natAbs_sum_Icc_add_one_add_len_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) = discOffset f d m n := by
  unfold discOffset
  -- First rewrite the paper sum into the nucleus tail sum, then fold back into `discOffset`.
  simp

/-- Mul-left variant of `natAbs_sum_Icc_add_one_add_len_eq_discOffset`. -/
@[simp] lemma natAbs_sum_Icc_add_one_add_len_eq_discOffset_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i))) = discOffset f d m n := by
  unfold discOffset
  simp

/-- `simp` wrapper: absolute value of the paper-notation affine tail interval sum.

We don't currently have a dedicated discrepancy wrapper for `apSumFrom`, so this lemma keeps the
result as an `Int.natAbs`.
-/
@[simp] lemma natAbs_sum_Icc_add_one_add_len_eq_natAbs_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d))) =
      Int.natAbs (apSumFrom f (a + m * d) d n) := by
  simp

end MoltResearch
