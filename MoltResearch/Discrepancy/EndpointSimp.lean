import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset

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

end MoltResearch
