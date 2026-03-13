import MoltResearch.Discrepancy.Basic

/-!
# `discOffset`/`disc` simp lemmas (opt-in)

This module is **opt-in**: it provides a *small* collection of `[simp]` lemmas that
normalize `discOffset` / `disc` expressions when endpoints are written using `Nat.succ`
(and a couple of harmless `Nat.pred (Nat.succ _)` cancellations).

Design goals:
- keep the simp set *minimal* and oriented so it does **not** cause simp loops;
- avoid forcing downstream users to rewrite `Nat.succ n` into `n + 1` by hand.

In particular, we only add simp lemmas whose **LHS is an `Int.natAbs` expression** and whose
RHS is the corresponding wrapper (`discOffset`/`disc`). This mirrors the existing simp bridges
`natAbs_apSumOffset_eq_discOffset` and `natAbs_apSum_eq_disc`.
-/

namespace MoltResearch

/-! ## `Nat.succ` normal forms -/

/-- `Nat.succ`-endpoint simp lemma for `discOffset`.

This is the `Nat.succ` wrapper analogue of `natAbs_apSumOffset_eq_discOffset`:
`Int.natAbs (apSumOffset … (n+1))` often simplifies to `discOffset … (n+1)` already,
but when the one-step expansion is present explicitly, this lemma lets `simp` close the loop
*without* rewriting `Nat.succ n` into `n + 1`.

Orientation note: we rewrite **toward** the wrapper to avoid simp loops with `discOffset_def`.
-/
@[simp] lemma natAbs_apSumOffset_succ_succ_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n + f ((m + Nat.succ n) * d)) = discOffset f d m (Nat.succ n) := by
  -- Avoid simp loops: rewrite `Nat.succ n` as `n + 1` and then use `apSumOffset_succ` directly.
  unfold discOffset
  -- Prevent `simp` from refolding via `natAbs_apSumOffset_eq_discOffset`.
  simp [Nat.succ_eq_add_one, Nat.add_assoc, -natAbs_apSumOffset_eq_discOffset]
  -- Close using the one-step expansion of `apSumOffset`.
  rw [apSumOffset_succ (f := f) (d := d) (m := m) (n := n)]
  -- Normalize associativity in the endpoint `(m + (n + 1))`.
  simp [Nat.add_assoc]

/-- `Nat.succ`-endpoint simp lemma for the homogeneous wrapper `disc`.

See `natAbs_apSumOffset_succ_succ_eq_discOffset`.
-/
@[simp] lemma natAbs_apSum_succ_succ_eq_disc (f : ℕ → ℤ) (d n : ℕ) :
    Int.natAbs (apSum f d n + f ((Nat.succ n) * d)) = disc f d (Nat.succ n) := by
  unfold disc
  -- Avoid `simp` refolding `Int.natAbs (apSum …)` back into wrappers.
  simp [Nat.succ_eq_add_one, -natAbs_apSum_eq_disc, -natAbs_apSum_eq_discrepancy]
  rw [apSum_succ (f := f) (d := d) (n := n)]

/-! ## `Nat.pred (Nat.succ _)` cleanup -/

@[simp] lemma discOffset_pred_succ (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m (Nat.pred (Nat.succ n)) = discOffset f d m n := by
  simp

@[simp] lemma disc_pred_succ (f : ℕ → ℤ) (d n : ℕ) :
    disc f d (Nat.pred (Nat.succ n)) = disc f d n := by
  simp

end MoltResearch
