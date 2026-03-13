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
  -- Expand `discOffset` and normalize `apSumOffset … (Nat.succ n)` using `apSumOffset_succ`.
  -- Keep the endpoint in the directed form `m + Nat.succ n`.
  simp [discOffset, apSumOffset_succ, Nat.succ_eq_add_one, Nat.add_assoc]

/-- `Nat.succ`-endpoint simp lemma for the homogeneous wrapper `disc`.

See `natAbs_apSumOffset_succ_succ_eq_discOffset`.
-/
@[simp] lemma natAbs_apSum_succ_succ_eq_disc (f : ℕ → ℤ) (d n : ℕ) :
    Int.natAbs (apSum f d n + f ((Nat.succ n) * d)) = disc f d (Nat.succ n) := by
  simp [disc, apSum_succ, Nat.succ_eq_add_one, Nat.add_assoc]

/-! ## `Nat.pred (Nat.succ _)` cleanup -/

@[simp] lemma discOffset_pred_succ (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m (Nat.pred (Nat.succ n)) = discOffset f d m n := by
  simp [discOffset]

@[simp] lemma disc_pred_succ (f : ℕ → ℤ) (d n : ℕ) :
    disc f d (Nat.pred (Nat.succ n)) = disc f d n := by
  simp [disc]

end MoltResearch
