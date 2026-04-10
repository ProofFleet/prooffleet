import MoltResearch.Discrepancy.Basic

/-!
# `CastSimp`: opt-in simp lemmas for common `Nat`/`Int` cast shapes

This module is **opt-in**: it provides a *minimal*, loop-free collection of `[simp]` lemmas that
normalize common coercion patterns between `Nat` and `Int`.

Motivation (Track B checklist item): in nucleus-level algebra around `apSumOffset`/`discOffset`,
proof scripts often accumulate ad-hoc `norm_cast` / `zify` sequences just to rewrite

- `(n : ℤ) + (m : ℤ)` ↔ `((n+m) : ℤ)`
- `(n : ℤ) * (m : ℤ)` ↔ `((n*m) : ℤ)`

We keep the simp set small and oriented toward *contracting* expressions (fewer casts).

Design constraint: avoid simp loops; do **not** add conditional subtraction cast lemmas.
-/

namespace MoltResearch

/-! ## Addition / multiplication: cast contraction -/

/-- Contract addition of `Nat` casts in `ℤ`.

This is a targeted simp lemma meant to reduce `norm_cast` churn in nucleus API algebra.
-/
@[simp] lemma natCast_add_natCast (m n : ℕ) : (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) := by
  simp

/-- Contract multiplication of `Nat` casts in `ℤ`.

This is a targeted simp lemma meant to reduce `norm_cast` churn in nucleus API algebra.
-/
@[simp] lemma natCast_mul_natCast (m n : ℕ) : (m : ℤ) * (n : ℤ) = ((m * n : ℕ) : ℤ) := by
  simp

/-- Contract addition with a `1` cast.

This shows up frequently when normalizing `(i + 1 : ℕ)` endpoints after rewriting.
-/
@[simp] lemma natCast_add_one (n : ℕ) : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by
  simpa using (natCast_add_natCast n 1)

/-- Contract addition with a `1` cast (right-add variant).

We include both orientations to avoid commutativity noise without enabling `Nat` commutativity.
-/
@[simp] lemma one_add_natCast (n : ℕ) : 1 + (n : ℤ) = ((1 + n : ℕ) : ℤ) := by
  -- Use the non-commutative contraction lemma directly (avoid simp loops).
  simpa using (natCast_add_natCast 1 n)

end MoltResearch
