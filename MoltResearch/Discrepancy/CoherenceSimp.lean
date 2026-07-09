import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset

/-!
# `CoherenceSimp`: minimal simp surface for discrepancy API coherence

This module is part of the **stable import surface** (`import MoltResearch.Discrepancy`).
It enables only a *small* set of simp rules that normalize the most common degenerate/boilerplate
parameter patterns:

- start-index arithmetic like `m + (n + k)` (push the start shift into the summand translation),
- and the corresponding `discOffset` wrapper normalization.

Design intent:
- Keep this file small.
- Prefer simp rules that move toward the nucleus normal forms used across Track B.
- Avoid enabling the full `DiscSimp` bundle, which is intentionally opt-in.

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — API coherence simp surface.
-/

namespace MoltResearch

/-! ## Start-shift normalization (stable-surface `[simp]`) -/

-- Normalize `apSumOffset f d (m + k) n` by pushing the shift into the summand translation.
attribute [simp] apSumOffset_shift_start_add
attribute [simp] apSumOffset_shift_start_add_mul_left

-- Same normalization at the discrepancy wrapper level.
attribute [simp] discOffset_shift_start_add
attribute [simp] discOffset_shift_start_add_mul_left

/-!
## Endpoint/start-index associativity helpers

Downstream proofs often produce start indices with different parenthesizations, e.g.
`(m + n) + k` vs `m + (n + k)`. Our core coherence simp lemmas (like
`discOffset_shift_start_add`) are keyed to the syntactic shape `m + k`, so we provide a
*minimal* family of simp wrappers that reassociate the start index into the convenient form
`m + (n + k)`.

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — endpoint algebra helpers.
-/

@[simp] lemma apSumOffset_start_add_assoc (f : ℕ → ℤ) (d m n k t : ℕ) :
    apSumOffset f d (m + n + k) t = apSumOffset f d (m + (n + k)) t := by
  -- `m + n + k` parses as `(m + n) + k`.
  simpa [Nat.add_assoc]

@[simp] lemma discOffset_start_add_assoc (f : ℕ → ℤ) (d m n k t : ℕ) :
    discOffset f d (m + n + k) t = discOffset f d (m + (n + k)) t := by
  simpa [Nat.add_assoc]

/-!
## Composing shifts/dilations of the summand (stable-surface `[simp]`)

Nested reindexing of the summand appears whenever two normal-form rewrites are chained:
shifting twice, dilating twice, or shifting then dilating. These simp lemmas normalize each
nested shape into a single canonical `shift_add` / `map_mul` form:

- `fun t => f ((t + a) + b)`     ↦ `fun t => f (t + (a + b))`
- `fun t => f (t * q * r)`       ↦ `fun t => f (t * (q * r))`
- `fun t => f ((t + a) * q + b)` ↦ `fun t => f (t * q + (a * q + b))`

All three right-hand sides are single-step reindexings, so the set is loop-free (each rewrite
strictly reduces the nesting depth of the summand argument).

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — Stable-surface simp normal form for
composing shifts/dilations.
-/

@[simp] lemma apSum_summand_add_add (f : ℕ → ℤ) (a b d n : ℕ) :
    apSum (fun t => f ((t + a) + b)) d n = apSum (fun t => f (t + (a + b))) d n := by
  have h : (fun t : ℕ => f ((t + a) + b)) = (fun t => f (t + (a + b))) := by
    funext t
    rw [Nat.add_assoc]
  rw [h]

@[simp] lemma apSumOffset_summand_add_add (f : ℕ → ℤ) (a b d m n : ℕ) :
    apSumOffset (fun t => f ((t + a) + b)) d m n =
      apSumOffset (fun t => f (t + (a + b))) d m n := by
  have h : (fun t : ℕ => f ((t + a) + b)) = (fun t => f (t + (a + b))) := by
    funext t
    rw [Nat.add_assoc]
  rw [h]

@[simp] lemma discOffset_summand_add_add (f : ℕ → ℤ) (a b d m n : ℕ) :
    discOffset (fun t => f ((t + a) + b)) d m n =
      discOffset (fun t => f (t + (a + b))) d m n := by
  have h : (fun t : ℕ => f ((t + a) + b)) = (fun t => f (t + (a + b))) := by
    funext t
    rw [Nat.add_assoc]
  rw [h]

@[simp] lemma apSum_summand_mul_mul (f : ℕ → ℤ) (q r d n : ℕ) :
    apSum (fun t => f (t * q * r)) d n = apSum (fun t => f (t * (q * r))) d n := by
  have h : (fun t : ℕ => f (t * q * r)) = (fun t => f (t * (q * r))) := by
    funext t
    rw [Nat.mul_assoc]
  rw [h]

@[simp] lemma apSumOffset_summand_mul_mul (f : ℕ → ℤ) (q r d m n : ℕ) :
    apSumOffset (fun t => f (t * q * r)) d m n =
      apSumOffset (fun t => f (t * (q * r))) d m n := by
  have h : (fun t : ℕ => f (t * q * r)) = (fun t => f (t * (q * r))) := by
    funext t
    rw [Nat.mul_assoc]
  rw [h]

@[simp] lemma discOffset_summand_mul_mul (f : ℕ → ℤ) (q r d m n : ℕ) :
    discOffset (fun t => f (t * q * r)) d m n =
      discOffset (fun t => f (t * (q * r))) d m n := by
  have h : (fun t : ℕ => f (t * q * r)) = (fun t => f (t * (q * r))) := by
    funext t
    rw [Nat.mul_assoc]
  rw [h]

@[simp] lemma apSum_summand_shift_mul_add (f : ℕ → ℤ) (a b q d n : ℕ) :
    apSum (fun t => f ((t + a) * q + b)) d n =
      apSum (fun t => f (t * q + (a * q + b))) d n := by
  have h : (fun t : ℕ => f ((t + a) * q + b)) = (fun t => f (t * q + (a * q + b))) := by
    funext t
    rw [Nat.add_mul, Nat.add_assoc]
  rw [h]

@[simp] lemma apSumOffset_summand_shift_mul_add (f : ℕ → ℤ) (a b q d m n : ℕ) :
    apSumOffset (fun t => f ((t + a) * q + b)) d m n =
      apSumOffset (fun t => f (t * q + (a * q + b))) d m n := by
  have h : (fun t : ℕ => f ((t + a) * q + b)) = (fun t => f (t * q + (a * q + b))) := by
    funext t
    rw [Nat.add_mul, Nat.add_assoc]
  rw [h]

@[simp] lemma discOffset_summand_shift_mul_add (f : ℕ → ℤ) (a b q d m n : ℕ) :
    discOffset (fun t => f ((t + a) * q + b)) d m n =
      discOffset (fun t => f (t * q + (a * q + b))) d m n := by
  have h : (fun t : ℕ => f ((t + a) * q + b)) = (fun t => f (t * q + (a * q + b))) := by
    funext t
    rw [Nat.add_mul, Nat.add_assoc]
  rw [h]

end MoltResearch
