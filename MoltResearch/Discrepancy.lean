import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Parity
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.AffineTail
import MoltResearch.Discrepancy.Const
import MoltResearch.Discrepancy.Scale
import MoltResearch.Discrepancy.Translate
import MoltResearch.Discrepancy.Reindex
import MoltResearch.Discrepancy.Bound
import MoltResearch.Discrepancy.Witness

/-!
# Discrepancy (module aggregator)

This file is the **stable import surface** for the discrepancy scaffold.

Rule of thumb:
- New reusable discrepancy artifacts should live in `MoltResearch/Discrepancy/*.lean`.
- Downstream work should prefer `import MoltResearch.Discrepancy` unless it needs a narrower import.
- Keep this aggregator small and boring: it is the API boundary.

## Normal forms (preferred rewrite targets)

The Track B lemma library is intended to be *directed*: we want a small set of
canonical shapes that downstream files can rewrite into and then work with.

Arithmetic progression sums:
- Prefer `apSum f d n` for homogeneous AP sums. Split lengths via `apSum_add_length`.
  For a head+tail decomposition, use `apSum_succ_length`.
  If an `apSumOffset` appears with `m = 0`, rewrite it back to `apSum` via
  `apSumOffset_zero_m`.
- Prefer `apSumOffset f d m n` for “tail starting after `m` steps of length `n`”.
  For a head+tail decomposition, use `apSumOffset_succ_length`.
  Rewrite between tails and differences using `apSumOffset_eq_sub` and
  `apSum_sub_apSum_eq_apSumOffset`. When you are already in the canonical `(m + n) - m` form,
  prefer `apSum_sub_eq_apSumOffset` (subtraction → tail) for rewriting.
  For “tail-of-tail” decompositions, rewrite differences of offset sums via
  `apSumOffset_sub_eq_apSumOffset_tail` (normal form) or `apSumOffset_sub_apSumOffset_eq_apSumOffset`
  (when a length inequality `n₁ ≤ n₂` is available). To split an offset sum at an intermediate
  length, use `apSumOffset_eq_add_apSumOffset_tail`.
  For paper notation, rewrite to an interval sum via `apSumOffset_eq_sum_Icc`; for the normal-form
  difference of offset sums, use `apSumOffset_sub_eq_sum_Icc`. If your surface statement uses a
  “variable” upper endpoint `n` (with a hypothesis `m ≤ n`), normalize using
  `sum_Icc_eq_apSumOffset_of_le` (paper → nucleus) and `apSumOffset_eq_sum_Icc_of_le` (nucleus →
  paper). (Or rewrite directly via `apSum_sub_eq_sum_Icc` when starting from a difference, and
  `apSum_sub_apSum_eq_sum_Icc` when starting from `apSum … n - apSum … m` with `m ≤ n`).
- Prefer `apSumFrom f a d n` for affine AP sums `a + d, a + 2d, …, a + nd`.
  Split lengths via `apSumFrom_add_length`.
  For tails/differences, rewrite via `apSumFrom_tail_eq_sub` (tail → difference) or
  `apSumFrom_sub_eq_apSumFrom_tail` (difference → tail, in the canonical `(m + n) - m` form).
  For differences with an inequality `m ≤ n`, use `apSumFrom_sub_apSumFrom_eq_apSumFrom`.
  If you want the canonical offset-sum normal form on the shifted sequence `k ↦ f (a + k)`, use
  `apSumFrom_sub_eq_apSumOffset_shift` for the `(m + n) - m` normal form, and
  `apSumFrom_sub_apSumFrom_eq_apSumOffset_shift` for the general `m ≤ n` case.
  For tail-of-tail differences with the same start `a + m*d`, prefer
  `apSumFrom_tail_sub_eq_apSumFrom_tail` (tail difference → later tail) or, if you want the offset
  normal form on the shifted sequence `k ↦ f (a + k)`,
  `apSumFrom_tail_sub_eq_apSumOffset_shift_tail`.
  For paper notation, rewrite:
  - `apSumFrom f a d n` via `apSumFrom_eq_sum_Icc`,
  - tails `apSumFrom f (a + m*d) d n` via `apSumFrom_tail_eq_sum_Icc`,
  - and differences via `apSumFrom_sub_eq_sum_Icc` / `apSumFrom_sub_apSumFrom_eq_sum_Icc`.

Discrepancy predicates / witnesses:
- Treat `HasDiscrepancyAtLeast` and `HasAffineDiscrepancyAtLeast` as normalization boundaries
  for existence statements; use the structured witness API in `Witness.lean` when convenient.
- If you want to keep witnesses structured, rewrite unbounded discrepancy to a `Nonempty` witness
  family:
  - homogeneous: `forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos`
  - affine: `forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos`
- For surface statements, rewrite `∀ C, HasDiscrepancyAtLeast f C` to an explicit witness form
  `∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ …` via
  `forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos`.
  If you want paper notation, further rewrite to an explicit interval-sum witness form via
  `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`.
- For affine discrepancy, the analogous “paper notation” witness normal form is
  `forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`.
  If you want to eliminate affine sums entirely, you can also rewrite affine unbounded discrepancy to
  “some shift has large homogeneous discrepancy” via
  `forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift`.
- When the sequence is reindexed, prefer the dedicated transforms (`…of_map_mul`, `…of_map_add`)
  instead of re-proving the bookkeeping from scratch.
- When scaling the sequence by a nonzero integer, prefer the dedicated scaling lemmas
  (`HasDiscrepancyAtLeast.mul_left_scale`, etc.) rather than unfolding definitions.

## Worked rewrite recipe (quick mental model)

When you see a sum in “paper notation”, try to normalize it into the nucleus API first,
*then* apply bounds/triangle inequality, and only at the end rewrite back to `Icc` sums.

A typical rewrite pipeline:
1. Convert paper notation to nucleus notation (and back):
   - Paper → nucleus:
     - `∑ i ∈ Icc 1 n, f (i*d)` ↦ `apSum f d n` via `sum_Icc_eq_apSum`.
     - `∑ i ∈ Icc (m+1) (m+n), f (i*d)` ↦ `apSumOffset f d m n` via `sum_Icc_eq_apSumOffset`.
     - `∑ i ∈ Icc 1 n, f (a + i*d)` ↦ `apSumFrom f a d n` via `sum_Icc_eq_apSumFrom`.
     - `∑ i ∈ Icc (m+1) (m+n), f (a + i*d)` ↦ `apSumFrom f (a + m*d) d n` via
       `sum_Icc_eq_apSumFrom_tail`.
       If your surface statement uses `Icc (m+1) n` with an inequality `m ≤ n`, prefer
       `sum_Icc_eq_apSumFrom_tail_of_le`.
   - Nucleus → paper:
     - `apSum f d n` ↦ `∑ i ∈ Icc 1 n, f (i*d)` via `apSum_eq_sum_Icc`.
     - `apSumOffset f d m n` ↦ `∑ i ∈ Icc (m+1) (m+n), f (i*d)` via `apSumOffset_eq_sum_Icc`.
     - `apSumFrom f a d n` ↦ `∑ i ∈ Icc 1 n, f (a + i*d)` via `apSumFrom_eq_sum_Icc`.
2. Normalize differences of partial sums into tails:
   - `apSum f d (m+n) - apSum f d m` ↦ `apSumOffset f d m n` via `apSum_sub_eq_apSumOffset`.
   - `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁` ↦ `apSumOffset f d (m+n₁) n₂` via
     `apSumOffset_sub_eq_apSumOffset_tail`.
3. Split sums by length (canonical “one cut” normal form):
   - `apSum_add_length`, `apSumOffset_add_length`, `apSumFrom_add_length`.
4. Only when you want to match the literature, rewrite back to interval sums:
   - `apSumOffset_eq_sum_Icc`, `apSum_sub_eq_sum_Icc`, `apSumOffset_sub_eq_sum_Icc`, etc.

The small “example” blocks below are regression tests that these normal-form lemmas remain usable
from the stable surface import `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

section NormalFormExamples

variable (f : ℕ → ℤ) (a d m n n₁ n₂ : ℕ)

example : apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  simpa using apSum_eq_sum_Icc (f := f) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using sum_Icc_eq_apSum (f := f) (d := d) (n := n)

example : apSum f d (n + 1) = f d + apSumOffset f d 1 n := by
  simpa using apSum_succ_length (f := f) (d := d) (n := n)

example : apSumOffset f d 0 n = apSum f d n := by
  simp

example : apSumOffset f d m (n + 1) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  simpa using apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using
    apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = apSum f d n - apSum f d m := by
  simpa using apSumOffset_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d n := by
  simpa using sum_Icc_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    (sum_Icc_eq_apSumFrom_tail_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn)

example (hmn : m ≤ n) :
    apSumFrom f (a + m * d) d (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

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
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ (∀ C : ℕ, Nonempty (DiscrepancyWitnessPos f C)) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, Nonempty (AffineDiscrepancyWitnessPos f C)) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

end NormalFormExamples

end MoltResearch
