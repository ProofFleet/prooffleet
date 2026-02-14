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

Two conventions that pay for themselves quickly:
- **Translation-friendly summands:** prefer the `… + const` shape *inside binders* (e.g. `i * d + a` or
  `k + a`) because `simp` and `ring_nf` tend to cooperate better without needing `Nat.add_comm` under
  lambdas. Many rewrite lemmas come in both `a + i*d` and `i*d + a` flavors; when in doubt, reach
  for the `_add` / `_add_left` variants (e.g. `apSumFrom_tail_eq_sum_Icc_add`,
  `sum_Icc_eq_apSumFrom_tail_of_le_add`, `apSumOffset_eq_apSum_shift_add`).
- **Difference → tail early:** when you see a subtraction like `apSum … (m+n) - apSum … m` (or the
  affine analogue), rewrite it to an explicit tail sum (`apSumOffset … m n` / `apSumFrom …` tail)
  *before* doing algebra. This keeps subsequent splitting/bounding lemmas in the nucleus API.

Arithmetic progression sums:
- Prefer `apSum f d n` for homogeneous AP sums. Split lengths via `apSum_add_length`.
  For a head+tail decomposition, use `apSum_succ_length`. For a right-end “append one term”
  decomposition, use `apSum_succ`. For a “step-one” normalization (bundle the step size `d`
  into the summand), rewrite
  `apSum f d n` ↦ `apSum (fun k => f (k * d)) 1 n` via `apSum_eq_apSum_step_one`
  (and back via `apSum_step_one_eq_apSum`).
  If an `apSumOffset` appears with `m = 0`, rewrite it back to `apSum` via
  `apSumOffset_zero_m`.
  If `d = 1`, you can also rewrite directly to the plain interval sum
  `∑ i ∈ Icc 1 n, f i` via `apSum_one_d`.
  If `d = 0`, simp to the expected “degenerate constant AP” form
  `apSum f 0 n = n • f 0` via `apSum_zero_d`.
- Prefer `apSumOffset f d m n` for “tail starting after `m` steps of length `n`”.
  If `d = 0`, simp to the expected “degenerate constant AP” form
  `apSumOffset f 0 m n = n • f 0` via `apSumOffset_zero_d`.
  For a head+tail decomposition, use `apSumOffset_succ_length`.
  For a right-end “append one term” decomposition, use `apSumOffset_succ`.
  Rewrite between tails and differences using `apSumOffset_eq_sub` and
  `apSum_sub_apSum_eq_apSumOffset`. When you are already in the canonical `(m + n) - m` form,
  prefer `apSum_sub_eq_apSumOffset` (subtraction → tail) for rewriting.
  For “tail-of-tail” decompositions, rewrite differences of offset sums via
  `apSumOffset_sub_eq_apSumOffset_tail` (normal form) or `apSumOffset_sub_apSumOffset_eq_apSumOffset`
  (when a length inequality `n₁ ≤ n₂` is available). To split an offset sum at an intermediate
  length, use `apSumOffset_eq_add_apSumOffset_tail`.
  For paper notation, rewrite to an interval sum via `apSumOffset_eq_sum_Icc` (or, if `d = 1`,
  via `apSumOffset_one_d`) and split such interval sums into consecutive blocks via
  `sum_Icc_add_length`; for the normal-form difference of offset sums, use
  `apSumOffset_sub_eq_sum_Icc`. If your surface statement uses a
  “variable” upper endpoint `n` (with a hypothesis `m ≤ n`), normalize using
  `sum_Icc_eq_apSumOffset_of_le` (paper → nucleus) and `apSumOffset_eq_sum_Icc_of_le` (nucleus →
  paper). (Or rewrite directly via `apSum_sub_eq_sum_Icc` when starting from a difference, and
  `apSum_sub_apSum_eq_sum_Icc` when starting from `apSum … n - apSum … m` with `m ≤ n`).
  Sometimes it is useful to change viewpoint on offset sums:
  - offset ↔ affine: `apSumOffset f d m n` ↔ `apSumFrom f (m * d) d n` via `apSumOffset_eq_apSumFrom`.
  - “step-one” normalization (bundle `d` into the summand):
    - keep an `apSumOffset` shape: `apSumOffset f d m n` ↦ `apSumOffset (fun k => f (k * d)) 1 m n` via
      `apSumOffset_eq_apSumOffset_step_one` (and back via `apSumOffset_step_one_eq_apSumOffset`).
    - or switch to an `apSum` shape: `apSumOffset f d m n` ↦ `apSum (fun k => f ((m + k) * d)) 1 n` via
      `apSumOffset_eq_apSum_step_one` (and back via `apSum_step_one_eq_apSumOffset`).
    - if you want to keep an offset-sum normal form *and* eliminate the explicit offset and step,
      rewrite `apSumOffset f d m n` ↦ `apSumOffset (fun k => f ((m + k) * d)) 1 0 n` via
      `apSumOffset_eq_apSumOffset_step_one_zero_m`.
  - shifted-sequence normalization:
    - `apSumOffset f d m n` ↦ `apSum (fun k => f (m * d + k)) d n` via `apSumOffset_eq_apSum_shift`.
    - `apSumOffset f d m n` ↦ `apSum (fun k => f (k + m * d)) d n` via
      `apSumOffset_eq_apSum_shift_add` (translation-friendly `k + const` form).
    - If you want to keep an `apSumOffset` shape while eliminating the explicit offset parameter,
      rewrite
      `apSumOffset f d m n` ↦ `apSumOffset (fun k => f (m * d + k)) d 0 n` via
      `apSumOffset_eq_apSumOffset_shift`.
      If you prefer the translation-friendly `k + m*d` form, use
      `apSumOffset_eq_apSumOffset_shift_add` instead.
- Prefer `apSumFrom f a d n` for affine AP sums `a + d, a + 2d, …, a + nd`.
  Split lengths via `apSumFrom_add_length`.
  For a right-end “append one term” decomposition, use `apSumFrom_succ`.
  For a homogeneous-sum view (shift the sequence, keep the step size `d`), rewrite
  - `apSumFrom f a d n` ↦ `apSum (fun k => f (k + a)) d n` via `apSumFrom_eq_apSum_shift_add`.
  - or `apSumFrom f a d n` ↦ `apSum (fun k => f (a + k)) d n` via `apSumFrom_eq_apSum_shift`.
  If you instead want to *commute the translation past the multiplication* (i.e. package the
  translation as `x ↦ f (x + a)` under the `apSum` binder), use `apSumFrom_eq_apSum_map_add`
  (or the `_left` variant `apSumFrom_eq_apSum_map_add_left`).
  For a “step-one” normalization (useful when you want to treat the AP step as part of the
  summand), rewrite
  `apSumFrom f a d n` ↦ `apSum (fun k => f (a + k * d)) 1 n` via `apSumFrom_eq_apSum_step_one`
  (and back via `apSum_step_one_eq_apSumFrom`).
  If you prefer the offset on the right, use the translation-friendly variant
  `apSumFrom_eq_apSum_step_one_add_left` to get `apSum (fun k => f (k * d + a)) 1 n`.
  and tails `apSumFrom f (a + m*d) d n` ↦ `apSum (fun k => f (a + (m + k) * d)) 1 n` via
  `apSumFrom_tail_eq_apSum_step_one` (and back via `apSum_step_one_eq_apSumFrom_tail`).
  If you want an offset-sum normal form on the shifted sequence `k ↦ f (a + k)`, rewrite
  `apSumFrom f a d n` ↦ `apSumOffset (fun k => f (a + k)) d 0 n` via
  `apSumFrom_eq_apSumOffset_shift`. If you prefer the translation-friendly `k ↦ f (k + a)` form,
  use `apSumFrom_eq_apSumOffset_shift_add`.
  If `d = 0`, simp via `apSumFrom_zero_d` (degenerate constant AP).
  If `a = 0`, rewrite to a homogeneous AP sum via `apSumFrom_zero_a` (and back via
  `apSum_eq_apSumFrom`).
  For tails/differences, rewrite via `apSumFrom_tail_eq_sub` (tail → difference) or
  `apSumFrom_sub_eq_apSumFrom_tail` (difference → tail, in the canonical `(m + n) - m` form).
  For differences with an inequality `m ≤ n`, use `apSumFrom_sub_apSumFrom_eq_apSumFrom`.
  If you want the canonical offset-sum normal form on the shifted sequence `k ↦ f (a + k)`, use
  `apSumFrom_sub_eq_apSumOffset_shift` for the `(m + n) - m` normal form, and
  `apSumFrom_sub_apSumFrom_eq_apSumOffset_shift` for the general `m ≤ n` case.
  If you prefer the `k ↦ f (k + a)` form, use the `_shift_add` variants:
  `apSumFrom_sub_eq_apSumOffset_shift_add` and `apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add`.
  For tail-of-tail differences with the same start `a + m*d`, prefer
  `apSumFrom_tail_sub_eq_apSumFrom_tail` (tail difference → later tail) or, if you want the offset
  normal form on the shifted sequence `k ↦ f (a + k)`,
  `apSumFrom_tail_sub_eq_apSumOffset_shift_tail`. If you prefer the translation-friendly
  `k ↦ f (k + a)` form, use `apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail`.
  For paper notation, rewrite:
  - `apSumFrom f a d n` via `apSumFrom_eq_sum_Icc` (or, if `d = 1`, via `apSumFrom_one_d`),
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
  If you prefer a strict-positivity step-size side condition `d > 0` (instead of `d ≥ 1`), use
  `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
- For affine discrepancy, the analogous “paper notation” witness normal form is
  `forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`.
  If you want to eliminate affine sums entirely, you can also rewrite affine unbounded discrepancy to
  “some shift has large homogeneous discrepancy” via
  `forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift`.
- When the sequence is reindexed, prefer the dedicated transforms instead of re-proving the
  bookkeeping from scratch:
  - multiplicative reindexing `x ↦ x * k`: `HasDiscrepancyAtLeast.of_map_mul`,
    `HasAffineDiscrepancyAtLeast.of_map_mul` (and sum-level rewrites like `apSum_map_mul`).
  - additive reindexing `x ↦ x + k`: `HasDiscrepancyAtLeast.of_map_add`,
    `HasAffineDiscrepancyAtLeast.of_map_add` (and sum-level rewrites like `apSumFrom_map_add`).
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
       If you want a difference-of-partial-sums normal form directly, use `sum_Icc_eq_apSum_sub`.
       If your surface statement uses `Icc (m+1) n` with a hypothesis `m ≤ n`, prefer
       `sum_Icc_eq_apSumOffset_of_le` (tail form) or `sum_Icc_eq_apSum_sub_apSum_of_le` (difference form).
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

example : apSum f 1 n = (Finset.Icc 1 n).sum f := by
  simpa using apSum_one_d (f := f) (n := n)

-- Degenerate constant APs.
example : apSum f 0 n = n • f 0 := by
  simp

example : apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  simpa using apSum_eq_apSum_step_one (f := f) (d := d) (n := n)

example : apSum (fun k => f (k * d)) 1 n = apSum f d n := by
  simpa using apSum_step_one_eq_apSum (f := f) (d := d) (n := n)

-- Translation-friendly affine “step-one” normal forms.
example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f (a + m * d) d n = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
  simpa using
    apSumFrom_tail_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Offset ↔ affine normal forms.
example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Step-one normalization that stays inside the affine nucleus API.
example : apSumFrom f a d n = apSumFrom (fun k => f (a + k * d)) 0 1 n := by
  simpa using apSumFrom_eq_apSumFrom_step_one (f := f) (a := a) (d := d) (n := n)

-- Differences of partial sums: normalize to tails early.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using
    apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  simpa using apSum_succ (f := f) (d := d) (n := n)

example : apSum f d (n + 1) = f d + apSumOffset f d 1 n := by
  simpa using apSum_succ_length (f := f) (d := d) (n := n)

example : apSumOffset f d 0 n = apSum f d n := by
  simp

example : apSumOffset f d m 0 = 0 := by
  simp

-- Degenerate constant AP tails.
example : apSumOffset f 0 m n = n • f 0 := by
  simp

example : apSumOffset f d m (n + 1) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  simpa using apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  simpa using apSumOffset_succ (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  simpa using apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)

-- Canonical “difference of partial sums” normal form: rewrite subtraction into a tail.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)).symm

-- Variable upper endpoints often appear in surface statements. When `m ≤ n`, normalize
-- `∑ i ∈ Icc (m+1) n, ...` into the canonical tail length `n - m`.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn

example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
  simpa using apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (k * d)) 1 m n = apSumOffset f d m n := by
  simpa using apSumOffset_step_one_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)

example : apSum (fun k => f ((m + k) * d)) 1 n = apSumOffset f d m n := by
  simpa using apSum_step_one_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- A translation-friendly variant of the step-one form: `k ↦ f (k*d + m*d)`.
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
  simpa using apSumOffset_eq_apSumOffset_step_one_zero_m (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  simpa using
    apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f (m * d + k)) d n := by
  simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Splitting a paper-notation tail sum into consecutive blocks matches the nucleus split lemma.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Normal form: difference of offset sums with the same `m` becomes a later tail.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)


example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Splitting a longer tail into an initial segment plus a (normalized) later tail.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_eq_add_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)

example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (i * d)) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)

example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f 1 m n = (Finset.Icc (m + 1) (m + n)).sum f := by
  simpa using apSumOffset_one_d (f := f) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSum f d (m + n) - apSum f d m := by
  simpa using sum_Icc_eq_apSum_sub (f := f) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum f d n - apSum f d m := by
  simpa using sum_Icc_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = apSum f d n - apSum f d m := by
  simpa using apSumOffset_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_apSum_eq_sum_Icc (f := f) (d := d) (m := m) (n := n) hmn

example :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)

-- Translation-friendly paper notation: avoid commuting `a + …` under binders.
example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (i * d + a)) := by
  simpa using apSumFrom_eq_sum_Icc_add (f := f) (a := a) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n)

-- Affine start `a = 0` recovers the homogeneous AP sum.
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_a (f := f) (d := d) (n := n)

example : apSumFrom f a 1 n = (Finset.Icc 1 n).sum (fun i => f (a + i)) := by
  simpa using apSumFrom_one_d (f := f) (a := a) (n := n)

example : apSumFrom f a d (n + 1) = apSumFrom f a d n + f (a + (n + 1) * d) := by
  simpa using apSumFrom_succ (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d 0 = 0 := by
  simp

example : apSumFrom f a d (n + 1) = f (a + d) + apSumFrom f (a + d) d n := by
  simpa using apSumFrom_succ_length (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (n₁ + n₂) = apSumFrom f a d n₁ + apSumFrom f (a + n₁ * d) d n₂ := by
  simpa using apSumFrom_add_length (f := f) (a := a) (d := d) (m := n₁) (n := n₂)

example : apSumFrom f a d (m + n) = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_add_length (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f a 0 n = n • f a := by
  simp

-- Affine sums at `a = 0` are just homogeneous AP sums.
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_a (f := f) (d := d) (n := n)

example : apSum f d n = apSumFrom f 0 d n := by
  simpa using apSum_eq_apSumFrom (f := f) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  simpa using apSumFrom_eq_apSum_shift (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (a + k * d)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  simpa using
    apSumFrom_eq_apSumOffset_step_one_zero_m (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    apSumFrom_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (n := n)

example : apSum (fun k => f (a + k * d)) 1 n = apSumFrom f a d n := by
  simpa using apSum_step_one_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n)

-- Canonical affine difference `(m+n) - m` as an offset sum on the shifted sequence.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Variable upper endpoints appear in surface statements.
-- When `m ≤ n`, normalize the difference `apSumFrom … n - apSumFrom … m` into the canonical tail
-- length `n - m` (in translation-friendly `k + a` form).
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn)

-- “Paper notation” for affine tails, in the translation-friendly `i*d + a` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Variable upper endpoints appear often in surface statements.
-- When `m ≤ n`, normalize `∑ i ∈ Icc (m+1) n, f (i*d + a)` into the canonical tail length `n - m`.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d + a)) =
      apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example : apSumFrom f (a + m * d) d n = apSum (fun k => f (a + (m + k) * d)) 1 n := by
  simpa using apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSum (fun k => f (a + (m + k) * d)) 1 n = apSumFrom f (a + m * d) d n := by
  simpa using apSum_step_one_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

-- Head+tail normal form for affine tails: increment the tail parameter `m`.
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f (a + (m + 1) * d) + apSumFrom f (a + (m + 1) * d) d n := by
  simpa using apSumFrom_tail_succ_length (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (a + k)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k + a)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (a + m * d) d n = apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d n := by
  simpa using sum_Icc_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ m + n) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (a + i * d)) +
        (Finset.Icc (k + 1) (m + n)).sum (fun i => f (a + i * d)) := by
  simpa using
    (sum_Icc_split_affine_of_le (f := f) (a := a) (d := d) (m := m) (k := k) (n := m + n) hmk hkn)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_sub_eq_sum_Icc (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using sum_Icc_eq_apSumFrom_sub (f := f) (a := a) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    (sum_Icc_eq_apSumFrom_tail_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn)

example (hmn : m ≤ n) :
    apSumFrom f (a + m * d) d (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_sub_apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using
    sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

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
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ (∀ C : ℕ, Nonempty (DiscrepancyWitnessPos f C)) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, Nonempty (AffineDiscrepancyWitnessPos f C)) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  simpa using
    forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ a : ℕ, HasDiscrepancyAtLeast (fun k => f (a + k)) C) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift (f := f)

/-! ### Transform / reindexing regression tests -/

example (k : ℕ) : apSum (fun x => f (x * k)) d n = apSum f (d * k) n := by
  simpa using apSum_map_mul (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSum (fun x => f (x + k)) d n = apSumFrom f k d n := by
  simpa using apSum_map_add (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSum (fun x => f (k + x)) d n = apSumFrom f k d n := by
  simpa using apSum_map_add_left (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSumOffset (fun x => f (k + x)) d m n = apSumFrom f (k + m * d) d n := by
  simpa using apSumOffset_map_add_left (f := f) (k := k) (d := d) (m := m) (n := n)

example (k C : ℕ) (hk : k > 0) :
    HasDiscrepancyAtLeast (fun x => f (x * k)) C → HasDiscrepancyAtLeast f C := by
  intro h
  exact HasDiscrepancyAtLeast.of_map_mul (f := f) (hk := hk) (h := h)

example (k C : ℕ) :
    HasDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C := by
  intro h
  exact HasDiscrepancyAtLeast.of_map_add (f := f) (k := k) (C := C) h

example (c : ℤ) (hc : c ≠ 0) (C : ℕ) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => c * f n) C := by
  intro h
  exact HasDiscrepancyAtLeast.mul_left_of_ne_zero (f := f) (C := C) c hc h

end NormalFormExamples

end MoltResearch
