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
-- Note: `MoltResearch.Discrepancy.NormalFormExamples` is a standalone regression-test module.
-- It should import `MoltResearch.Discrepancy` (the stable surface) rather than being imported here,
-- to avoid an import cycle.
import MoltResearch.Discrepancy.Examples

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
  lambdas.

  Many rewrite lemmas come in both `a + …` and `… + a` flavors. In this folder we try to follow a
  consistent naming convention:
  - suffix `_add` usually means the bound variable is on the **left**: `fun k => f (k + a)`;
  - suffix `_add_left` usually means the constant is on the **left**: `fun k => f (a + k)`;
  - when multiplication is involved, `_add_left` often corresponds to the paper-friendly `k * d + a`.

  A small but practical consequence: when you are trying to normalize *affine tails* into an
  `apSumOffset` on a shifted sequence, the `_shift_add` lemma family keeps the binder in the
  translation-friendly `k + a` form:

  - `apSumFrom f (a + m*d) d n` ↦ `apSumOffset (fun k => f (k + a)) d m n` via
    `apSumFrom_tail_eq_apSumOffset_shift_add`.

  This avoids having to commute `Nat.add_comm` under a lambda later.

  When in doubt, reach for the `_add` / `_add_left` variants (e.g. `apSumFrom_tail_eq_sum_Icc_add`,
  `sum_Icc_eq_apSumFrom_tail_of_le_add`, `apSumFrom_tail_succ_length_add_left`,
  `apSumOffset_eq_apSum_shift_add`).

## NormalFormExamples

`MoltResearch.Discrepancy.NormalFormExamples` is a **standalone regression-test module**.
It imports the stable surface `MoltResearch.Discrepancy` and contains a collection of `example`
blocks that act as compile-time checks for the preferred normal-form rewrite pipelines.

It is not imported here (in the stable surface) for two reasons:
- avoid an import cycle (`NormalFormExamples` should depend on the stable surface, not vice versa)
- keep downstream compile costs low for users who only need the API

If you want to run these locally or use them as a reference, you can import the module directly:

```lean
import MoltResearch.Discrepancy.NormalFormExamples
```

### Choosing a translation normal form (`_shift` vs `_shift_add` vs `_map_add`)

When you “shift the sequence” or “shift the index”, there are three recurring normal forms. They’re
mathematically equivalent, but *proof automation* tends to prefer one depending on what you’re doing:

- **`_shift_add`**: translation-friendly binder form `k ↦ f (k + a)`.
  Use this when you want `simp`/`ring_nf` to behave without rewriting `Nat.add_comm` under a lambda.
  This is the default convention in this folder.

- **`_shift`**: constant-on-the-left binder form `k ↦ f (a + k)`.
  Use this when your goal statement already has `a + …` everywhere (e.g. it came from rewriting a
  paper statement `a + i*d`) and you want to avoid commutativity steps.

- **`_map_add` / `_map_add_left`**: “push the translation into the function” form `x ↦ f (x + a)`.
  Use this when you want to *commute the translation past multiplication* (e.g. normalize
  `a + (m+k)*d` into something like `(m+k)*d` under `apSum` while shifting the sequence).

Practical rule: if you’re not sure which one to pick, normalize to `_shift_add` first; it composes
well with the offset/tail API and keeps later splitting/bounding lemmas uniform.

### Multiplication-left variants (`*_mul_left`)

Many paper statements prefer `i * d`, but sometimes it’s better to keep the binder in the form
`d * i` to avoid commuting multiplication *under a lambda*.

The `*_mul_left` lemma families (e.g. `apSumOffset_eq_sum_Icc_mul_left`,
`sum_Icc_eq_apSumOffset_of_le_mul_left`, `apSum_sub_eq_sum_Icc_mul_left`) keep summands as `d * i`.
Downstream developments should pick one multiplication-side convention and stick to it; the
`*_mul_left` variants pair well with the translation-friendly `_shift_add` convention.

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
  For “tail-of-tail” decompositions, move between tails and differences of offset sums using
  `apSumOffset_tail_eq_sub` (tail → difference) and `apSumOffset_sub_eq_apSumOffset_tail`
  (difference → tail, normal form). When a length inequality `n₁ ≤ n₂` is available, use
  `apSumOffset_sub_apSumOffset_eq_apSumOffset`.
  If you want to further eliminate the explicit offset parameter in the resulting tail, normalize
  to an `m = 0` offset sum on a shifted sequence using `apSumOffset_sub_eq_apSumOffset_shift_add`
  (canonical `n₁ + n₂` form) or `apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add` (inequality
  form).
  To split an offset sum at an intermediate length, use `apSumOffset_eq_add_apSumOffset_tail`.
  For paper notation, rewrite to an interval sum via `apSumOffset_eq_sum_Icc` (or, if `d = 1`,
  via `apSumOffset_one_d`). If you want the translation-friendly `d * i` binder form, use
  `apSumOffset_eq_sum_Icc_mul_left`.
  If you prefer a *fixed* lower endpoint, rewrite to the length-indexed interval sum
  `(Finset.Icc 1 n).sum (fun i => f ((m + i) * d))` via `apSumOffset_eq_sum_Icc_length` (or use
  the `d * (m+i)` summand convention via `apSumOffset_eq_sum_Icc_length_mul_left`).
  If you start from the canonical difference normal form `apSum f d (m+n) - apSum f d m`, rewrite
  directly to this fixed-lower-endpoint paper form via `apSum_sub_eq_sum_Icc_length`
  (or `apSum_sub_eq_sum_Icc_length_mul_left`).
  Normalize back to the nucleus API via `sum_Icc_eq_apSumOffset_length` / `sum_Icc_eq_apSumOffset_length_mul_left`.
  Split such interval sums into consecutive blocks via `sum_Icc_add_length`; for the normal-form
  difference of offset sums, use `apSumOffset_sub_eq_sum_Icc`. If your surface statement uses a
  “variable” upper endpoint `n` (with a hypothesis `m ≤ n`), normalize using
  `sum_Icc_eq_apSumOffset_of_le` / `sum_Icc_eq_apSumOffset_of_le_mul_left` (paper → nucleus) and
  `apSumOffset_eq_sum_Icc_of_le` / `apSumOffset_eq_sum_Icc_of_le_mul_left` (nucleus → paper).
  (Or rewrite directly via `apSum_sub_eq_sum_Icc` / `apSum_sub_eq_sum_Icc_mul_left` when
  starting from a difference, and `apSum_sub_apSum_eq_sum_Icc` /
  `apSum_sub_apSum_eq_sum_Icc_mul_left` when starting from `apSum … n - apSum … m` with `m ≤ n`).
  Sometimes it is useful to change viewpoint on offset sums:
  - offset ↔ affine: `apSumOffset f d m n` ↔ `apSumFrom f (m * d) d n` via `apSumOffset_eq_apSumFrom`.
  - shifted-sequence offset ↔ affine tail:
    `apSumOffset (fun k => f (k + a)) d m n` ↔ `apSumFrom f (a + m * d) d n` via
    `apSumFrom_tail_eq_apSumOffset_shift_add` / `apSumOffset_shift_add_eq_apSumFrom_tail`.
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
  For affine *tails* `apSumFrom f (a + m*d) d n`, you can split by length using the tail-focused lemmas
  `apSumFrom_tail_succ_length`/`apSumFrom_tail_succ_length_add_left` (head+tail) and
  `apSumFrom_tail_succ`/`apSumFrom_tail_succ_add_left` (append-one-term).
  For a homogeneous-sum view (shift the sequence, keep the step size `d`), rewrite
  - `apSumFrom f a d n` ↦ `apSum (fun k => f (k + a)) d n` via `apSumFrom_eq_apSum_shift_add`.
  - or `apSumFrom f a d n` ↦ `apSum (fun k => f (a + k)) d n` via `apSumFrom_eq_apSum_shift_add_left`.
  If you instead want to *commute the translation past the multiplication* (i.e. package the
  translation as `x ↦ f (x + a)` under the `apSum` binder), you can use the legacy names
  `apSumFrom_eq_apSum_map_add` / `apSumFrom_eq_apSum_map_add_left`.

  These are now deprecated wrappers for the canonical `apSumFrom_eq_apSum_shift_add` /
  `apSumFrom_eq_apSum_shift_add_left` lemmas.
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
  If you want to eliminate an explicit tail/offset parameter `m` by absorbing it into the
  translation constant (i.e. produce an `apSumOffset … 0 n` tail), use:
  - `apSumFrom_tail_eq_apSumOffset_shift_add_zero_m`
  - `apSumFrom_sub_eq_apSumOffset_shift_add_zero_m`
  - `apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m`
  If you want to go one step further and eliminate the now-trivial offset sum (`m = 0`) into a
  homogeneous AP sum, use:
  - `apSumFrom_tail_eq_apSum_shift_add`
  - `apSumFrom_tail_eq_apSum_shift_add_left` (if your affine start is written as `m*d + a`)
  - `apSumFrom_sub_eq_apSum_shift_add`
  - `apSumFrom_sub_eq_apSum_shift_add_left` (if you prefer the translation constant `m*d + a`)
  - `apSumFrom_add_length_eq_add_apSum_shift_add`
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
  - tails `apSumFrom f (a + m*d) d n` via `apSumFrom_tail_eq_sum_Icc`
    (or the mul-left variants `apSumFrom_tail_eq_sum_Icc_mul_left` / `apSumFrom_tail_eq_sum_Icc_mul_left_add`),
  - and differences via `apSumFrom_sub_eq_sum_Icc` / `apSumFrom_sub_apSumFrom_eq_sum_Icc`.

Discrepancy predicates / witnesses:
- Treat `HasDiscrepancyAtLeast` and `HasAffineDiscrepancyAtLeast` as normalization boundaries
  for existence statements; use the structured witness API in `Witness.lean` when convenient.
- If you want to keep witnesses structured, rewrite unbounded discrepancy to a `Nonempty` witness
  family:
  - homogeneous: `forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos`
  - affine: `forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos`
- For sign sequences, you can strengthen the length side-condition: the lemma
  `IsSignSequence.exists_affine_witness_d_ge_one_and_length_gt` shows that any witness of
  `HasAffineDiscrepancyAtLeast f C` can be chosen with `d ≥ 1` and `n > C`.
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
  - additive reindexing `x ↦ x + k`: `HasDiscrepancyAtLeast.of_shift_add`,
    `HasAffineDiscrepancyAtLeast.of_shift_add` (and sum-level rewrites like `apSum_shift_add` /
    `apSumFrom_shift_add`).
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

Regression tests for these normal-form lemmas live in `MoltResearch.Discrepancy.NormalFormExamples`.
-/

