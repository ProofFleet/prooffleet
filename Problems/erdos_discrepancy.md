# Problem Card: Erdos discrepancy theorem

Status: active

## 0. One-line pitch

A canonical “agents at scale” benchmark: turn an open-problem-shaped statement into reusable definitions + lemmas, then (eventually) a full formal proof.

## 1. Natural language statement

Let f : N → {−1, +1}. For any constant C, there exist positive integers d and n such that

| sum_{i=1..n} f(i*d) | > C.

Equivalently: every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

Notes:
- Historically posed by Erdős; solved by Tao (2015). In this repo, it serves as a **pipeline test** and long-horizon target.

## 2. Formalization target (Lean)

Goal: a *type-correct* Lean statement (even if unproved initially).

- Target file: `Conjectures/C0002_erdos_discrepancy/src/ErdosDiscrepancy.lean`
- Definitions should land in `MoltResearch/` when reusable.

## 3. Dependencies

- Finite sums over ranges (`Finset.range`)
- Integer absolute value / natAbs
- Basic number theory (multiples)

## 4. Decomposition (mergeable sub-tasks)

### Track A — Definitions (verified artifacts)

- [x] Define `IsSignSequence (f : ℕ → ℤ)`
- [x] Define the partial sum on a homogeneous AP: `apSum f d n`
- [x] Define a predicate `HasDiscrepancyAtLeast f C`

(Implemented in `MoltResearch/Discrepancy/Basic.lean`.)

Definition of done:
- lands under `MoltResearch/Discrepancy/Basic.lean`
- compiles with **no `sorry`**

### Track B — Lemma library (verified artifacts)

Goal: build a *directed* lemma scaffold (not lemma-sprawl). Each checkbox should correspond to a reusable normal form.

#### Track B normal-form guide (what we rewrite *to*)

If you’re unsure “what shape should this lemma end in?”, default to the stable import surface:

- Prefer `import MoltResearch.Discrepancy` in downstream files.
- Prefer nucleus objects (`apSum`, `apSumOffset`, `apSumFrom`) internally.
- Rewrite to paper notation (`Finset.Icc` sums) only at statement boundaries.

Canonical shapes we try to normalize into:

- Homogeneous AP sum: `apSum f d n` (paper: `∑ i ∈ Icc 1 n, f (i*d)`).
- Offset/tail sum: `apSumOffset f d m n` (paper: `∑ i ∈ Icc (m+1) (m+n), f (i*d)`).
- Affine AP sum: `apSumFrom f a d n` (paper: `∑ i ∈ Icc 1 n, f (a + i*d)`).

A common “glue” normal form (especially when you want to use the *offset* API even for affine
statements) is to shift the sequence and rewrite affine tails/differences as an `apSumOffset`:

- Tail: `apSumFrom f (a + m*d) d n` ↦ `apSumOffset (fun k => f (k + a)) d m n`
  via `apSumFrom_tail_eq_apSumOffset_shift_add`.
- Difference: `apSumFrom f a d (m+n) - apSumFrom f a d m` ↦
  `apSumOffset (fun k => f (k + a)) d m n` via `apSumFrom_sub_eq_apSumOffset_shift_add`.

This keeps downstream algebra/bounding lemmas uniform: once everything is an `apSumOffset`, you can
split/compare/bound tails without carrying around the affine-start bookkeeping.

Two practical conventions (to reduce “almost-the-same” lemmas):

- **Translation-friendly summands:** when you see `a + i*d` vs `i*d + a`, prefer using the `…_add`
  variants (e.g. `apSumFrom_tail_eq_sum_Icc_add`, `sum_Icc_eq_apSumFrom_tail_of_le_add`) so `simp`
  doesn’t fight you on `Nat.add_comm` under binders.
- **Canonical difference normal form:** when a goal has a subtraction like
  `apSum…(m+n) - apSum…m` (or the affine analogue), rewrite it to an explicit tail sum
  (`apSum_sub_eq_apSumOffset` / `apSumFrom_sub_eq_apSumFrom_tail`) *before* doing any algebra.
  This keeps subsequent splitting/bounding lemmas in the nucleus API.

Quick start (when you just want a stable normal form and to avoid “lemma sprawl”):
- If you see paper notation, rewrite it into nucleus form using `sum_Icc_eq_apSum`,
  `sum_Icc_eq_apSumOffset`, or `sum_Icc_eq_apSumFrom`.
- If you see a difference of partial sums `apSum … (m+n) - apSum … m`, rewrite it to an offset sum
  using `apSum_sub_eq_apSumOffset`.
- If you want to “bundle the step into the summand” (step-one normalization), rewrite `apSum f d n`
  to `apSum (fun k => f (k*d)) 1 n` via `apSum_eq_apSum_step_one` (and similarly for offset/affine).

Mini playbook (common rewrite goal states)

A lot of Track B work boils down to getting the goal into one of these *canonical shapes*, and then
only doing algebra/bounds afterwards.

1) Turn an affine tail into an offset sum on a shifted sequence:

- Start: `apSumFrom f (a + m*d) d n`
- Normalize to: `apSumOffset (fun k => f (k + a)) d m n`
  via `apSumFrom_tail_eq_apSumOffset_shift_add`.

2) Turn a difference into an explicit tail (do this early):

- Start: `apSumFrom f a d (m+n) - apSumFrom f a d m`
- Normalize to: `apSumFrom f (a + m*d) d n`
  via `apSumFrom_sub_eq_apSumFrom_tail`, and optionally further to an offset-sum normal form via
  `apSumFrom_sub_eq_apSumOffset_shift_add`.

3) Eliminate the explicit tail parameter when you want a homogeneous-AP view:

- Start: `apSumOffset f d m n`
- Normalize to: `apSum (fun k => f (k + m*d)) d n`
  via `apSumOffset_eq_apSum_shift_add`.

These three steps cover most “get it into nucleus normal form” moments; they also keep downstream
proof scripts uniform (everything becomes `apSumOffset` on a shifted sequence, or a homogeneous
`apSum` when you want to use bounds that are stated that way).

Practical tip (regression tests): if you add or refactor any normal-form lemmas, prefer adding a
small `example` block under `section NormalFormExamples` in `MoltResearch/Discrepancy.lean`.
Those examples are intended to be “compile-time sanity checks” that the stable surface import
`import MoltResearch.Discrepancy` still supports the intended rewrite pipelines.

(For a curated list plus regression-test examples, see the `## Normal forms` and
`section NormalFormExamples` blocks in `MoltResearch/Discrepancy.lean`.)

Typical rewrite pipeline:

1) Paper → nucleus (normalize endpoints)
   - `sum_Icc_eq_apSum`, `sum_Icc_eq_apSumOffset`, `sum_Icc_eq_apSumFrom`.
   - For variable upper endpoints with `m ≤ n`, prefer the `_of_le` lemmas.
2) Differences → tails
   - Rewrite `apSum … (m+n) - apSum … m` to `apSumOffset … m n`.
3) Split by length (one-cut normal form)
   - `apSum_add_length`, `apSumOffset_add_length`, `apSumFrom_add_length`.
4) Only at the end: nucleus → paper
   - `apSum_eq_sum_Icc`, `apSumOffset_eq_sum_Icc`, `apSumFrom_eq_sum_Icc`.

(See `MoltResearch/Discrepancy.lean` for an expanded “normal forms” section with regression-test examples.)

**Core nucleus (definitions + basic API)**
- [x] `IsSignSequence` API: `natAbs_eq_one`, `ne_zero`, etc. (`Discrepancy/Basic.lean`)
- [x] `HasDiscrepancyAtLeast` API: monotonicity + witness extraction (`Discrepancy/Basic.lean` + `Witness.lean`)

**Homogeneous AP sums (`apSum`)**
- [x] Basic simp/succ lemmas for `apSum` (`apSum_zero`, `apSum_one`, `apSum_succ`)
- [x] Split `apSum` over lengths (`apSum_add_length`)
- [x] Algebraic lemmas (`apSum` respects add/sub/neg/mul)

**Offset AP sums (`apSumOffset`) and differences**
- [x] Relate offset sums to differences of `apSum` (`apSumOffset_eq_sub` and rewrites)
- [x] Split `apSumOffset` over lengths + first-term/succ decompositions
- [x] Algebraic lemmas (`apSumOffset` respects add/sub/neg/mul)
- [x] Bounds: `natAbs (apSumOffset …) ≤ n` and bounds for differences of AP sums

**Affine AP sums (`apSumFrom`)**
- [x] Define `apSumFrom` and basic simp lemmas (`Discrepancy/Affine.lean`)
- [x] Split over lengths (`apSumFrom_add_length`) (normal form)
- [x] Bounds for affine sums of sign sequences (carryover of triangle inequality scaffold)

**Witness structures / normalization (mergeable decomposition)**
- [x] Introduce structured witnesses + helper lemmas to normalize witness forms (`Witness.lean`)
- [x] Equivalences: witness existence ↔ `Nonempty` wrappers (to ease composition)

**Reindexing / scaling / translation (canonical transforms)**
- [x] Reindexing lemmas (undo `map_mul` etc. under divisibility) (`Reindex.lean`)
- [x] Scaling lemmas (multiply sequence, scale bounds)
- [x] Translation lemmas (shift indices / offset handling)

**Remaining (choose next boxes from here)**
- [x] Add regression example: affine difference → offset normal form (apSumFrom_sub_eq_apSumOffset_shift_add)
- [x] Add regression example: mul-left affine difference → shifted homogeneous normal form (apSumFrom_sub_eq_apSum_shift_add_mul_left)
- [x] Write a short “normal forms” section in `MoltResearch/Discrepancy.lean` documenting preferred rewrite targets
- [x] Add a minimal set of lemmas bridging the Conjectures statement to the nucleus API (so the theorem statement reads cleanly)
- [x] Add paper→nucleus rewrite lemmas for affine difference interval sums (`sum_Icc_eq_apSumFrom_sub`, `sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le`)
- [x] Nucleus normal form: rewrite `apSumFrom f a d n` to `apSumOffset` when `a` is a multiple of `d`

#### Auto-generated backlog (needs triage)
- [x] Affine: for sign sequences, a witness for `HasAffineDiscrepancyAtLeast f C` can be taken with `d ≥ 1` and `n > C`.
  - proved as `IsSignSequence.exists_affine_witness_d_ge_one_and_length_gt`
- [x] Normal form: rewrite `HasAffineDiscrepancyAtLeast f C` into an offset-sum witness `Int.natAbs (apSumOffset (fun k => f (k + a)) d 0 n) > C`.
  - proved as `HasAffineDiscrepancyAtLeast_iff_exists_apSumOffset_shift_add_zero` in `MoltResearch/Discrepancy/Affine.lean`.
- [x] Normal form: rewrite `HasDiscrepancyAtLeast f C` into an offset-sum witness `Int.natAbs (apSumOffset f d 0 n) > C`.
  - proved as `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero` in `MoltResearch/Discrepancy/Basic.lean`.
- [x] Add mul-left variant of the affine difference normal form for `m ≤ n` (rewrite `apSumFrom … n - apSumFrom … m` to a shifted `apSum` with summand `fun k => f (d * k + const)`).
  - proved as `apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left` in `MoltResearch/Discrepancy/AffineTail.lean`.
- [x] Introduce `discrepancy (f d n : …) : ℕ := Int.natAbs (apSum f d n)` and prove the basic API (bounds, simp lemmas, and `HasDiscrepancyAtLeast` witness reformulation).
- [x] Introduce `affineDiscrepancy (f a d n : …) : ℕ := Int.natAbs (apSumFrom f a d n)` and prove the basic API + reformulation for `HasAffineDiscrepancyAtLeast`.
- [x] Regression example: reindexing via `map_mul` compiles under `import MoltResearch.Discrepancy` (`apSum_map_mul`, `apSumOffset_map_mul`, `apSumFrom_map_mul`).
- [x] Regression example: translation via `map_add` compiles under `import MoltResearch.Discrepancy` (`apSumFrom_map_add`, `apSum_map_add`, plus the `_left` variants).

- [x] Normal form (two-way bridge): add lemmas `apSumFrom_eq_apSumOffset_mul_left` and `apSumOffset_eq_apSumFrom_mul_left` rewriting between `apSumFrom f (m*d) d n` and `apSumOffset (fun k => f (d*k)) 1 m n` (step-one + offset), with regression examples under `import MoltResearch.Discrepancy`.
  - Implemented in `MoltResearch/Discrepancy/Affine.lean`.
  - Regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Reindexing glue: prove a canonical lemma rewriting `apSumOffset f d m n` to `apSumOffset (fun k => f (k*d)) 1 m n` (`…_step_one`) and make it the preferred simp-normal form for proofs that want to “push the step into the summand”. (Completed: opt-in simp module `MoltResearch.Discrepancy.StepOneSimp` + regression example.)
- [x] API coherence: add a small `section` of `[simp]` lemmas for degenerate lengths (`n=0`, `n=1`) for `apSumOffset` and `apSumFrom` that match the existing `apSum_zero/apSum_one` naming, to reduce boilerplate in later bounds.
- [x] Difference normal form (affine): add the `m ≤ n` variants rewriting `apSumFrom f a d n - apSumFrom f a d m` directly to an `apSumOffset` normal form on a shifted sequence (no intermediate tail), with `…_of_le` lemma names consistent with the `sum_Icc_…_of_le` family (implemented as `apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_of_le` and `apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add_of_le` in `MoltResearch/Discrepancy/AffineTail.lean`).
- [x] Translation associativity: prove a lemma normalizing nested shifts, e.g. `apSumOffset (fun k => f (k + a)) d (m + b) n` to `apSumOffset (fun k => f (k + (a + b*d))) d m n` (and the corresponding homogeneous `apSum` version), so shift bookkeeping doesn’t proliferate.
- [x] Bounding lemma: for `IsSignSequence f`, prove a reusable inequality bounding a *difference of discrepancies* by length, e.g. `Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤ n + n'` (or a tighter canonical statement), to support later triangle-inequality pipelines.
- [x] Stable surface test: add one or two “pipeline examples” showing paper interval sums with variable endpoints (`m ≤ n`) normalize all the way to `apSumOffset` and then split via `…_add_length`, compiling under `import MoltResearch.Discrepancy`.
  - Implemented as pipeline examples in `MoltResearch/Discrepancy/NormalFormExamples.lean` (split at `k` for `m ≤ k ≤ n`).
- [x] Consolidation PR: audit the existing normal-form lemma names for `*_shift_add` vs `*_map_add` and standardize the preferred ones (keeping old names as deprecated aliases if needed), to keep the nucleus surface coherent.
  - Done in `MoltResearch/Discrepancy/Translate.lean` (shift lemmas are canonical; `*_map_add` are deprecated wrappers), plus related wrappers in `Discrepancy/Affine.lean` and `Discrepancy/Basic.lean`.

- [x] Split normal form (two-cut): add a canonical lemma splitting an offset sum at an interior cut `k` (with `m ≤ k ≤ m+n`) into two offset sums, with a stable name like `apSumOffset_split_at` and a regression example under `import MoltResearch.Discrepancy`.
  - Implemented as `apSumOffset_split_at` in `MoltResearch/Discrepancy/Offset.lean`.
  - Regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean` (imports `MoltResearch.Discrepancy`).
- [x] Triangle inequality API: prove `Int.natAbs (apSumOffset f d m (n₁+n₂)) ≤ Int.natAbs (apSumOffset f d m n₁) + Int.natAbs (apSumOffset f d (m+n₁) n₂)` (and the analogous `apSum`/`apSumFrom` statements), so later discrepancy bounds can be stated without redoing `Finset.sum` algebra.
  - Implemented as `natAbs_apSumOffset_add_le` and `natAbs_apSum_add_le` in `MoltResearch/Discrepancy/Basic.lean`, and `natAbs_apSumFrom_add_len_le` in `MoltResearch/Discrepancy/Affine.lean`.
- [x] Invariance normal form: for `IsSignSequence f`, add lemmas `discrepancy (fun k => -f k) d n = discrepancy f d n` and the shift normal form `discrepancy (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n)` (as a definitional rewrite to an `apSumOffset` on a shifted sequence), plus `simp` tags where safe.
- [x] “Step into summand” coherence: affine analogue of step-one normalization (`apSumFrom …` → step-one + shifted/offset normal form), with naming aligned to the existing `…_step_one` family.
  - Implemented as `apSumFrom_eq_apSumOffset_step_one_via_shift_add` (and `sum_Icc_eq_apSumOffset_step_one_via_shift_add`).
  - Regression examples live in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Endpoint normalization: add a small, consistent family of `…_of_le` lemmas that rewrite paper interval sums with variable endpoints (`m ≤ n`) directly into nucleus `apSumOffset`/`apSumFrom` forms without intermediate commutativity rewrites (reduce `Nat.add_comm` noise under binders).
  - Implemented in:
    - `MoltResearch/Discrepancy/Offset.lean`: `sum_Icc_eq_apSumOffset_of_le` (+ `…_mul_left` variants)
    - `MoltResearch/Discrepancy/AffineTail.lean`: `sum_Icc_eq_apSumFrom_tail_of_le` and translation-friendly `…_add` / `…_mul_left` variants
- [x] Degenerate-step API: prove and `simp`-tag the `d = 0` behavior for `apSum`, `apSumOffset`, and `apSumFrom` (and show how to rewrite such cases to a length-multiple of a constant term), so downstream proofs can safely normalize away impossible/degenerate progressions.
  - Implemented as:
    - `apSum_zero_d` and `apSumOffset_zero_d` in `MoltResearch/Discrepancy/Basic.lean`
    - `apSumFrom_zero_d` in `MoltResearch/Discrepancy/Affine.lean`
- [ ] Shift-composition simp lemma set: add a minimal [simp] lemma set that normalizes nested shifts in summands (`fun k => f (k + a + b)` and `fun k => f (k + (a + b))`) specifically for the nucleus rewrite pipeline, without causing simp loops.
- [ ] Stable surface audit: create a tiny “API surface checklist” file (or section) ensuring `import MoltResearch.Discrepancy` exposes exactly the intended normal-form lemmas (with deprecated aliases hidden behind a separate import), and add compile-time tests that fail if the surface regresses.

Definition of done:
- each PR adds 1–3 lemmas OR consolidates/normalizes existing ones
- minimal imports; prefer `import MoltResearch.Discrepancy` as stable surface

### Track C — Conjecture stub + equivalences (backlog)

- [x] A clean Lean statement stub in `Conjectures/` (allowed `sorry`)
- [ ] Prove the main theorem (long-horizon)
- [x] Alternate formulations/equivalences recorded in the card + notes
- [x] Sanity check: exhibit a sign sequence with unbounded discrepancy (constant +1 sequence)

Equivalences / surface forms (proved lemmas; use these instead of unfolding defs):
- `apSum_eq_sum_Icc` / `sum_Icc_eq_apSum` (paper interval sum ↔ nucleus `apSum`)
- `HasDiscrepancyAtLeast_iff_exists_witness_pos`
- `HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos`
- `HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos`
- `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`
- `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`
- `HasDiscrepancyAtLeast.iff_nonempty_witness` / `.iff_nonempty_witnessPos`

(See `MoltResearch/Discrepancy/Basic.lean` and `MoltResearch/Discrepancy/Witness.lean`, plus
`Conjectures/C0002_erdos_discrepancy/notes.md`.)

## 5. References / links

- Terence Tao, “The Erdős discrepancy problem” (2015)

## 6. Notes / gotchas

- Keep verified artifacts **modular**: definitions in `MoltResearch/`, open claims in `Conjectures/`.
- Don’t chase the whole proof early; win by building reusable substrate.
