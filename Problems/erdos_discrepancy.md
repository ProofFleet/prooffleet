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

- [x] Parity split (even length): `apSum f d (2*(n+1)) = apSum f (2*d) (n+1) + f d + apSumFrom f d (2*d) n`
  (Implemented as `apSum_two_mul_len_succ` in `MoltResearch/Discrepancy/Parity.lean`; regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.)

- [x] Bridge lemma (along-`d` predicate → `discOffset` witness normal form):
  `HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔ (∃ n : ℕ, C < discOffset f d m n)`.
  (Implemented as `HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt` in `MoltResearch/Discrepancy/Basic.lean`; regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.)

- [x] Range-cut normal form (discOffset-level): using `apSumOffset_eq_sum_range'`, prove a canonical lemma splitting a `discOffset`
  over `Finset.range` at a cut `k` and rewriting both pieces back to `discOffset` (so later proofs can do “cut at k” without dropping to `Int` sums).
  (Implemented as `discOffset_eq_natAbs_apSumOffset_cut` / `discOffset_cut_le` in `MoltResearch/Discrepancy/Offset.lean`; regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`.)

#### Track C — Tao2015 “build the plane” (context; Track C checklist below)

Goal: make the Tao 2015 proof **structural** before it is complete: explicitly name the reduction stages,
package their IO contracts, and add the small rewrite/transfer lemmas that let later stages compose.

- Primary file: `Conjectures/C0002_erdos_discrepancy/src/Tao2015.lean`
- Key interface (Stage 1): `Tao2015.ReductionOutput` (derived sign sequence `g`, parameters `d,m`,
  plus `apSum`/`apSumOffset` rewrite + discrepancy-transfer lemmas)
- Key deliverable (Stage 2, stubbed):
  `stage2_unbounded_discOffset : ∀ B, ∃ n, B < discOffset f out.d out.m n`

Current status notes:
- `ReductionOutput` and its rewrite/transfer glue are in place; consumers should treat it as the Stage-1 IO contract.
- Stage-1 also exposes “boundedness equivalence” glue, so consumers can freely swap between:
  - bounded fixed-step discrepancy of the reduced sequence `BoundedDiscrepancyAlong out.g out.d`, and
  - bounded offset discrepancy of the original sequence `BoundedDiscOffset f out.d out.m`.
  (This is the main contract form that Stage-2 wants to negate.)
- Stage-1 now also exposes a small *combinator API* for composing reductions: `ReductionOutput.shiftRight` packages “shift the reduced sequence again by `m₂*out.d`” as a new `ReductionOutput`, with assoc/zero simp lemmas (`shiftRight_shiftRight`, `shiftRight_zero_*`) so downstream stages can normalize nested shifts.
- Unboundedness witness normal form: use `ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt` (and friends) to flip between
  “`out.g` has unbounded discrepancy along `out.d`” and “`discOffset f out.d out.m` is unbounded”.
- Witness-normal form: downstream stages that work with affine tails can use
  `ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt` to rewrite
  `HasDiscrepancyAtLeastAlong out.g out.d C` into an explicit `apSumFrom` witness for `f`.
- Stage-2 output is already *packaged* as `Tao2015.Stage2Output` (with helper lemmas to convert between witness normal forms and negated boundedness); the actual deliverable `stage2_unbounded_discOffset` is still stubbed.
- `reduction` is still a *stub* implementation (currently the trivial `(d,m,g)=(1,0,f)` shift), so downstream stages should avoid depending on its specific parameters beyond the provided simp/bridge lemmas.

Next bite-size Track C steps (good 1-PR targets):
- Replace the `reduction` stub with the first *actually-used* reduction in Tao’s pipeline (even if the proof is `sorry`), but keep the output packaged purely via `ReductionOutput` contracts.
- Fill in `stage2_unbounded_discOffset` by wiring the existing equivalence lemmas (`UnboundedDiscrepancyAlong` / `HasDiscrepancyAtLeastAlong` / `¬Bounded…`) and leaving only the mathematical “core lemma” as a single `sorry`.
- Add a minimal `section Stage2RegressionExamples` in `Conjectures/.../Tao2015.lean` with 2–3 `example` blocks that show the intended consumer rewrite pipeline compiles (these are cheap and catch naming regressions).

Definition of done for Track C PRs:
- Only edits under `Conjectures/` (and optionally this card)
- CI green
- Interfaces improve composability (more named rewrites / transfer lemmas; fewer ad-hoc rewrites)

Quick consumption pattern (Stage 1):
- Given `hf : IsSignSequence f` and a boundedness hypothesis `hb : BoundedDiscrepancy f`, build
  `out : Tao2015.ReductionOutput f` (typically via `ReductionOutput.ofShift`).
- Immediately derive a fixed-step context for the reduced sequence:
  `ctx' : Tao2015.ContextAlong out.g out.d := out.contextAlong_ofContext (ctx := Context.ofBoundedDiscrepancy hb)`.
- When a later stage produces a witness about offsets of `f`, normalize it through the contract:
  `discrepancy out.g out.d n = discOffset f out.d out.m n` via `ReductionOutput.discrepancy_eq_discOffset`.

Stage-1 contract “cheat sheet” (most-used lemmas):
- Rewrite (sum level):
  - `ReductionOutput.apSum_eq_apSumOffset` (and the reverse `apSumOffset_eq_apSum`)
  - `ReductionOutput.apSum_eq_apSumFrom_mul` (affine-tail nucleus normal form)
- Rewrite (discrepancy level):
  - `ReductionOutput.discrepancy_eq_discOffset`
  - `ReductionOutput.discrepancy_eq_natAbs_apSumFrom_mul`
- Transfer (bounds):
  - `ReductionOutput.contract_discrepancy_le_derived` (offset bound → reduced bound)
  - `ReductionOutput.contract_discOffset_le_derived` (reduced bound → offset bound)
- Swap “boundedness vs unboundedness” normal forms:
  - `ReductionOutput.boundedDiscrepancyAlong_iff_boundedDiscOffset`
  - `ReductionOutput.unboundedDiscrepancyAlong_iff_unboundedDiscOffset`

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
- [x] Normal form: reduce summand shifts modulo the step for offset sums (`apSumOffset_shift_mod`).
- [x] Reindexing lemmas (undo `map_mul` etc. under divisibility) (`Reindex.lean`)
- [x] Scaling lemmas (multiply sequence, scale bounds)
- [x] Translation lemmas (shift indices / offset handling)

**Remaining (choose next boxes from here)**
- [x] Stability lemma: apSumOffset support / invariance under modifying f outside accessed indices
- [x] Add regression example: affine difference → offset normal form (apSumFrom_sub_eq_apSumOffset_shift_add)
- [x] Add regression example: mul-left affine difference → shifted homogeneous normal form (apSumFrom_sub_eq_apSum_shift_add_mul_left)
- [x] Write a short “normal forms” section in `MoltResearch/Discrepancy.lean` documenting preferred rewrite targets
- [x] Add a minimal set of lemmas bridging the Conjectures statement to the nucleus API (so the theorem statement reads cleanly)
- [x] Add paper→nucleus rewrite lemmas for affine difference interval sums (`sum_Icc_eq_apSumFrom_sub`, `sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le`)
- [x] Nucleus normal form: rewrite `apSumFrom f a d n` to `apSumOffset` when `a` is a multiple of `d`
- [x] Canonical quotient/remainder normal form: prove a lemma rewriting `apSumFrom f a d n` into an `apSumOffset` form using `a = (a / d) * d + (a % d)` (when `d>0`).

#### Auto-generated backlog (needs triage)
- [x] Affine: for sign sequences, a witness for `HasAffineDiscrepancyAtLeast f C` can be taken with `d ≥ 1` and `n > C`.
  - proved as `IsSignSequence.exists_affine_witness_d_ge_one_and_length_gt`
- [x] Normal form: rewrite `HasAffineDiscrepancyAtLeast f C` into an offset-sum witness `Int.natAbs (apSumOffset (fun k => f (k + a)) d 0 n) > C`.
  - proved as `HasAffineDiscrepancyAtLeast_iff_exists_apSumOffset_shift_add_zero` in `MoltResearch/Discrepancy/Affine.lean`.
- [x] Normal form: rewrite `HasDiscrepancyAtLeast f C` into an offset-sum witness `Int.natAbs (apSumOffset f d 0 n) > C`.
  - proved as `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_start` in `MoltResearch/Discrepancy/Basic.lean`.
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
- [x] Shift-composition simp lemma set: add a minimal [simp] lemma set that normalizes nested shifts in summands (`fun k => f (k + a + b)` and `fun k => f (k + (a + b))`) specifically for the nucleus rewrite pipeline, without causing simp loops.
  - Implemented as `shift_summand_add_assoc` in `MoltResearch/Discrepancy/Basic.lean` (function-level simp lemma oriented to avoid loops).
- [x] Stable surface audit: create a tiny “API surface checklist” file (or section) ensuring `import MoltResearch.Discrepancy` exposes exactly the intended normal-form lemmas (with deprecated aliases hidden behind a separate import), and add compile-time tests that fail if the surface regresses.
  - Implemented as:
    - `MoltResearch/Discrepancy/SurfaceAudit.lean` (stable surface checks)
    - `MoltResearch/Discrepancy/DeprecatedAudit.lean` (opt-in deprecated surface checks)
    - wired into CI via `MoltResearch/Discrepancy/SurfaceChecklist.lean` and `.../DeprecatedSurfaceChecklist.lean`

Definition of done:
- each PR adds 1–3 lemmas OR consolidates/normalizes existing ones
- minimal imports; prefer `import MoltResearch.Discrepancy` as stable surface

#### Auto-generated backlog (needs triage)
- [x] Add `…_congr` lemmas for nucleus sums (`apSum_congr`, `apSumOffset_congr`, `apSumFrom_congr`) with a consistent statement shape (pointwise equality of summands on the relevant range) so rewrite scripts can swap `f` under a binder without manual `simp` gymnastics.
- [x] Add “shift in start index” normal form: rewrite `apSumOffset f d (m + k) n` into `apSumOffset (fun t => f (t + k*d)) d m n` (and a translation-friendly `…_add` variant), so proofs can move offset mass between the `m` parameter and the summand shift canonically.
  - Lemmas in `MoltResearch/Discrepancy/Offset.lean`: `apSumOffset_shift_start_add`, `apSumOffset_shift_start_add_left` (and `apSumOffset_shift_start_add_mul_left`).
- [x] Add a canonical lemma relating `apSumOffset` to an explicit tail of `apSumFrom` on a shifted sequence (a two-way bridge): `apSumOffset (fun t => f (t + a)) d m n = apSumFrom f (a + (m+1)*d) d n` (or the repo’s preferred endpoint convention), with a regression example under `import MoltResearch.Discrepancy`.
  - Done via `apSumOffset_shift_add_eq_apSumFrom_tail` + doc-clarified alias `apSumOffset_shift_add_eq_apSumFrom_tail_firstTerm`; stable-surface regression landed in `MoltResearch/Discrepancy/Examples.lean` (PR #584).
- [x] Add endpoint-normalization for affine tails with variable endpoints: a small family of `…_of_le` lemmas rewriting paper sums over `Icc (a + (m+1)*d) (a + n*d)` directly into `apSumOffset` (avoid `Nat.add_comm` noise under binders; align names with the existing `sum_Icc_eq_apSumOffset_of_le` family).
  - Done in `MoltResearch/Discrepancy/AffineTail.lean` via the `sum_Icc_eq_apSumOffset_of_le_affine*` alias family (e.g. `…_affineEndpoints` / `…_mul_left`). See PRs #590–#593.
- [x] Add a “one-cut in paper notation” bridge: a lemma that splits a paper interval sum `∑ i ∈ Icc (m+1) (m+n₁+n₂), f (i*d)` into two paper sums (at `m+n₁`), then immediately rewrite both pieces to nucleus `apSumOffset`; include a regression example showing the full pipeline compiles under the stable surface.
  - Implemented as `sum_Icc_add_len_eq_apSumOffset_add` in `MoltResearch/Discrepancy/Offset.lean`.
  - Stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Add a small, stable simp lemma set for distributing `Int.natAbs` across definitional rewrites of `discrepancy` / `affineDiscrepancy` (e.g. `discrepancy_def`/`affineDiscrepancy_def` tagged `[simp]?` if safe) so downstream goals normalize to `Int.natAbs (apSum…)` without unfolding by hand.
  - Implemented via `[simp]` lemmas like `discrepancy_def`, `affineDiscrepancy_def`, and the `natAbs_apSum_*` bridge lemmas; see also `MoltResearch/Discrepancy/NormalFormExamples.lean` for regression examples.
- [x] Add a reusable “compare different steps” normal form: rewrite `apSum f (d₁*d₂) n` to `apSum (fun t => f (t*d₁)) d₂ n` (and `mul_left`/`mul_right`-friendly variants), so later multiplicative reindexing arguments can normalize step factorization canonically.
  - Done: `apSum_mul_eq_apSum_map_mul` in `MoltResearch/Discrepancy/Reindex.lean` (kept on the stable surface via `MoltResearch/Discrepancy/SurfaceAudit.lean`).
- [x] Add an API coherence pass: ensure the `apSum`/`apSumOffset`/`apSumFrom` split lemmas all have matching `simp`-friendly corollaries for `n₁=0` and `n₂=0` (so `simp` closes degenerate split goals uniformly across the three nucleus objects).

  Implemented via:
  - `apSum_add_len_zero_left` / `apSum_add_len_zero_right` in `MoltResearch/Discrepancy/Basic.lean`
  - `apSumOffset_add_len_zero_left` / `apSumOffset_add_len_zero_right` in `MoltResearch/Discrepancy/Basic.lean`
  - `apSumFrom_add_len_zero_left` / `apSumFrom_add_len_zero_right` in `MoltResearch/Discrepancy/Affine.lean`

#### Auto-generated backlog (needs triage)
- [x] Invariance API: prove `HasDiscrepancyAtLeast (fun k => -f k) C ↔ HasDiscrepancyAtLeast f C` (and the affine analogue) so sign-flips can be normalized away early.
  - Implemented as `HasDiscrepancyAtLeast_neg_iff` in `MoltResearch/Discrepancy/Basic.lean` and `HasAffineDiscrepancyAtLeast_neg_iff` in `MoltResearch/Discrepancy/Affine.lean` (both now tagged `[simp]`).
- [x] Translation normal form (witness-level): rewrite `HasDiscrepancyAtLeast (fun k => f (k + a)) C` into `∃ d n, d>0 ∧ Int.natAbs (apSumOffset (fun t => f (t + (a % d))) d (a / d) n) > C` (align with `apSumOffset_shift_start_add*`).
- [x] Normal form: add a lemma moving the offset parameter into the summand shift, e.g. `apSumOffset f d m n = apSumOffset (fun k => f (k + m*d)) d 0 n` (plus `_add`/`mul_left` variants to avoid `Nat.add_comm` noise).
  - Implemented in `MoltResearch/Discrepancy/Offset.lean` as:
    - `apSumOffset_eq_apSumOffset_shift` (`m*d + k`)
    - `apSumOffset_eq_apSumOffset_shift_add` (`k + m*d`)
    - `apSumOffset_eq_apSumOffset_shift_add_mul_left` (`k + d*m`)
- [x] Paper↔nucleus glue: add `sum_Icc_eq_apSumOffset_of_le` variants specialized to the “homogeneous tail” endpoints `Icc (m+1) (m+n)` that are `simp`-friendly under `import MoltResearch.Discrepancy` (reduce binder-commutativity churn in downstream proofs).
  - Done in `MoltResearch/Discrepancy/Offset.lean` as:
    - `sum_Icc_eq_apSumOffset_of_le_add_len` (`i * d` binder)
    - `sum_Icc_eq_apSumOffset_of_le_add_len_mul_left` (`d * i` binder)
    - plus aliases `sum_Icc_eq_apSumOffset_of_le_homogeneousTail*`
- [x] Bounding lemma (stable normal form): for `IsSignSequence f`, prove a tight canonical bound `Int.natAbs (apSumOffset f d m n) ≤ n` as a stable-surface lemma (and derive `discrepancy ≤ n`).
  - Implemented as `IsSignSequence.natAbs_apSumOffset_le` (see `MoltResearch/Discrepancy/Offset.lean`) and `IsSignSequence.discrepancy_le` (see `MoltResearch/Discrepancy/Bound.lean`).
- [x] Reindexing glue: add a canonical “factor the step” lemma family for offsets, rewriting `apSumOffset f (d₁*d₂) m n` to `apSumOffset (fun t => f (t*d₁)) d₂ m n` (with `mul_left`-friendly variants), mirroring `apSum_mul_eq_apSum_map_mul`. (Implemented in `MoltResearch/Discrepancy/Reindex.lean` via lemmas `apSumOffset_mul_eq_apSumOffset_map_mul₁₂` and `apSumOffset_mul_eq_apSumOffset_map_mul_left`.)
- [x] Stable-surface coherence: add a short compile-time test file ensuring the preferred normal-form lemmas for the above invariance/translation/reindexing live under `import MoltResearch.Discrepancy` (and deprecated aliases stay opt-in).

#### Auto-generated backlog (needs triage)
- [x] Normal-form API: add a canonical lemma rewriting `apSumOffset f d m n` into a `Finset.range n` sum with summand `fun i => f ((m+i+1)*d)` (and a translation-friendly `…_add` variant), so downstream bounds can avoid `Icc` bookkeeping.
  - Implemented in `MoltResearch/Discrepancy/Offset.lean` as `apSumOffset_eq_sum_range` and `apSumOffset_eq_sum_range_add`.
- [x] Endpoint-coherence pass: add a small, consistent family of lemmas normalizing affine endpoints `a + (m+1)*d` ↔ `a + d*(m+1)` and `a + (m+n)*d` ↔ `a + m*d + n*d`, tagged so `simp` reduces binder-level `Nat` ring-noise in rewrite pipelines.
  - Implemented in `MoltResearch/Discrepancy/Affine.lean` (`add_mul_succ_norm`, `add_mul_add_norm` + reverses) and opt-in simp rules in `MoltResearch/Discrepancy/AffineEndpointSimp.lean`.
- [x] Difference→tail→offset pipeline: add `apSumFrom_sub_eq_apSumOffset`-style lemmas specialized to the common “subtract a tail from a longer tail” shape `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁` ↦ `apSumOffset f d (m+n₁) n₂`, with stable names + regression examples.
  - Implemented in `MoltResearch/Discrepancy/Offset.lean` as:
    - `apSumOffset_sub_apSumOffset_eq_apSumOffset_add_len`
    - plus rewrite-normal-form variants `apSumOffset_sub_eq_apSumOffset_shift_add` / `apSumOffset_sub_eq_apSum_shift_add` (and `*_mul_left` variants)
- [x] Reindexing glue (injective map): add a lemma that reindexes `apSumOffset` along an injective affine map on indices (a controlled `Finset.map` lemma) and packages it as a nucleus-normal-form reindexing step, to reduce repeated `Finset` boilerplate.
  Implemented in `MoltResearch/Discrepancy/Reindex.lean` via lemmas `sum_range_affine_reindex`, `affineEmbedding`, `apSumOffset_reindex_affine`.
- [x] Invariance API (mod step): add a lemma normalizing shifts modulo the step: `apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a % d))) d (m + a / d) n` (when `d>0`), aligned with the existing witness-level translation normal form.
  - Implemented in `MoltResearch/Discrepancy/Basic.lean` as `apSumOffset_shift_mod` (with a regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`).
- [x] “Paper boundary” bridge: add a canonical lemma rewriting paper sums over `Icc (m+1) (m+n)` with summand `f (a + i*d)` directly to `apSumOffset (fun k => f (k + a)) d m n` (both `i*d` and `d*i` variants), minimizing `Nat.add_comm` churn.
  - Implemented as `sum_Icc_eq_apSumOffset_shift_add_left` and `sum_Icc_eq_apSumOffset_shift_add_left_mul_left` in `MoltResearch/Discrepancy/AffineTail.lean`.
- [x] API surface coherence: add `@[simp]` lemmas that move `Int.natAbs` through the definitional bridges `discrepancy/affineDiscrepancy` → `Int.natAbs (apSum…)` in a way that avoids simp loops, plus compile-time regression examples under `import MoltResearch.Discrepancy`.
  - Implemented in `MoltResearch/Discrepancy/Basic.lean`, `MoltResearch/Discrepancy/Affine.lean`, and `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Consolidate naming: audit the “step-one” + “mul_left/mul_right” lemma families for `apSum`/`apSumOffset`/`apSumFrom` and ensure each has exactly one preferred public name (others as deprecated aliases), with `SurfaceAudit` tests updated accordingly.
  - Stable surface: `import MoltResearch.Discrepancy` exports the canonical names (see `MoltResearch/Discrepancy/SurfaceAudit.lean`).
  - Deprecated aliases (argument-order variants, inverse orientations, mul-left wrappers) live behind `import MoltResearch.Discrepancy.Deprecated` and are compile-audited in `MoltResearch/Discrepancy/DeprecatedAudit.lean`.

#### Auto-generated backlog (needs triage)
- [x] Normal form: add a canonical lemma rewriting `apSumOffset f d m n` to a *plain* `Finset.range n` sum with summand `fun i => f ((m+i+1)*d)` **and** provide the inverse rewrite lemma (so `simp` can go both directions via `simp?`/`rw` without unfolding). Target stable names like `apSumOffset_eq_sum_range'` / `sum_range_eq_apSumOffset'` with an example under `import MoltResearch.Discrepancy`.
  - Implemented in `MoltResearch/Discrepancy/Offset.lean` as `apSumOffset_eq_sum_range'` and `sum_range_eq_apSumOffset'` (regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`).
- [x] Congruence-on-range: add `apSumOffset_congrOn` / `apSumFrom_congrOn` lemmas parameterized by a predicate `P` on indices (e.g. equality of summands for all `i` in the relevant `Icc`/`range`), so downstream proofs can replace `f` by `g` without rewriting the whole function.
  - Implemented as `apSumOffset_congrOn` in `MoltResearch/Discrepancy/Basic.lean` and `apSumFrom_congrOn` in `MoltResearch/Discrepancy/Affine.lean` (usage regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`).
- [x] Stability lemma: prove `apSumOffset` is invariant under modifying `f` outside the accessed indices, packaged as a “support” statement (e.g. if `∀ i ∈ Icc (m+1) (m+n), f (i*d) = g (i*d)` then `apSumOffset f d m n = apSumOffset g d m n`). This should be the preferred glue for later “local surgery” arguments.
  - Implemented in `MoltResearch/Discrepancy/Basic.lean` as `apSumOffset_congr_Icc` (and `apSumOffset_congr_finset_Icc`).
- [x] Step-factor coherence: add the *affine* analogue of step factorization, rewriting `apSumFrom f a (d₁*d₂) n` to `apSumFrom (fun t => f (a + (t - a) * d₁)) a d₂ n` (and `mul_left`-friendly variant `a + d₁ * (t - a)`), mirroring the existing `apSum_mul_eq_apSum_map_mul` / `apSumOffset_mul_eq_apSumOffset_map_mul…` family.
  - Implemented in `MoltResearch/Discrepancy/Reindex.lean` as `apSumFrom_mul_eq_apSumFrom_map_mul_keep_a` and `apSumFrom_mul_eq_apSumFrom_map_mul_keep_a_left`.
- [x] Translation bookkeeping: add a canonical lemma rewriting `apSumFrom f (a + b) d n` to `apSumFrom (fun t => f (t + b)) a d n` (and the corresponding “push translation into the start” inverse), so affine-start noise can be moved uniformly either into the start parameter or the summand shift.
- [x] Periodicity normal form: if `f` is periodic with period `p` (or satisfies `∀ k, f (k+p)=f k`), normalize an offset AP sum whose step is a multiple of `p` to a constant sum (implemented as `apSumOffset_mul_periodic`, with a regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`). This is high-leverage for later Fourier/character-style decompositions.
- [x] Bounding API generalization: add a lemma family for functions bounded by 1 in `Int.natAbs` (not just sign sequences), e.g. if `∀ k, Int.natAbs (f k) ≤ 1` then `Int.natAbs (apSumOffset f d m n) ≤ n`, and derive the `IsSignSequence` bound as a corollary. Keep it in nucleus form.
- [x] “Kernel lemma” for discrepancy: define `discOffset f d m n := Int.natAbs (apSumOffset f d m n)` (or prove it as a lemma-only abbreviation) and add triangle-inequality + split lemmas directly at the `discOffset` level, so later statements don’t have to carry `Int.natAbs (apSumOffset …)` everywhere.
  - Wrapper `discOffset` + concat triangle inequality: `MoltResearch/Discrepancy/Basic.lean` (`discOffset`, `discOffset_add_le`).
  - Interior-cut split inequality: `MoltResearch/Discrepancy/Offset.lean` (`discOffset_split_at_le`) + regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.

#### Auto-generated backlog (needs triage)
- [x] Canonical quotient/remainder normal form: prove a lemma rewriting `apSumFrom f a d n` into an `apSumOffset` form using `a = (a / d) * d + (a % d)` (when `d>0`), so affine starts can be normalized into “multiple-of-step + small remainder” without manual arithmetic.
  - Implemented as `apSumFrom_eq_apSumOffset_div_mod` in `MoltResearch/Discrepancy/Translate.lean`.
- [x] Provide a stable, `simp`-friendly lemma family for the `d = 1` specialization of `apSumOffset` / `apSumFrom` (rewrite to shifted `Finset.range` sums), to reduce boilerplate in later discrepancy bounds and translation arguments.
- [x] Add a `discOffset`-level split lemma: `discOffset f d m (n₁+n₂) ≤ discOffset f d m n₁ + discOffset f d (m+n₁) n₂` with a stable name and proof that does not unfold `discOffset` more than necessary (so later proofs can work at discrepancy-normal-form level).
  - Implemented as `discOffset_add_le` in `MoltResearch/Discrepancy/Basic.lean`.
- [x] Normal form: prove a lemma that moves *both* a start shift and a step factor into the summand in one rewrite (a combined “shift-start + step-one” normalization), so the rewrite pipeline can go directly to `apSumOffset (fun k => f (k*d + a)) 1 m n`-style shapes without two intermediate rewrites.
- [x] Reindexing glue: add a controlled lemma that rewrites `apSumOffset` under a bijective change-of-variables on `Finset.range` indices (implemented as `apSumOffset_reindex_range_bij` in `MoltResearch/Discrepancy/Reindex.lean`) (packaged as a nucleus API lemma, not raw `Finset`), to support later “swap parity classes / split by residue” proofs.
- [x] API coherence: add a short file of `simp` lemmas for `Nat.succ`/`Nat.pred`-style endpoint normalization specifically tailored to the nucleus sums (avoid `Nat.add_comm` churn under binders), with a compile-only regression example under `import MoltResearch.Discrepancy`.
- [x] Surface regression: add 2–3 “typical user scripts” examples that start from paper statements (Icc sums with affine endpoints + differences) and normalize to `apSumOffset` + `discOffset` bounds with a single `simp`/`rw` pipeline, and make them compile under the stable surface.
  - Implemented as compile-time regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean` (imports only `MoltResearch.Discrepancy`).
- [x] Bounding lemma generalization: introduce a small lemma family stating that if `∀ k, Int.natAbs (f k) ≤ B` then `Int.natAbs (apSumOffset f d m n) ≤ n * B` (and analogous `apSum`/`apSumFrom`), so later work can reuse the same bound pipeline beyond sign sequences.
  - Note: see `MoltResearch/Discrepancy/Bound.lean` for lemmas `natAbs_apSum_le_mul`, `natAbs_apSumOffset_le_mul`, `natAbs_apSumFrom_le_mul`.

#### Auto-generated backlog (needs triage)
- [x] Normal form: prove and `[simp]`-tag `apSumOffset f d 0 n = apSum f d n` so zero-offset goals normalize to the homogeneous API without manual rewrites.
  - Implemented in `MoltResearch/Discrepancy/Basic.lean` as `@[simp] lemma apSumOffset_zero_start`.
- [x] Normal form: prove and `[simp]`-tag `apSumFrom f 0 d n = apSum f d n`, plus a small paper↔nucleus helper lemma specialized to `a=0` so the Conjectures statement can be stated uniformly.
  - Implemented in `MoltResearch/Discrepancy/Affine.lean` as `apSumFrom_zero_start` (simp) and `apSumFrom_zero_eq_sum_Icc` / `sum_Icc_eq_apSumFrom_zero`.
- [x] Translation glue: add a direct normal-form lemma rewriting `apSumFrom f (a + m*d) d n` to `apSumOffset (fun k => f (k + a)) d m n` (and an `…_add`/`mul_left`-friendly variant) without intermediate arithmetic rearrangements.
  - Implemented as `apSumFrom_tail_eq_apSumOffset_shift_add` and `apSumFrom_tail_eq_apSumOffset_shift_add_mul_left` in `MoltResearch/Discrepancy/AffineTail.lean`.
- [x] API coherence: add the inverse normal-form lemma rewriting `apSumOffset (fun k => f (k + a)) d m n` back to an `apSumFrom` tail with the repo’s preferred endpoint convention, and ensure both directions live on the stable surface. (Implemented as `apSumOffset_shift_add_eq_apSumFrom_tail` / `apSumFrom_tail_eq_apSumOffset_shift_add`; surfaced via `import MoltResearch.Discrepancy` and audited in `MoltResearch/Discrepancy/SurfaceAudit.lean`.)
- [x] Surface regression: add 2–3 compile-only examples under `import MoltResearch.Discrepancy` showing the rewrite pipelines (see `MoltResearch/Discrepancy/SurfaceAudit.lean`)
  - `apSumFrom f 0 d (m+n) - apSumFrom f 0 d m` → `apSumOffset f d m n` → split/bound, and
  - `apSumOffset f d 0 n` → `apSum f d n` → step-one normalization,
  to catch simp/namespace regressions early.
- [x] Naming audit: ensure the new `…_zero`/`…_zero_start` lemmas follow the existing `apSum_zero/apSum_one` naming scheme across `apSum`, `apSumOffset`, and `apSumFrom` (with deprecated aliases isolated behind `MoltResearch.Discrepancy.Deprecated`).
  - Verified stable surface provides: `apSum_zero/apSum_one`, `apSumOffset_zero/apSumOffset_one/apSumOffset_zero_start`, `apSumFrom_zero/apSumFrom_one/apSumFrom_zero_start`.
  - Verified legacy aliases (`*_zero_n`, `*_zero_m`, `*_zero_a`, etc.) live only in `MoltResearch.Discrepancy.Deprecated` and are guarded by `Discrepancy/SurfaceAudit.lean` absence checks.
- [x] Stable-surface audit: update `MoltResearch/Discrepancy/SurfaceAudit.lean` to assert the above normal-form lemmas are exported by `import MoltResearch.Discrepancy` (and add a companion check that deprecated aliases are not).

#### Auto-generated backlog (needs triage)
- [x] Residue-class split normal form: a lemma family splitting `apSum`/`apSumOffset` into a sum of `r` smaller AP sums by reindexing `i = r*q + j` (with both `i*d` and `d*i` summand orders), plus a regression example under `import MoltResearch.Discrepancy`.
  - Implemented in `MoltResearch/Discrepancy/Residue.lean` as `apSum_mul_len_succ_eq_sum_range`, `apSumOffset_mul_len_succ_eq_sum_range`, plus the `*_mul_left` variants; regression examples live in `MoltResearch/Discrepancy/NormalFormExamples.lean` (importing the stable surface `MoltResearch.Discrepancy`).
- [x] Lipschitz-in-length: prove a canonical “one-step extension” lemma `apSumOffset f d m (n+1) = apSumOffset f d m n + f ((m+n+1)*d)` (and `apSum`/`apSumFrom` analogues), and derive `Int.natAbs (apSumOffset … (n+1)) ≤ Int.natAbs (apSumOffset … n) + 1` for sign sequences.
  - Implemented as `apSumOffset_succ` + `apSum_succ` + `apSumFrom_succ`, and the sign-sequence bound `IsSignSequence.natAbs_apSumOffset_succ_le` (see `MoltResearch/Discrepancy/Basic.lean` / `MoltResearch/Discrepancy/Affine.lean`).
  - Stable-surface regression examples live in `MoltResearch/Discrepancy/NormalFormExamples.lean` (imports only `MoltResearch.Discrepancy`).
- [x] Disc-level API coherence: introduce `disc (f d n) : ℕ := Int.natAbs (apSum f d n)` (homogeneous analogue of `discOffset`) and port the existing split/triangle/bound lemmas to `disc` with stable names mirroring `discOffset_*`.
  - Implemented in `MoltResearch/Discrepancy/Basic.lean` (core API + bounds) and `MoltResearch/Discrepancy/Offset.lean` (`disc_split_at_le`); stable-surface regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] “Support finset” normal form: define `apSupport d m n : Finset ℕ` (the accessed indices `{(m+i+1)*d | i < n}`) and prove `apSumOffset_congr`/stability lemmas phrased as equality on `apSupport` (so later local-surgery arguments don’t need `Icc` bookkeeping).
  - Implemented in `MoltResearch/Discrepancy/Basic.lean` (`apSupport`, `mem_apSupport_of_lt`, `apSumOffset_congr_support`, `apSum_congr_support`), with stable-surface regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Step-factoring for affine tails (API shape): add a canonical lemma rewriting `apSumFrom f a (d₁*d₂) n` into an `apSumOffset` normal form on a shifted sequence when `a` is a multiple of `d₂` (so affine starts + factored steps normalize in one hop).
  - Implemented in `MoltResearch/Discrepancy/Reindex.lean` as `apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul` (plus wrappers `_right` and `apSumFrom_mul_step_eq_apSumOffset_shift_mul_of_dvd`); see PR #1383.
- [x] One-cut in `Finset.range` normal form: a lemma splitting `apSumOffset` written as a `Finset.range` sum (via `apSumOffset_eq_sum_range'`) at a cut `k`, producing two `range` sums and immediately rewriting both back to nucleus `apSumOffset`; include a stable-surface regression example.
  - Implemented as `sum_range_add_len_eq_apSumOffset_add` in `MoltResearch/Discrepancy/Offset.lean`, with stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] “Swap start shift vs summand shift” coherence: prove a two-way lemma family normalizing between `apSumOffset (fun t => f (t + a)) d (m+b) n` and `apSumOffset (fun t => f (t + (a + b*d))) d m n` with a preferred public name + deprecated aliases isolated.
  - Implemented in `MoltResearch/Discrepancy/Offset.lean` as `apSumOffset_shift_add_add_offset_eq` and its inverse `apSumOffset_shift_add_shift_add_eq_apSumOffset_shift_add_add_offset`, with stable-surface regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Bounded-by-B generalization for affine tails: lemma `natAbs_apSumFrom_add_sub_apSumFrom_le_mul` (in `MoltResearch/Discrepancy/Bound.lean`) bounds `Int.natAbs (apSumFrom f a d (m+n) - apSumFrom f a d m) ≤ n * B` under `∀k, Int.natAbs (f k) ≤ B`.

#### Auto-generated backlog (needs triage)
- [x] DiscOffset-level succ/Lipschitz API: add the canonical step lemma
  `discOffset f d m (n+1) ≤ discOffset f d m n + 1` (and the corresponding equality for `apSumOffset`), plus `simp`-friendly corollaries.
- [x] DiscOffset-level stability: a lemma stating `discOffset f d m n = discOffset g d m n` if `f` and `g` agree on the accessed indices (prefer phrasing via `apSupport` or `Finset.range` normal form), so later “local surgery” arguments can stay at discrepancy level.
- [x] Coherence lemma: expose a stable normal form `discOffset f d m 0 = 0` and `discOffset f d m 1 = Int.natAbs (f ((m+1)*d))` (and affine/homogeneous analogues) to reduce degenerate-case boilerplate in later bounds. (Done: `MoltResearch/Discrepancy/Basic.lean`, sections `discOffset_degenerate` and `disc_degenerate`.)
- [x] Reindex-by-residue infrastructure: introduce a small helper API that packages the standard change of variables `i = r*q + j` as a reusable `Finset`/`Nat` reindexing lemma (separate from the final residue-class split lemma), to keep later residue-splitting PRs short and uniform. (Implemented as `sum_range_mul_reindex_div_mod` in `MoltResearch/Discrepancy/Reindex.lean`, with a stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.)
- [x] Disc-level “factor the step” coherence: add `discOffset_mul_eq_discOffset_map_mul…` lemmas (mirroring `apSumOffset_mul_eq_apSumOffset_map_mul…`) so later statements can stay in `ℕ` discrepancy form without unfolding `Int.natAbs`.
  - Implemented in `MoltResearch/Discrepancy/Reindex.lean` as `discOffset_mul_eq_discOffset_map_mul₁₂` and `discOffset_mul_eq_discOffset_map_mul_left` (plus `discOffset_map_mul`), with a stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Stable-surface regression examples: add 2–3 compile-only examples that start from paper `Icc` statements, normalize to `discOffset` (not `Int.natAbs (apSumOffset …)`), then split/bound — ensuring the whole pipeline works under `import MoltResearch.Discrepancy`.
  - Implemented as a dedicated section in `MoltResearch/Discrepancy/NormalFormExamples.lean` (imports only `MoltResearch.Discrepancy`).
- [x] API hygiene: create a tiny `DiscOffsetSimp` opt-in module with the minimal `[simp]` set for `discOffset`/`disc` normal forms (succ/zero/shift), audited so it doesn’t cause loops.
  - Implemented as opt-in module `MoltResearch/Discrepancy/DiscOffsetSimp.lean` with regression examples in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Bridge lemma: a canonical rewrite from `HasDiscrepancyAtLeastAlong` (or the repo’s preferred “along d” predicate) directly into a `discOffset` witness normal form, so Stage-2 statements can be phrased purely in `discOffset` without unpacking `Int.natAbs`.
  - Implemented as `HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt` in `MoltResearch/Discrepancy/Basic.lean`, with a stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.

#### Auto-generated backlog (needs triage)
- [x] DiscOffset witness normal form: rewrite `HasDiscrepancyAtLeast f C` directly into `∃ d n, discOffset f d 0 n > C` (stable lemma on the `discOffset` API; avoid exposing `Int.natAbs (apSumOffset …)` in downstream statements).
  - Implemented as `HasDiscrepancyAtLeast_iff_exists_discOffset_zero_start` in `MoltResearch/Discrepancy/Basic.lean`, with a stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`. 
- [x] Range-cut normal form (discOffset-level): using `apSumOffset_eq_sum_range'`, prove a canonical lemma splitting a `discOffset` over `Finset.range` at a cut `k` and rewriting both pieces back to `discOffset` (so later proofs can do “cut at k” without dropping to `Int` sums).
  - Implemented as `discOffset_eq_natAbs_apSumOffset_cut` (and the length-form `discOffset_add_len_eq_natAbs_apSumOffset_add`) in `MoltResearch/Discrepancy/Offset.lean`, with stable-surface regression example in `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- [x] Residue-class split (offset → r tracks): for `r>0`, split `apSumOffset f d m n` (and `discOffset`) into a sum over residue classes `j < r` via reindexing `i = r*q + j` (provide both `i*d` and `d*i` summand-order variants), with a stable-surface regression example under `import MoltResearch.Discrepancy`.
- [ ] `disc` API (homogeneous discrepancy): define `disc f d n := Int.natAbs (apSum f d n)` (or a lemma-only abbreviation) and port the key `discOffset_*` lemmas (`*_add_le`, `*_split_at_le`, stability) to `disc` with consistent names, so later stages can stay in `ℕ` discrepancy form.
- [ ] Disc-level step-factor coherence: add `discOffset_mul_eq_discOffset_map_mul…` lemmas mirroring `apSumOffset_mul_eq_apSumOffset_map_mul…`, so multiplicative reindexing arguments can remain at discrepancy level without unfolding `Int.natAbs`.
- [ ] `DiscOffsetSimp` hygiene pass: create an opt-in simp module for `discOffset`/`disc` with just the non-looping normal forms (`zero/one/succ`, `shift`, `mul` coherence), and add compile-time regression examples that use `simp` to normalize typical goals.
- [ ] Stability at discrepancy level (apSupport-driven): prove `discOffset f d m n = discOffset g d m n` assuming `f` and `g` agree on the accessed indices (prefer phrasing via `apSupport` or the `Finset.range` normal form); include a stable-surface example showing local surgery works without `Icc` bookkeeping.
- [ ] Endpoint/coherence bridge for Stage-2: add a canonical lemma rewriting `UnboundedDiscrepancyAlong`/`HasDiscrepancyAtLeastAlong` into a `∀ C, ∃ n, C < discOffset f d m n` normal form (quantifier-level, `discOffset`-native), so Stage-2 statements can be phrased purely in the nucleus API.

#### Auto-generated backlog (needs triage)
- [ ] Quantifier normal form (boundedness, discOffset-native): prove `BoundedDiscOffset f d m B ↔ ∀ n, discOffset f d m n ≤ B` with a stable lemma name (so later stages avoid unfolding defs).
- [ ] Quantifier normal form (unboundedness, discOffset-native): prove `¬BoundedDiscOffset f d m ↔ ∀ B, ∃ n, B < discOffset f d m n` (the negation-pushed form Stage-2 wants).
- [ ] Along-d API coherence: define a lightweight abbreviation (or lemma-only normal form) `discAlong f d n := discOffset f d 0 n` and add rewrite lemmas bridging it to `discrepancy f d n` / `HasDiscrepancyAtLeastAlong` so downstream files can stay entirely in the `ℕ` discrepancy API.
- [ ] `discOffset` step-one normalization: add lemmas rewriting `discOffset f d m n` to `discOffset (fun k => f (k*d)) 1 m n` (and `mul_left`-friendly variants), mirroring `apSumOffset`’s `…_step_one` family.
- [ ] `discOffset` step-factor coherence: port the existing `apSumOffset_mul_eq_apSumOffset_map_mul…` family to `discOffset` with stable names, so multiplicative reindexing arguments can remain at discrepancy level.
- [ ] Range-form stability at discrepancy level: using `apSumOffset_eq_sum_range'`, prove `discOffset f d m n = discOffset g d m n` assuming pointwise agreement of summands on `Finset.range n` (no `Icc` endpoints), and add a stable-surface regression example.
- [ ] Stage-2 bridge: a lemma rewriting `HasDiscrepancyAtLeast f C` directly into a `discOffset` witness `∃ d n, discOffset f d 0 n > C` (stable name; avoid exposing `Int.natAbs (apSumOffset …)` downstream).
- [ ] “Consumer regression” examples: add 2–3 compile-only `example` blocks under `import MoltResearch.Discrepancy` that start from the Stage-2 goal shape (`∀ B, ∃ n, B < discOffset …`) and normalize through the preferred rewrite pipeline without unfolding.

#### Auto-generated backlog (needs triage)
- [ ] Boundedness API hygiene: add monotonicity + transport lemmas for `BoundedDiscOffset` / `BoundedDiscrepancyAlong` (e.g. `mono_B`, `mono_len`, and `map` lemmas that push along `apSumOffset_eq_apSumOffset_shift_add`), so later stages can move between equivalent boundedness hypotheses without unfolding.
- [ ] Residue-splitting helper infra: factor out a tiny `Finset.range` reindexing lemma bundle for `i = r*q + j` (with `q < (n+j)/r` bounds packaged), so the eventual residue-class split PRs don’t each rebuild the arithmetic boilerplate.
- [ ] Residue-class split (homogeneous, nucleus): prove `apSum f d n` splits into `∑ j < r, apSum (fun q => f ((r*q + j)*d)) (r*d) ?` (choose the repo’s preferred normal form) with both `i*d` and `d*i` variants, plus a stable-surface regression example.
- [ ] DiscOffset-level sign/shift invariances: port the existing `apSumOffset` invariance lemmas to the `discOffset` API (`discOffset (fun k => -f k) = discOffset f`, and `discOffset (fun k => f (k + a*d)) d m n = discOffset f d (m+a) n`), with careful simp orientation to avoid loops.
- [ ] `discOffset` congruence-on-support: once `apSupport` exists (or via `Finset.range` normal form), add a canonical lemma `discOffset_congr` stating equality when `f` and `g` agree on accessed indices, so later local-surgery arguments stay purely in `ℕ` discrepancy form.
- [ ] Range-form cut lemma (sum level): using `apSumOffset_eq_sum_range'`, add a canonical lemma splitting `apSumOffset` written as a `Finset.range` sum at `k`, rewriting both pieces back to nucleus `apSumOffset` (not just an inequality), with a stable-surface regression example.
- [ ] Along-d convenience API: add `discAlong f d n := discOffset f d 0 n` (or the repo’s preferred abbreviation) plus a minimal lemma family that rewrites `HasDiscrepancyAtLeastAlong` into a `discAlong` witness, so Stage-2 statements can avoid explicit `m=0` bookkeeping.
- [ ] Coherence pass: add a small `DiscSimp`/`DiscOffsetSimp` opt-in module audited for non-looping simp rules (`zero/one/succ`, step-one, shift-start), plus compile-only examples that demonstrate the intended `simp`-first normalization pipeline.

#### Auto-generated backlog (needs triage)
- [ ] Define `apSupport d m n : Finset ℕ := (Finset.range n).image (fun i => (m+i+1)*d)` (or the repo’s preferred endpoint convention) and prove the basic API: `mem_apSupport_iff`, `apSupport_card` (for `d>0`), and monotonicity in `n`.
- [ ] Prove the core injectivity lemma used by support/reindexing arguments: for `d>0`, the map `i ↦ (m+i+1)*d` is injective on `Finset.range n` (and a `mul_left`-friendly variant `d*(m+i+1)`). Package it as a nucleus lemma (not raw arithmetic).
- [ ] DiscOffset stability (support-driven): prove `discOffset f d m n = discOffset g d m n` assuming `∀ x ∈ apSupport d m n, f x = g x` (and surface it under `import MoltResearch.Discrepancy`).
- [ ] DiscOffset shift-start coherence: port `apSumOffset_shift_start_add` to discrepancy level, i.e.
  `discOffset f d (m+k) n = discOffset (fun t => f (t + k*d)) d m n` (with an `_add`/`mul_left` variant to avoid `Nat.add_comm` noise).
- [ ] DiscOffset periodicity corollary: if `f` is periodic with period `p` and `p ∣ d`, prove `discOffset f d m n = discOffset f d 0 n` (or the tight constant-sum normal form implied by periodicity), and add a stable-surface regression example.
- [ ] Bound transport API: add monotonicity/transport lemmas for `BoundedDiscOffset` under the standard normal-form rewrites (`shift_start`, `step_one`, `mul`-factor reindexing), so Stage-2 can rewrite hypotheses without unfolding.
- [ ] Stable-surface coherence pass: ensure all preferred `discOffset_*` lemmas live under `import MoltResearch.Discrepancy` (and any old/unpreferred names are moved behind `MoltResearch.Discrepancy.Deprecated`), with compile-time audit tests.
- [ ] Consumer regression examples (discOffset-native): add 2–3 compile-only `example` blocks that start from a paper `Icc` statement, normalize to `discOffset`, apply a split/triangle/bound lemma, and close with `simp`/`linarith`-style steps — all under `import MoltResearch.Discrepancy`.

### Track C — Conjecture stub + equivalences (backlog)

- [x] A clean Lean statement stub in `Conjectures/` (allowed `sorry`)
- [x] Tao2015 skeleton: derived bound lemmas from `Context.bound` (offset sums / `discOffset` / shift-add normal form)
- [x] Tao2015 “plane” interface: a first nontrivial `ReductionOutput f` packaging `(d,m,g)` plus bridge/transfer lemmas connecting `apSum g d` and `apSumOffset f d m` (lives in `Conjectures/C0002_erdos_discrepancy/src/Tao2015.lean`).
- [x] Closure: `BoundedDiscrepancy` is stable under dilation (`n ↦ n*k`).
- [ ] Prove the main theorem (long-horizon)
- [x] Alternate formulations/equivalences recorded in the card + notes
- [x] Quantifier-level normal form: define `BoundedDiscrepancy` and prove `forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy`.
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
