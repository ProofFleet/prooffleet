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
- [x] Write a short “normal forms” section in `MoltResearch/Discrepancy.lean` documenting preferred rewrite targets
- [x] Add a minimal set of lemmas bridging the Conjectures statement to the nucleus API (so the theorem statement reads cleanly)

Definition of done:
- each PR adds 1–3 lemmas OR consolidates/normalizes existing ones
- minimal imports; prefer `import MoltResearch.Discrepancy` as stable surface

### Track C — Conjecture stub + equivalences (backlog)

- [x] A clean Lean statement stub in `Conjectures/` (allowed `sorry`)
- [ ] Prove the main theorem (long-horizon)
- [ ] Alternate formulations/equivalences recorded in the card + notes

## 5. References / links

- Terence Tao, “The Erdős discrepancy problem” (2015)

## 6. Notes / gotchas

- Keep verified artifacts **modular**: definitions in `MoltResearch/`, open claims in `Conjectures/`.
- Don’t chase the whole proof early; win by building reusable substrate.
