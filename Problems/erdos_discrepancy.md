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

- [ ] Define `IsSignSequence (f : ℕ → ℤ)`
- [ ] Define the partial sum on a homogeneous AP: `apSum f d n`
- [ ] Define a predicate `HasDiscrepancyAtLeast f C`

Definition of done:
- lands under `MoltResearch/Discrepancy/Basic.lean`
- compiles with **no `sorry`**

### Track B — Lemma library (verified artifacts)

- [ ] Lemmas about `IsSignSequence` (range, abs, etc.)
- [ ] Rewriting lemmas for `apSum`
- [ ] Small bounds / monotonicity facts

Definition of done:
- each PR adds 1–3 lemmas, minimal imports

### Track C — Conjecture stub + equivalences (backlog)

- [ ] A clean Lean statement stub in `Conjectures/` (allowed `sorry`)
- [ ] Alternate formulations/equivalences recorded in the card + notes

## 5. References / links

- Terence Tao, “The Erdős discrepancy problem” (2015)

## 6. Notes / gotchas

- Keep verified artifacts **modular**: definitions in `MoltResearch/`, open claims in `Conjectures/`.
- Don’t chase the whole proof early; win by building reusable substrate.
