# Tao2015 pipeline map (Track C)

This file is an **operational roadmap** for Track C: wiring up Tao2015’s reduction pipeline for Erdős discrepancy.

It is intentionally lightweight and automation-friendly.

## Finish lines (pick one when planning)

- **Pipeline finish line (engineering):** we have named stage interfaces with theorems that compose end-to-end, plus small regression examples. `Conjectures/` may still contain `sorry`, but stage boundaries are stable.
- **Theorem finish line (math):** the full Erdős discrepancy theorem is proved in Lean (no `sorry` on the critical path).

Track C is primarily targeting the **pipeline** finish line.

## Design constraints

- Prefer wiring-only files at stage boundaries (API + packaging), pushing any heavy proof content into dedicated proof files.
- Avoid global `[simp]` expansions; keep aggressive simp opt-in via `DiscSimp` / `DiscOffsetSimp`.
- When a boundary lemma is meant to be used downstream, prefer a **normal form** wrapper rather than repeated rewriting at call sites.

## Stage map (current skeleton)

Below, “output” means a Lean structure/type that packages witnesses/parameters.

### Stage 1 — discrepancy ↔ nucleus witness normal forms

**Goal:** stable normal forms that relate discrepancy / discOffset to explicit witness families.

- Primary surface: `MoltResearch/Discrepancy/*` (Track B)
- Track C consumes these as lemmas, not as proof search.

**Definition of done:** downstream stages can call a lemma that produces the witness family they need without unfolding definitions.

### Stage 2 — package nucleus witnesses at concrete parameters

**Files (indicative):** `Conjectures/C0002_erdos_discrepancy/src/TrackCStage2*.lean`

**Goal:** build a `Stage2Output` (or equivalent) that exposes:
- parameters `d`, `m`
- reduced sign sequence `g`
- one or more “witness normal forms” (e.g. `∀ C, ∃ n, natAbs (apSumOffset ...) > C` or affine-tail `apSumFrom` forms)

**Acceptance test:** a downstream lemma can:
1) take `out : Stage2Output`
2) obtain a witness family in a canonical normal form (prefer `1 ≤ d` or `d > 0` versions)
3) rewrite into the affine-tail nucleus form without manual `gt_iff_lt` churn.

### Stage 3 — expose a minimal stable consumer API

**Files (indicative):** `Conjectures/C0002_erdos_discrepancy/src/TrackCStage3*.lean`

**Goal:** Stage 3 should be mostly **wiring**:
- projections / convenience accessors
- wrapper lemmas delegating to Stage 2 APIs
- canonical existential packaging (“there exist parameters with 1 ≤ d s.t. …”)

**Acceptance test:** Stage 3 lemmas should not duplicate Stage 2 logic; they should delegate.

## Next PR-sized tasks (actionable)

1) **One page of “stage interface signatures”:** for Stage2Output/Stage3Output, list the exact exported lemmas that downstream code is supposed to call.
2) **Stable regression examples:** add 2–3 tiny examples that import only the stable surface + opt-in simp bundles and exercise the stage boundary wrappers.
3) **Eliminate duplicate normal forms:** where we have both `d > 0` and `1 ≤ d` versions, pick one canonical downstream-facing form and make the other a thin wrapper.
4) **Import boundary tightening:** ensure TrackCStage3 only imports what it needs (prefer stage APIs + specific normal-form lemmas).

## Notes for automation

When opening Track C PRs, put in the PR body header:

- Card: Problems/tao2015_pipeline.md
- Track: C
- Checklist item: <short>
