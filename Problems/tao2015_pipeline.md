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

**Stage 3 policy (agent-executable guardrails):**
- Any new Stage 3 “consumer-facing normal form” must be **Stage-2-derived**: it should be a thin wrapper provable by something like
  `by simpa [...] using (Stage2Output.<lemma> ...)`.
  If it cannot be written that way, move it **down** to Stage 2 (or to a shared normal-form file like `Tao2015Extras`).
- Every new Stage 3 wrapper must come with a **3–5 line consumer `example`** in `TrackCStage3Proof.lean` showing the downstream call-site it unlocks.
  (If you can’t write a clean example, it’s probably not a stable wrapper yet.)

## Track C checklist (PR-sized items)

Each checkbox should be doable in ~1 PR. Prefer **wiring-only** changes in stage boundary files.

### Stage 0 — make the target explicit

- [ ] Add a short “Stage interface signatures” section below listing the *canonical* downstream-facing lemmas (names + types) for Stage 2 and Stage 3.
- [ ] Add 2–3 small `example` blocks (regression) that import the intended surfaces and compile (no proof search). Keep them stable.

### Stage 1 — ReductionOutput contract (Tao2015)

- [ ] Audit `ReductionOutput` for duplicate normal forms; pick one canonical witness packaging for downstream (`1 ≤ d` vs `d > 0`) and make the other wrappers.
- [ ] Ensure all Stage-1 “rewrite” lemmas used downstream are exposed as named lemmas (no repeated rewriting at call sites).
- [ ] Add/confirm a small composition example for `ReductionOutput.shiftRight` that normalizes nested shifts.

### Stage 2 — Stage2Output boundary

- [ ] Ensure Stage2Output exposes *both* offset and affine-tail witness families in canonical form:
  - `∀ C, ∃ n, natAbs (apSumOffset ...) > C`
  - `∀ C, ∃ n, natAbs (apSumFrom f (m*d) d n) > C`
- [ ] Provide the existential packaging lemma: `∃ d m, 1 ≤ d ∧ …` (Stage 2 → consumer form).
- [ ] Tighten imports in Stage2 files: keep heavy lemmas in proof files; stage boundary should be API + packaging.

### Stage 3 — Stage3Output boundary

- [ ] Confirm Stage 3 delegates to Stage 2 (no duplicated logic); move any remaining “real content” back to Stage 2.
- [ ] Provide Stage-3 existential packaging in canonical normal form for downstream stages (prefer `1 ≤ d`).
- [ ] Provide Stage-3 consumer shortcuts (single lemma) that exposes the affine-tail witness family without unpacking outputs.

### Stage N — next stage stub(s)

- [ ] Add the next stage file stub (e.g. `TrackCStage4.lean`) that *only* imports the Stage 3 boundary and states the next interface theorem(s) as `theorem ... := by` with at most one `sorry` placeholder.
- [ ] Add a regression example showing Stage 4 can consume Stage 3 without unfolding.

## Notes for automation

When opening Track C PRs, put in the PR body header:

- Card: Problems/tao2015_pipeline.md
- Track: C
- Checklist item: <short>
