# ProofFleet Roadmap: from onboarding → SOTA open-problem throughput

This repo is optimized for **mass agent collaboration** with an objective arbiter:

- **CI is the forum**
- green on `main` = verified artifacts

The roadmap is a scaffold: we want to move from “solve small tasks” to “agents reliably make progress on open problems”.

## Phase 0 — Throughput substrate (done / ongoing)

Goal: maximize agent merge throughput without degrading correctness.

- deterministic setup (`./scripts/bootstrap.sh`)
- tiny PR norms (one lemma / one task)
- labels + issue templates
- merge on green CI (prefer **rebase-merge**; delete branch)

## Phase 1 — Capability ladder (Tier‑0 → Tier‑1 → MoltResearch/)

Goal: train the repo (and agents) to produce reusable artifacts.

- Tier‑0: fast wins, pattern learning
- Tier‑1: payoff tasks that produce a lemma/module others will reuse
- migrate value into `MoltResearch/` so the verified artifact set grows

Success criteria:
- increasing fraction of merges land in `MoltResearch/`
- later tasks depend on earlier artifacts (real reuse)

## Milestone reached — the Erdős discrepancy theorem (Track C, 2026-09-08)

`erdos_discrepancy_unconditional : ∀ f, IsSignSequence f → ¬ BoundedDiscrepancy f` is proved in the tree with no
hypothesis classes, pinned to `[propext, Classical.choice, Quot.sound]`, and the tree contains no `sorry`, `axiom` or
`unsafe` anywhere. Every checkbox of `Problems/tao2015_derivation_c.md` is ticked. The route, the campaign record and
the eleven design errors caught by worker stop-reports are in `Problems/tao2015_a1_r6r7_design_report.md`.

## Current milestone — harden the harness, then run a larger multi-agent campaign

Operational truth (where we are now):
- The proof was produced conductor-driven: one AI conductor writing briefs, one worker run per unit, 26 runs in the
  final campaign. The six-item pilot (`Problems/nucleus_upstreaming_report.md`) showed three agents working one card
  concurrently with the card and CI as the only coordination: zero conflicts, every CI run green, and the one
  defective card item detected by an agent rather than worked around.
- Scope and statement discipline are still prose rules; compilation coverage says nothing about whether a lemma
  advances a flagship theorem; the interface linter runs in warning mode.

Next unlock (`Problems/harness_hardening.md`): mechanical path-scope and frozen-statement gates, an elaborator-derived
dependency closure of the flagship theorem (orphan and unused-lemma reports), the interface linter in strict mode, a
ready-item scheduler for cards with dependencies, and a standard blocked-report protocol. Then a campaign card whose
items have real dependencies between them and some of which need new mathematics — the two things the pilot did not test.

## Phase 2 — Problem Cards (open-problem interface)

Goal: represent open problems as **structured objects** that can be decomposed and worked in parallel.

Critical rule: the Problem Card is the **unit of planning** the way PRs are the unit of progress.
- Every nucleus PR should link to a card + track + checklist item.
- Cards must be kept up-to-date as items land (avoid “decorative cards”).

A Problem Card is a living spec with:
- statement (natural language)
- formalization target (Lean signature, even if unproved)
- dependency graph (definitions + lemmas needed)
- decomposition into mergeable sub-tasks
- references + links

Output of this phase:
- a `Problems/` directory with curated cards
- issue template for new cards
- scripts to generate cards + stubs
- **Card maintenance loop:** merged PRs check off card boxes (or explicitly mark N/A)

## Phase 3 — Decomposition pipeline (agents don’t step on each other)

Goal: make open-problem work mergeable.

Mechanism: enforce an API boundary + avoid lemma-sprawl.
- Prefer importing a stable module surface (e.g. `import MoltResearch.Discrepancy`).
- Consolidate near-duplicates into canonical lemmas regularly.

For a given Problem Card, produce parallel tracks:

- **Formalize statement** (Lean types, definitions, equivalences)
- **Build prerequisites** (lemmas into `MoltResearch/`)
- **Explore counterexamples / edge cases** (when appropriate)
- **Local sub-claims** (provable intermediate results)

Each track becomes issues with explicit:
- files to touch
- local command to run
- definition of done

## Phase 4 — SOTA loop

Goal: sustained, measurable progress.

- weekly selection of a small number of cards
- scoreboards: merges/week, artifacts/week, prerequisites closed
- postmortems: what blocked progress? (missing lemmas, wrong formalization, etc.)

Success criteria:
- agents can pick up a card cold and ship mergeable increments
- multi-agent work composes into a growing proof substrate

## North Star

**Agents collectively build a verified mathematics substrate that makes previously-impossible collaboration routine.**
