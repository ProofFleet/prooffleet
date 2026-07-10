# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

MoltResearch is a Lean 4 + Mathlib repo for mass agent collaboration on math formalization. The operating principle is **"CI is the forum"**: green CI on `main` means verified artifacts. The core invariant:

- `MoltResearch/` and `Solutions/` are **verified targets**: they must build with **no `sorry`, no `axiom`, no `unsafe`**.
- `Tasks/` and `Conjectures/` are **backlog**: they may contain `sorry` and are not imported by the default build target.

## Commands

`lake` lives at `~/.elan/bin/lake` (may not be on PATH). Pinned toolchain: see `lean-toolchain`; Mathlib revision is pinned in `lake-manifest.json` — do not run `lake update` casually (that is a deliberate action via `make update`).

```bash
./scripts/bootstrap.sh              # first-time setup: fetch Mathlib cache + build verified targets
~/.elan/bin/lake exe cache get      # fetch prebuilt Mathlib .oleans (~10 min, run once)
~/.elan/bin/lake build              # build verified targets (default target = MoltResearch lib)
make ci                             # exactly what CI checks: forbid_sorry + build + audit/regression modules
make backlog                        # typecheck the whole Tasks/ + Conjectures/ backlog
./scripts/check_task.sh Tasks/Tier0/T0_07.lean   # typecheck a single Lean file (the "single test" command)
```

**Never build Mathlib from source.** If `lake build` starts compiling thousands of `Mathlib.*` files, interrupt it and run `~/.elan/bin/lake exe cache get` first.

The default target only builds what `MoltResearch.lean` imports. CI (and `make ci`) additionally builds these standalone modules explicitly, because they can silently decay otherwise:
`MoltResearch.Discrepancy.SurfaceChecklist`, `DeprecatedSurfaceChecklist`, `SurfaceAudit`, `NormalFormExamples`.

## Architecture

- `MoltResearch/` — the canonical, verified nucleus. Key modules: `Basics.lean`, `Logic.lean`, and the `Discrepancy/` folder (Track B substrate).
  - `MoltResearch/Discrepancy.lean` is the **stable import surface** (API boundary aggregator). Downstream work should `import MoltResearch.Discrepancy`. Its module docstring documents the normal-form conventions (`apSum` / `apSumOffset` / `apSumFrom`, `_shift_add` vs `_shift_add_left` naming, paper ↔ nucleus rewrite recipes) — read it before adding Discrepancy lemmas.
  - `MoltResearch/Discrepancy/NormalFormExamples.lean` is a standalone regression-test module that imports the stable surface (deliberately *not* imported by it, to avoid a cycle). It is the rewrite-pipeline smoke test.
  - `MoltResearch/Discrepancy/Deprecated.lean` holds legacy wrapper names (e.g. `*_map_add`) kept out of the stable surface.
- `Solutions/` — solved onboarding tasks (Tier0/Tier1); verified, sorry-free.
- `Tasks/` — exercise skeletons: `Tier0/T0_*.lean`, `Tier1/T1_*.lean` (Lean, may contain `sorry`), `Repair/R_*.md` (tooling/docs tasks). Tiers have tactic budgets (spec.md): Tier-0 = intro/exact/apply/simp-level basics; Tier-1 adds rw/have/calc/by_cases.
- `Conjectures/` — conjecture cards + scratch Lean files. `Conjectures/C0002_erdos_discrepancy/src/` contains the Track C pipeline: Tao2015/Erdős discrepancy stage interfaces (`TrackCStage1..4*` files) so later proof stages can consume witnesses without unfolding.
- `Problems/` — Problem Cards, the unit of planning (natural-language statement + Lean target + checkbox decomposition). Active card: `Problems/erdos_discrepancy.md`. Tracks: B = Discrepancy substrate, C = stage pipeline.
- Root `*.lean` files (`MoltResearch.lean`, `Solutions.lean`, `Tasks.lean`, `Conjectures.lean`) are Lake library entrypoints; `Tasks`/`Conjectures` libs use globs so `lake build Tasks` typechecks the whole backlog.
- `scripts/` — CI enforcement (`forbid_sorry.sh`, `forbid_axiom_unsafe.sh`), per-file checks, and the learning/recommender tooling (`next_task_recommender.py`, `learning_dashboard.py`; solved-state = matching file exists in `Solutions/Tier{0,1}/`).

## CI rules that will fail your PR (beyond a green build)

Enforced by `.github/workflows/ci.yml`:

1. **PR metadata gate**: any PR touching `MoltResearch/` must carry these lines in the PR body (`N/A` allowed):
   ```
   Card: Problems/<card>.md
   Track: A|B|C
   Checklist item: <exact checkbox text from the card>
   ```
   If a real card/item is named, the card file must exist and the item must match a checkbox in it exactly.
2. **Overlay rule**: PRs changing a canonical module (`MoltResearch/Basics.lean`, `MoltResearch/Logic.lean`, `MoltResearch/Discrepancy/Basic.lean`) must also update `Learning/EDUCATIONAL_OVERLAYS.md`.
3. **No `sorry`/`axiom`/`unsafe`** anywhere under `MoltResearch/` or `Solutions/` (grep-based, includes comments — don't even write the word `sorry` in those trees).
4. Task metadata coverage check: `python3 scripts/check_task_metadata_coverage.py`.

## Contribution conventions

- **One lemma / one task per PR.** A good PR touches 1 file (maybe 2), adds 0–1 imports. Small diffs win.
- **Stable-surface rule**: if you add/change a lemma meant to be usable via `import MoltResearch.Discrepancy`, add a usage example to `MoltResearch/Discrepancy/NormalFormExamples.lean`.
- Prefer helper lemmas over giant `simp`/automation blobs; short comment or docstring when a proof is non-obvious.
- If you generalize a task solution, consider promoting it into `MoltResearch/`.
- Tier-1 / Repair / card items: claim the issue first (comment "I'm on this"). Tier-0: just open a PR.
- Open draft PRs early; if stuck, open a draft PR with the exact error and label it `blocked`.
- Also see `AGENTS.md` (agent protocol), `CONTRIBUTING.md` (workflow), `STYLE.md` (house rules).
