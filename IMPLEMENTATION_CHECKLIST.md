# Implementation Checklist (iterate)

## Iteration 1 — Reduce onboarding friction + make progress legible

### A. Front door
- [x] Create + pin a GitHub issue: **Mission Board: Start Here**
- [x] Link Mission Board from README

### B. Onboarding determinism
- [x] Add CI badge to README
- [x] Add **Local commands** section to README (works even when `lake` isn’t on PATH)
- [x] Add PR/claiming rule one-liner (Tier-0 PR ok; Tier-1/Repair claim first)

### C. Progress visibility
- [x] Add Tier-0 progress counter to README (e.g., `2/20 solved`)
- [x] Keep SOLVED.md updated (already started)

### D. House style + ergonomics
- [x] Add `STYLE.md` (10 short rules)
- [x] Add `scripts/check_task.sh` to typecheck a single task file

### E. Verification
- [x] CI green on `main`

## Iteration 2 — Automation + contributor flywheel
- [x] Add weekly “Top 5 Missions” section to Mission Board
- [x] Add lightweight script to append SOLVED.md entries
- [x] Add a short FAQ (toolchain mismatch, cache, stuck workflow)

## Iteration 3 — Upgrade to “real math”
- [ ] Add a curated Tier-1 set with stronger payoff
- [ ] Start moving generalized results into `MoltResearch/`
## Iteration 2.1 — Flywheel polish
- [x] Add README note about SOLVED helper scripts
- [x] Add a pinned comment to Mission Board about weekly rotation (optional)
- [x] Consider auto-updating Tier-0 counter (script or manual cadence)

## Iteration 4 — Repo hygiene + contributor UX
- [ ] Add CODEOWNERS (optional)
- [ ] Add CODE_OF_CONDUCT (optional)
- [ ] Add issue label `claimed` and convention for stale claims (e.g., 72h)

## Iteration 5 — Make Tier-1 feel like a payoff
- [ ] Curate 5 Tier-1 tasks with real payoff; document why they matter
- [ ] Update Mission Board to include Tier-1 “spicy picks”

## Iteration 6 — Turn merges into momentum
- [ ] Add a short `NEWS.md` / changelog for weekly recap
- [ ] Create script to generate a "weekly recap" stub from merged PRs

## Iteration 7 — Start migrating value into MoltResearch/
- [ ] Introduce one non-trivial lemma/module in MoltResearch/ with docs
- [ ] Add 2 tasks that depend on it (so MoltResearch/ becomes the target)

