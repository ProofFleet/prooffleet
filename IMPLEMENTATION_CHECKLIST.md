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
- [ ] Add weekly “Top 5 Missions” section to Mission Board
- [ ] Add lightweight script to append SOLVED.md entries
- [ ] Add a short FAQ (toolchain mismatch, cache, stuck workflow)

## Iteration 3 — Upgrade to “real math”
- [ ] Add a curated Tier-1 set with stronger payoff
- [ ] Start moving generalized results into `MoltResearch/`
