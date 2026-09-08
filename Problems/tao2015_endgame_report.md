# Track R — the endgame (run 30): no axiom anywhere

Card: `Problems/tao2015_derivation_c.md`, the last checkbox. Brief: `Problems/tao2015_endgame_brief.md`. Run 30 of the
Codex worker (`gpt-5.6-sol`, reasoning effort `xhigh`), branch `vex/track-r-endgame`, based on `5be5e1d2` (the run-29 docs
commit on `main`). Three commits, cherry-picked unchanged onto `main` by the shipping PR.

## Outcome

The Stage-2 stub axiom `stage2Stub_exists_params_one_le_unboundedDiscOffset` — the only `axiom` declaration in the whole tree, in
the `Conjectures/` backlog, never under `MoltResearch/` — is deleted, together with the low-priority default `Stage2Assumption`
instance built on it. The public theorem `MoltResearch.erdos_discrepancy_notBounded` (and `erdos_discrepancy` with its
corollaries) is now proved by `Tao2015.erdos_discrepancy_unconditional`, and `TrackCAxiomAudit.lean` pins both public names to
`[propext, Classical.choice, Quot.sound]` under `#guard_msgs`. After this PR, `git grep '^axiom' -- '*.lean'` returns nothing.

- **END-1** `ff753dc5` — `ErdosDiscrepancy.lean` imports `TrackCStage5PrimeLargeValuesDischarge` and re-proves
  `erdos_discrepancy_notBounded` from the unconditional theorem; two new `#print axioms` guards.
- **END-2** `c667d0b2` — the axiom and the default instance deleted; `TrackCStage2Stub.lean` kept at its import path as an
  axiom-free interface file (`class Stage2Assumption`, `stage2Of`, `stage2OutOf`); the legacy Stage-2/3 consumers
  (`stage2`, `stage2Out`, `stage3`, `stage3_notBounded`, `stage3_forall_hasDiscrepancyAtLeast`, the Stage-5 skeleton) now take
  `[Stage2Assumption]` explicitly. 22 files, −510/+152 lines: `TrackCStage2StubProof.lean` lost its stub-dependent half.
- **END-3** `3479ba85` — the endgame checkbox ticked, blueprint milestone (C) flipped in `Conjectures/C0002_erdos_discrepancy/card.md`,
  `notes.md` and `Problems/tao2015_analytic_core.md` no longer describe the stub as live.

## The one design finding (E.8)

The brief offered, as the preferred option, a verified `instance : Stage2Assumption` built from the honest theorem. The worker
declined it, correctly: `Stage2Output f` asks for **one fixed step `d`** with unbounded offsets along it, while
`¬ BoundedDiscrepancy f` only says that for every bound some pair `(d, n)` exceeds it — the step may change with the bound.
The fixed-step statement is genuinely stronger and is not what Tao's theorem gives, so no instance can be honestly derived, and
the legacy Stage-2/3 path stays an explicitly conditional interface that nothing public uses. Same class as Findings E.1–E.7:
a brief that assumed an implication which does not hold, caught by the worker's report.

## The checkbox text

The card's endgame item, written before Phase 6, said "re-prove `stage5_notBounded` from `FourierReductionStochasticAssumption` +
`theorem18`, retire the Stage-2 stub axiom, flip milestone (C)". The unconditional theorem superseded the first clause (the public
theorem no longer routes through the Stage-5 skeleton at all), so the worker rewrote the item to describe the route actually
taken and ticked that. The rewrite is deliberate and recorded here so the ledger stays honest.

## Verification (as run by the worker in its own worktree, then re-run by CI on the shipping PR)

`~/.elan/bin/lake build MoltResearch.DiscrepancyAnalytic Conjectures` (8,358 jobs) and `make ci` (8,478 jobs) passed;
`forbid_sorry`, `forbid_axiom_unsafe`, `check_layering`, `check_aggregator_coverage` (208 modules), `check_task_metadata_coverage`
(42 files) passed; `#print axioms` of `erdos_discrepancy_notBounded` and `erdos_discrepancy` gives the standard three.
Note for anyone repeating the whole-directory grep: `grep -rn '^axiom' --include=*.lean .` must exclude `.lake/` (Mathlib's
test fixtures) and any stale `.claude/worktrees/` copies; the tracked tree (`git grep`) is the statement that matters.
