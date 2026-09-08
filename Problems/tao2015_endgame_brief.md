# Track R — Endgame brief (card item 202): retire the Stage-2 stub axiom; `erdos_discrepancy` from `erdos_discrepancy_unconditional`

**Ground rules:** no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`; `Conjectures/` is backlog and may be restructured, but the whole
`Conjectures` library must still typecheck (`lake build Conjectures`) and every CI target in `scripts/ci_targets.txt` must build; never edit
`PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; one commit per unit `Track R: <one line> (#3044, END-<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted. Read: `Conjectures/C0002_erdos_discrepancy/src/ErdosDiscrepancy.lean` (`erdos_discrepancy_notBounded`
→ `Tao2015.stage3_notBounded` → the Stage-2 stub), `TrackCStage2Stub.lean` (the **only axiom** in the tree: `stage2Stub_exists_params_one_le_unboundedDiscOffset`,
line ≈92, plus the class `Stage2Assumption`, `ofStage2`, `stage2Of`, and the low-priority default instance), `TrackCStage2Boundary.lean` (`Stage2Output`),
the files importing the stub (`grep -rln TrackCStage2Stub Conjectures`: `TrackCStage2Boundary`, `TrackCStage2`, `TrackCStage2ProofCore`, `Tao2015`,
`TrackCStage2StubProof`, `TrackCStage3EntryMinimal`, `TrackCStage2Entry`), `TrackCStage5PrimeLargeValuesDischarge.lean` (**`erdos_discrepancy_unconditional`**),
`TrackCAxiomAudit.lean`, `scripts/ci_targets.txt`, `Problems/tao2015_derivation_c.md` (line ≈202, the checkbox), `Conjectures/C0002_erdos_discrepancy/card.md`
(the blueprint milestones).

## Units

- **END-1 (the honest top-level theorem).** In `ErdosDiscrepancy.lean` re-prove `erdos_discrepancy_notBounded (f) (hf) : ¬ BoundedDiscrepancy f :=
  Tao2015.erdos_discrepancy_unconditional f hf` (add the import of `TrackCStage5PrimeLargeValuesDischarge`; keep the module small — if the import makes the
  Track-C hard-gate target slow, that is acceptable for the backlog, but check `scripts/ci_targets.txt` for what CI builds and keep those targets green).
  `erdos_discrepancy` and its corollaries then inherit the honest proof. Add `#print axioms` guards for `erdos_discrepancy_notBounded` and `erdos_discrepancy`
  in `TrackCAxiomAudit.lean` (standard three).
- **END-2 (retire the axiom).** Delete the axiom `stage2Stub_exists_params_one_le_unboundedDiscOffset` and the default `Stage2Assumption` instance built on
  it; move the interface (`class Stage2Assumption`, `ofStage2`, `stage2Of`, docstrings) to where its consumers can still import it (e.g. keep
  `TrackCStage2Stub.lean` as an axiom-free interface file renamed `TrackCStage2Interface.lean`, or fold it into `TrackCStage2Boundary.lean`), fix the eight
  importers, and — where a consumer needed the default instance (e.g. `stage3_notBounded`, `stage3Out`) — either supply the verified instance
  **`instance : Stage2Assumption`** built from the honest theorem if `Stage2Output f` can be constructed from `¬ BoundedDiscrepancy f` (read
  `Stage2Output`: it needs a `ReductionOutput f` and `UnboundedDiscrepancyAlong out1.g out1.d`; check whether the Stage-1/Stage-2 constructive files
  `TrackCStage2ProofCore`/`TrackCStage2StubProof` already build the output from `¬ BoundedDiscrepancy` — if they do, wire them; if not, make those consumers
  take `[Stage2Assumption]` as an explicit hypothesis instead of using a default instance, and make sure nothing on the path to `erdos_discrepancy` uses
  the class any more). The tree must contain **no `axiom` declaration anywhere** after END-2 (`grep -rn "^axiom" --include=*.lean .` returns nothing);
  `lake build Conjectures` and every CI target must pass.
- **END-3 (the card and the blueprint).** In `Problems/tao2015_derivation_c.md` tick the two remaining checkboxes (the Matomäki–Radziwiłł leg — cite
  `erdos_discrepancy_unconditional`, PRs #3673–#3711, and the Phase 4/5/6 sections of `Problems/tao2015_a1_r6r7_design_report.md` — and the endgame item),
  and in `Conjectures/C0002_erdos_discrepancy/card.md` flip milestone (C) to done with a one-line pointer to the pinned theorem; update
  `Conjectures/C0002_erdos_discrepancy/notes.md` if it describes the stub.

**Verification/report:** `lake build Conjectures`; the grep gates; `python3 scripts/check_task_metadata_coverage.py`; `./scripts/check_layering.sh`;
`python3 scripts/check_aggregator_coverage.py`; `make ci` if feasible; `#print axioms` of `erdos_discrepancy` (standard three). **Stop rule:** stop only if a
consumer of the stub cannot be made axiom-free without rewriting a substantial development (record which and why) — in that case do END-1 and END-3's
Matomäki–Radziwiłł checkbox, leave the endgame checkbox open, and report.
