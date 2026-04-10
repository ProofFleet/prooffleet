import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof

/-!
# Track C: Stage 2 (lightweight import)

This file is intentionally thin: it re-exports
- the Stage-2 entry point (the conjecture stub `stage2` and deterministic name `stage2Out`),
- the Stage-2 boundary interface, and
- the tiny convenience projections/wrapper lemmas about `stage2Out` (from `TrackCStage2Proof`),

without importing the larger proved convenience-lemma library
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output`.

Consumers that want the full Stage-2 convenience layer should import
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2`.
-/
