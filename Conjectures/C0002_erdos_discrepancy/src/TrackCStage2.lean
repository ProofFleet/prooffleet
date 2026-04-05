import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output

/-!
# Track C: Stage 2 boundary (Tao 2015 plane)

This file is intentionally thin: it re-exports
- the Stage-2 entry point (the conjecture stub `stage2` and deterministic name `stage2Out`),
- the Stage-2 boundary interface,
- the tiny convenience projections/wrapper lemmas about `stage2Out` (from `TrackCStage2Proof`), and
- the proved convenience lemmas about `Tao2015.Stage2Output`,

keeping `TrackCStage2.lean` as “API + wiring”.

The conjecture stub itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry` and is imported here so consumers can
just `import ...TrackCStage2`.
-/
