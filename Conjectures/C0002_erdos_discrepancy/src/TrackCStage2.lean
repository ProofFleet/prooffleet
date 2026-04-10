import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Light
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output

/-!
# Track C: Stage 2 boundary (Tao 2015 plane)

This file is intentionally thin: it re-exports
- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Light` (entry point + boundary + lightweight wrappers about `stage2Out`), and
- the proved convenience lemmas about `Tao2015.Stage2Output` (from `TrackCStage2Output`),

keeping `TrackCStage2.lean` as “API + wiring”.

The conjecture stub itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry` (imported via
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Light`) so consumers can just
`import ...TrackCStage2`.
-/
