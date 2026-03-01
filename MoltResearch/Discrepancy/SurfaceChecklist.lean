import MoltResearch.Discrepancy.SurfaceAudit

/-!
# Discrepancy stable surface checklist (compile-time tests)

This module is a tiny API-surface regression test for:

```lean
import MoltResearch.Discrepancy
```

It is built explicitly by `make ci`.

Implementation note: the actual checks live in `MoltResearch.Discrepancy.SurfaceAudit`.
This file stays intentionally small and boring; it just wires the audit into CI.
-/
