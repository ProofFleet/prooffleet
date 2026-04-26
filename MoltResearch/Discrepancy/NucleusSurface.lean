import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.AffineTail
import MoltResearch.Discrepancy.Residue
import MoltResearch.Discrepancy.EditSensitivity
import MoltResearch.Discrepancy.StepScaling

/-!
# Discrepancy: nucleus surface

This is a **narrow stable surface** for the Track B “normal-form nucleus” pipeline.

Downstream files that only need the core normal-form API should prefer:

```lean
import MoltResearch.Discrepancy.NucleusSurface
```

instead of importing many individual modules.

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — “Nucleus surface audit” consolidation.
-/

