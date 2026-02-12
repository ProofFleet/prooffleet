import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.Const
import MoltResearch.Discrepancy.Scale
import MoltResearch.Discrepancy.Translate
import MoltResearch.Discrepancy.Reindex
import MoltResearch.Discrepancy.Bound
import MoltResearch.Discrepancy.Witness

/-!
# Discrepancy (module aggregator)

This file is the **stable import surface** for the discrepancy scaffold.

Rule of thumb:
- New reusable discrepancy artifacts should live in `MoltResearch/Discrepancy/*.lean`.
- Downstream work should prefer `import MoltResearch.Discrepancy` unless it needs a narrower import.
- Keep this aggregator small and boring: it is the API boundary.
-/
