import MoltResearch.Discrepancy

/-!
# Residue-splitting regression examples (stable surface)

This module is a small compile-time regression test for the residue-class split lemma.
It imports only the stable surface:

```lean
import MoltResearch.Discrepancy
```

It is wired into CI via `MoltResearch.Discrepancy.SurfaceChecklist`.
-/

namespace MoltResearch

section

variable (f : ℕ → ℤ) (d n : ℕ)

-- Regression: `q = 3` residue split.
example :
    apSum f d (3 * (n + 1)) =
      apSum f (3 * d) (n + 1) +
        (Finset.range (3 - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (3 * d) n) := by
  simpa using (apSum_mul_len_succ (f := f) (d := d) (q := 3) (n := n) (by decide))

end

end MoltResearch
