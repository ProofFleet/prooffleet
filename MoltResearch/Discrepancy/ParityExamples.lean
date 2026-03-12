import MoltResearch.Discrepancy

/-!
# Parity regression examples (stable surface)

This file is a tiny compile-time regression test for the parity-split lemma.
It intentionally imports only the stable surface:

```lean
import MoltResearch.Discrepancy
```

It is wired into CI via `MoltResearch.Discrepancy.SurfaceChecklist`.
-/

namespace MoltResearch

section

variable (f : ℕ → ℤ) (d n : ℕ)

-- Regression: parity split for even-length homogeneous AP sums.
example :
    apSum f d (2 * (n + 1)) = apSum f (2 * d) (n + 1) + f d + apSumFrom f d (2 * d) n := by
  simpa using (apSum_two_mul_len_succ (f := f) (d := d) (n := n))

end

end MoltResearch
