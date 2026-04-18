import MoltResearch.Discrepancy

/-!
# `apSum` simp audit (stable surface)

Compile-only regression tests for the `simp` behaviour of the homogeneous nucleus `apSum`
under the stable import surface:

```lean
import MoltResearch.Discrepancy
```

Checklist item: Problems/erdos_discrepancy.md (Track B)
- Stable-surface `simp` set audit for `apSum` (homogeneous).

We keep these as `example` blocks (not new lemmas) to avoid expanding the exported API.
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (d k n : ℕ)

  /-!
  ## Zero-length

  `simp` should collapse the degenerate length case.
  -/

  example : apSum f d 0 = 0 := by
    simp

  /-!
  ## Step-one normal form

  `simp` (with the canonical normal-form lemma) should rewrite an arbitrary step size `d`
  into the step-one presentation by pushing `d` into the summand.
  -/

  example : apSum f d n = apSum (fun t => f (t * d)) 1 n := by
    simp [apSum_eq_apSum_step_one]

  /-!
  ## Dilation pull-in (product step)

  When the step is a product `d*k`, normalize by pushing `d` into the summand.
  -/

  example : apSum f (d * k) n = apSum (fun t => f (t * d)) k n := by
    simp [apSum_mul_eq_apSum_map_mul]

  /-!
  ## Reflect reindexing

  `simp` should be able to express the `Finset.range` sum defining `apSum` in reflected form.
  This is the `range`-level “reverse the order” normalization.
  -/

  example :
      apSum f d n =
        (Finset.range n).sum (fun i => f (((n - 1) - i + 1) * d)) := by
    classical
    -- `apSum` is definitionally a `Finset.range` sum; `Finset.sum_range_reflect` reverses it.
    unfold apSum
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Finset.sum_range_reflect (f := fun i => f ((i + 1) * d)) n).symm

end

end MoltResearch
