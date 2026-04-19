import MoltResearch.Discrepancy

/-!
# Discrepancy: stable-surface support-algebra regression examples

Compile-only examples under the **stable surface**

```lean
import MoltResearch.Discrepancy
```

Checklist item (Track B): Problems/erdos_discrepancy.md
- "Stable-surface regression for support algebra: add 2–3 tiny `example` blocks under `import MoltResearch.Discrepancy` showing the intended pipeline"
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (d m n k : ℕ)

  /-!
  ## Support normal forms

  These should remain one-liner rewrites that keep downstream code out of `Finset` internals.
  -/

  -- `apSupport` as the image of a range (canonical normal form).
  example : apSupport d m n = (Finset.range n).image (fun i => (m + i + 1) * d) := by
    simpa using (apSupport_eq_image_range (d := d) (m := m) (n := n))

  -- Concatenation (length add) normal form.
  example : apSupport d m (n + k) = apSupport d m n ∪ apSupport d (m + n) k := by
    simpa using (apSupport_add (d := d) (m := m) (n := n) (k := k))

  -- Cardinality bookkeeping: when `d > 0`, support has exactly `n` elements.
  example (hd : d > 0) : (apSupport d m n).card = n := by
    simpa using (card_apSupport_eq (d := d) (m := m) (n := n) hd)

end

end MoltResearch
