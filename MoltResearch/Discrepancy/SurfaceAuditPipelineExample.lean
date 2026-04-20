import MoltResearch.Discrepancy

/-!
# Discrepancy: stable-surface rewrite pipeline example (SurfaceAudit)

This file is a **compile-only regression test** meant to lock in the intended proof-script shape
using **only** the stable surface:

```lean
import MoltResearch.Discrepancy
```

Pipeline exercised (directional):

paper affine endpoints → `discOffset` → range cut → residue split → triangle bound.

Checklist item: Problems/erdos_discrepancy.md (Track B) — API coherence SurfaceAudit pipeline.
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (a d m k q n : ℕ)

  /-- Stable-surface pipeline regression:

  1. Normalize a paper-shaped `Icc` sum into `discOffset`.
  2. Cut at length `k` (triangle inequality at `discOffset` level).
  3. Split the remaining block into residue classes mod `q` (triangle inequality bound).

  This should remain doable without importing any internal implementation modules.
  -/
  example (hq : q > 0) :
      Int.natAbs
          ((Finset.Icc (m + 1) (m + (k + q * (n + 1)))).sum (fun i => f (a + i * d))) ≤
        discOffset (fun t => f (a + t)) d m k +
          (Finset.range q).sum (fun r =>
            Int.natAbs
              ((fun t => f (a + t)) (((m + k) + r + 1) * d) +
                apSumFrom (fun t => f (a + t)) (((m + k) + r + 1) * d) (q * d) n)) := by
    -- Step 1: paper affine endpoints → nucleus `discOffset`.
    have hnorm :
        Int.natAbs
            ((Finset.Icc (m + 1) (m + (k + q * (n + 1)))).sum (fun i => f (a + i * d))) =
          discOffset (fun t => f (a + t)) d m (k + q * (n + 1)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (natAbs_sum_Icc_add_affineEndpoints_eq_discOffset (f := f) (a := a) (d := d)
          (m := m) (n := k + q * (n + 1)))

    -- Step 2: cut the `discOffset` block at `k`.
    have hcut :
        discOffset (fun t => f (a + t)) d m (k + q * (n + 1)) ≤
          discOffset (fun t => f (a + t)) d m k +
            discOffset (fun t => f (a + t)) d (m + k) (q * (n + 1)) := by
      -- `k ≤ k + q*(n+1)`.
      have hk : k ≤ k + q * (n + 1) := Nat.le_add_right _ _
      -- Apply the range-cut triangle inequality and simplify the tail length.
      simpa [Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (discOffset_cut_le (f := fun t => f (a + t)) (d := d) (m := m)
          (n := k + q * (n + 1)) (k := k) hk)

    -- Step 3: residue-class split + triangle bound on the tail.
    have hres :
        discOffset (fun t => f (a + t)) d (m + k) (q * (n + 1)) ≤
          (Finset.range q).sum (fun r =>
            Int.natAbs
              ((fun t => f (a + t)) (((m + k) + r + 1) * d) +
                apSumFrom (fun t => f (a + t)) (((m + k) + r + 1) * d) (q * d) n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (discOffset_mul_len_succ_le_sum_range_natAbs (f := fun t => f (a + t)) (d := d)
          (m := m + k) (q := q) (n := n) hq)

    -- Combine the steps.
    calc
      Int.natAbs
          ((Finset.Icc (m + 1) (m + (k + q * (n + 1)))).sum (fun i => f (a + i * d)))
          = discOffset (fun t => f (a + t)) d m (k + q * (n + 1)) := by
              simpa [hnorm]
      _ ≤ discOffset (fun t => f (a + t)) d m k +
            discOffset (fun t => f (a + t)) d (m + k) (q * (n + 1)) := hcut
      _ ≤ discOffset (fun t => f (a + t)) d m k +
            (Finset.range q).sum (fun r =>
              Int.natAbs
                ((fun t => f (a + t)) (((m + k) + r + 1) * d) +
                  apSumFrom (fun t => f (a + t)) (((m + k) + r + 1) * d) (q * d) n)) := by
              exact Nat.add_le_add_left hres _

end

end MoltResearch
