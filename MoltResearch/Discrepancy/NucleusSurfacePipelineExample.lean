import MoltResearch.Discrepancy.NucleusSurface

/-!
# Discrepancy: nucleus-surface pipeline example (compile-only)

This file is a **compile-only regression test** meant to ensure the core “nucleus surface”
supports the intended normal-form proof-script shape while importing only:

```lean
import MoltResearch.Discrepancy.NucleusSurface
```

Pipeline exercised (directional):

paper sum → nucleus (`discOffset`) → shift/dilate → cut → residue split → triangle bound.

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — “Nucleus surface audit” consolidation.
-/

namespace MoltResearch

open scoped BigOperators

section
  variable (f : ℕ → ℤ) (a d m k q n : ℕ)

  /-- Stable nucleus-surface pipeline regression.

  1. Normalize a paper-shaped `Icc` sum into `discOffset`.
  2. Cut at length `k` (triangle inequality at `discOffset` level).
  3. Split the remaining block into residue classes mod `q` (triangle inequality bound).
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
            discOffset (fun t => f (a + t)) d (m + k) ((n + 1) * q) := by
      have hk : k ≤ k + q * (n + 1) := Nat.le_add_right _ _
      simpa [Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (discOffset_cut_le (f := fun t => f (a + t)) (d := d) (m := m)
          (n := k + q * (n + 1)) (k := k) hk)

    -- Step 3: residue-class split + triangle bound on the tail.
    have hres :
        discOffset (fun t => f (a + t)) d (m + k) ((n + 1) * q) ≤
          (Finset.range q).sum (fun r =>
            Int.natAbs
              ((fun t => f (a + t)) (((m + k) + r + 1) * d) +
                apSumFrom (fun t => f (a + t)) (((m + k) + r + 1) * d) (q * d) n)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (discOffset_mul_len_succ_le_sum_range_natAbs (f := fun t => f (a + t)) (d := d)
          (m := m + k) (q := q) (n := n) hq)

    -- Combine the steps.
    calc
      Int.natAbs
          ((Finset.Icc (m + 1) (m + (k + q * (n + 1)))).sum (fun i => f (a + i * d))) =
          discOffset (fun t => f (a + t)) d m (k + q * (n + 1)) := by
            simpa using hnorm
      _ ≤ discOffset (fun t => f (a + t)) d m k +
            discOffset (fun t => f (a + t)) d (m + k) ((n + 1) * q) := hcut
      _ ≤ discOffset (fun t => f (a + t)) d m k +
            (Finset.range q).sum (fun r =>
              Int.natAbs
                ((fun t => f (a + t)) (((m + k) + r + 1) * d) +
                  apSumFrom (fun t => f (a + t)) (((m + k) + r + 1) * d) (q * d) n)) := by
            exact Nat.add_le_add_left hres _

  /-!
  A small “dilate step” sanity check: the step-scaling wrapper should be usable under the
  nucleus surface.
  -/
  example (hq : q > 0) :
      disc (fun t => f (a + t)) (q * d) (n + 1) ≤
        disc (fun t => f (a + t)) d (q * (n + 1)) +
          (Finset.range (q - 1)).sum (fun r =>
            Int.natAbs
              ((fun t => f (a + t)) ((r + 1) * d) +
                apSumFrom (fun t => f (a + t)) ((r + 1) * d) (q * d) n)) := by
    simpa using
      (disc_mul_step_le (f := fun t => f (a + t)) (d := d) (q := q) (n := n) hq)

end

end MoltResearch

