import MoltResearch.Discrepancy

/-!
# Discrepancy: end-to-end normal-form pipeline (compile-only)

This file is intentionally **example-only**: it provides a tiny “paper-shaped” script that exercises
several parts of the stable discrepancy surface in the order they typically appear in Track B.

Pipeline (typical):

1. **Paper sum** (`Finset.Icc`)
2. **Nucleus normal form** (`discOffset` wrapper)
3. **Local edit sensitivity** (change at ≤1 sampled index)
4. **Triangle / split bound** (`discOffset_split_at_le`)

This is wired into `MoltResearch.Discrepancy.SurfaceAudit` so it cannot silently regress.
-/

namespace MoltResearch

section
  open scoped BigOperators

  /-!
  A compact “edit + split + bound” example.

  We compare two sign sequences `f` and `g` that differ at exactly one sampled index, and we bound
  the discrepancy of `g` by splitting the interval, then transport the bound to `f` via edit
  sensitivity.

  The goal is not a tight inequality; the goal is to keep the rewrite pipeline stable and
  one-screen.
  -/
  example :
      let f : ℕ → ℤ := fun _ => 1
      let g : ℕ → ℤ := fun n => if n = 4 then (-1) else 1
      -- Paper `Icc` tail-sum form rewritten into the nucleus normal form `apSumOffset`:
      (Finset.Icc (0 + 1) (0 + 6)).sum (fun i => g (i * 1)) = apSumOffset g 1 0 6 ∧
      -- End-to-end inequality: split `g`, then pay a +2 edit cost to replace `g` by `f`.
      discOffset f 1 0 6 ≤ discOffset g 1 0 3 + discOffset g 1 3 3 + 2 := by
    intro f g
    constructor
    · -- (1) Paper sum → nucleus normal form.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (apSumOffset_eq_sum_Icc (f := g) (d := 1) (m := 0) (n := 6)).symm
    · -- (2) Local edit sensitivity: `f` and `g` differ on at most one sampled index in `range 6`.
      have hf : IsSignSequence f := by
        intro n; simp [f]
      have hg : IsSignSequence g := by
        intro n
        by_cases h : n = 4 <;> simp [g, h]
      have hcard :
          ((Finset.range 6).filter (fun i => f ((0 + i + 1) * 1) ≠ g ((0 + i + 1) * 1))).card ≤ 1 := by
        -- Only `i=3` (sampled index `4`) differs.
        decide

      have h_edit : discOffset f 1 0 6 ≤ discOffset g 1 0 6 + 2 := by
        -- Apply the standard offset edit bound with `t = 1`.
        simpa using
          (IsSignSequence.discOffset_edit_le
            (hf := hf) (hg := hg) (d := 1) (m := 0) (n := 6) (t := 1) hcard)

      -- (3) Triangle/split bound on `g` at cut `k = 3`.
      have h_split : discOffset g 1 0 6 ≤ discOffset g 1 0 3 + discOffset g 1 3 3 := by
        -- `discOffset_split_at_le` expects an interior cut `m ≤ k ≤ m+n`.
        have h :=
          discOffset_split_at_le (f := g) (d := 1) (m := 0) (k := 3) (n := 6)
            (hmk := by decide) (hkn := by decide)
        -- Normalize the subtraction terms: `k - m = 3`, `m + n - k = 3`.
        simpa using h

      -- Combine: `discOffset f ≤ discOffset g + 2 ≤ (split g) + 2`.
      calc
        discOffset f 1 0 6 ≤ discOffset g 1 0 6 + 2 := h_edit
        _ ≤ (discOffset g 1 0 3 + discOffset g 1 3 3) + 2 := by
              exact Nat.add_le_add_right h_split 2
        _ = discOffset g 1 0 3 + discOffset g 1 3 3 + 2 := by
              ac_rfl

end

end MoltResearch
