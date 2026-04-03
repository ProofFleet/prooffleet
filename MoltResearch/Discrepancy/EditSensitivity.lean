import MoltResearch.Discrepancy.Basic

/-!
# Local edit sensitivity (sum level)

This file contains Track B lemmas controlling how much an arithmetic-progression sum can change
when you modify a sign sequence on only a few indices.

Checklist item: Problems/erdos_discrepancy.md (Track B)
- Local edit sensitivity (sum-level): if `f` and `g` differ on at most `t` indices of the relevant
  `Icc`/`range`, prove a canonical bound.
-/

namespace MoltResearch

/-- Pointwise bound: if `f` and `g` are sign sequences, then `|f n - g n| ≤ 2`. -/
lemma IsSignSequence.natAbs_sub_le_two {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (n : ℕ) :
    Int.natAbs (f n - g n) ≤ 2 := by
  rcases hf n with hn | hn <;> rcases hg n with hm | hm <;> simp [hn, hm]

/-- **Local edit sensitivity (sum level, range form).**

For sign sequences `f,g`, the absolute difference of the homogeneous AP sums is controlled by the
number of indices in `Finset.range n` where the sampled values differ.

This is a canonical “count-the-edits” bound intended to be used after normalizing sums into
`Finset.range` form.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (sum-level).
-/
lemma IsSignSequence.natAbs_apSum_sub_apSum_le_two_mul_card_range_diff {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d n : ℕ) :
    Int.natAbs (apSum f d n - apSum g d n) ≤
      2 * ((Finset.range n).filter (fun i => f ((i + 1) * d) ≠ g ((i + 1) * d))).card := by
  classical
  -- Expand the subtraction to a single `Finset.range` sum.
  have hsub : apSum f d n - apSum g d n =
      (Finset.range n).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) := by
    simp [apSum, Finset.sum_sub_distrib]

  -- Replace the full sum by the filtered sum (the summand is 0 when `f=g` at that index).
  let p : ℕ → Prop := fun i => f ((i + 1) * d) ≠ g ((i + 1) * d)
  have hfilter :
      (Finset.range n).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) =
        ((Finset.range n).filter p).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) := by
    -- Use the standard `sum_filter` normal form.
    -- `(range n).filter p` sums the same because the summand is 0 when `p` is false.
    --
    -- `sum_filter` says:
    --   `(s.filter p).sum h = s.sum (fun x => if p x then h x else 0)`.
    -- We prove the original sum equals the `if`-version, then rewrite using `sum_filter`.
    have hif :
        (Finset.range n).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) =
          (Finset.range n).sum (fun i => if p i then (f ((i + 1) * d) - g ((i + 1) * d)) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hp : p i
      · simp [hp]
      · -- If `f=g` at this index, the summand is `0`.
        have : f ((i + 1) * d) = g ((i + 1) * d) := by
          exact by simpa [p] using hp
        simp [hp, this]
    -- Now rewrite the RHS using `sum_filter`.
    -- `sum_filter` gives the filtered sum equals the if-sum, so we use it in reverse.
    have hsum_filter :
        ((Finset.range n).filter p).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) =
          (Finset.range n).sum (fun i => if p i then (f ((i + 1) * d) - g ((i + 1) * d)) else 0) := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter (s := Finset.range n)
          (p := p) (f := fun i => (f ((i + 1) * d) - g ((i + 1) * d))))
    -- Combine.
    exact (hif.trans hsum_filter.symm)

  -- Apply triangle inequality + pointwise bound `≤ 2` on the filtered sum.
  -- A small helper: triangle inequality for `Int.natAbs` over `Finset.sum`.
  have natAbs_sum_le_sum_natAbs {α : Type} (s : Finset α) (h : α → ℤ) :
      Int.natAbs (s.sum h) ≤ s.sum (fun a => Int.natAbs (h a)) := by
    classical
    refine Finset.induction_on s ?h0 ?hstep
    · simp
    · intro a s ha hs
      -- `|h a + sum h| ≤ |h a| + |sum h| ≤ |h a| + sum |h|`.
      have h1 : Int.natAbs (h a + s.sum h) ≤ Int.natAbs (h a) + Int.natAbs (s.sum h) := by
        simpa [add_comm, add_left_comm, add_assoc] using (Int.natAbs_add_le (h a) (s.sum h))
      have h2 : Int.natAbs (s.sum h) ≤ s.sum (fun b => Int.natAbs (h b)) := hs
      have h3 : Int.natAbs (h a) + Int.natAbs (s.sum h) ≤
          Int.natAbs (h a) + s.sum (fun b => Int.natAbs (h b)) := by
        exact Nat.add_le_add_left h2 _
      -- Reassociate the RHS into a `Finset.sum`.
      simpa [Finset.sum_insert ha, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.le_trans h1 h3)

  have htri :
      Int.natAbs (((Finset.range n).filter p).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d)))) ≤
        ((Finset.range n).filter p).sum (fun i => Int.natAbs (f ((i + 1) * d) - g ((i + 1) * d))) := by
    simpa using
      (natAbs_sum_le_sum_natAbs ((Finset.range n).filter p)
        (fun i => (f ((i + 1) * d) - g ((i + 1) * d))))

  have hpt : ∀ i, Int.natAbs (f ((i + 1) * d) - g ((i + 1) * d)) ≤ 2 := by
    intro i
    simpa [sub_eq_add_neg] using (IsSignSequence.natAbs_sub_le_two (hf := hf) (hg := hg) ((i + 1) * d))

  have hsum_le :
      ((Finset.range n).filter p).sum (fun i => Int.natAbs (f ((i + 1) * d) - g ((i + 1) * d))) ≤
        ((Finset.range n).filter p).card * 2 := by
    -- A `Nat`-sum bounded termwise by `2`.
    exact Finset.sum_le_card_nsmul _ _ 2 (by intro i hi; simpa using (hpt i))

  -- Put everything together.
  -- Note: rewrite the RHS into `2 * card` for consistency.
  have :
      Int.natAbs (apSum f d n - apSum g d n) ≤ ((Finset.range n).filter p).card * 2 := by
    -- Rewrite to the filtered sum, then chain inequalities.
    simpa [hsub, hfilter] using Nat.le_trans htri hsum_le

  -- Normalize `card * 2` to `2 * card`.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, p] using this

/-- Convenience corollary: if `f,g` differ on at most `t` sampled indices, then
`|apSum f d n - apSum g d n| ≤ 2*t`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (sum-level).
-/
lemma IsSignSequence.natAbs_apSum_sub_apSum_le_two_mul_of_card_range_diff_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((i + 1) * d) ≠ g ((i + 1) * d))).card ≤ t) :
    Int.natAbs (apSum f d n - apSum g d n) ≤ 2 * t := by
  have h :=
    IsSignSequence.natAbs_apSum_sub_apSum_le_two_mul_card_range_diff (hf := hf) (hg := hg) (d := d)
      (n := n)
  exact le_trans h (Nat.mul_le_mul_left 2 ht)

end MoltResearch
