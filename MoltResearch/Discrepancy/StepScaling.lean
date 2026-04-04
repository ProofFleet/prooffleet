import MoltResearch.Discrepancy.Residue

/-!
# Discrepancy: step-scaling bounds

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Step scaling” bound wrapper.

Goal: if `d' = q*d` (so `d ∣ d'`), control discrepancy at step `d'` by discrepancy-style
expressions at step `d`.  The core input is the residue-class split normal form
`apSum_mul_len_succ`.
-/

namespace MoltResearch

open scoped BigOperators

/-- Triangle-inequality helper for `Int.natAbs` of a finite sum.

This is a local lemma so downstream statements can avoid unfolding the induction.
-/
private lemma natAbs_sum_le_sum_natAbs (s : Finset α) (g : α → ℤ) :
    Int.natAbs (s.sum g) ≤ s.sum (fun a => Int.natAbs (g a)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    -- `sum_insert` + triangle inequality + IH.
    -- `|g a + ∑ g| ≤ |g a| + |∑ g| ≤ |g a| + ∑ |g|`.
    have h1 : Int.natAbs (g a + s.sum g) ≤ Int.natAbs (g a) + Int.natAbs (s.sum g) :=
      Int.natAbs_add_le (g a) (s.sum g)
    have h2 : Int.natAbs (g a) + Int.natAbs (s.sum g) ≤
        Int.natAbs (g a) + s.sum (fun x => Int.natAbs (g x)) :=
      Nat.add_le_add_left hs _
    -- Rewrite `sum_insert` and conclude.
    simpa [ha, Finset.sum_insert, add_assoc, add_left_comm, add_comm] using le_trans h1 h2

/-- Step-scaling bound wrapper (disc-level).

If `q > 0`, the discrepancy along the dilated step `q*d` (over `n+1` terms) is bounded by the
full length-`q*(n+1)` discrepancy at step `d`, plus the sum of the discrepancies of the nonzero
residue-class blocks from the residue-split normal form.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Step scaling” bound wrapper.
-/
theorem disc_mul_step_le (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    disc f (q * d) (n + 1) ≤
      disc f d (q * (n + 1)) +
        (Finset.range (q - 1)).sum (fun r =>
          Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)) := by
  classical
  -- Residue split: `A = B + S`.
  set S : ℤ := (Finset.range (q - 1)).sum (fun r =>
      f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) with hS
  have hsplit := apSum_mul_len_succ (f := f) (d := d) (q := q) (n := n) hq
  -- Rearrange to isolate the `0 mod q` class.
  have hB : apSum f (q * d) (n + 1) = apSum f d (q * (n + 1)) - S := by
    -- `hsplit : A = B + S`.
    -- Use `eq_sub_of_add_eq` on `B + S = A`.
    exact eq_sub_of_add_eq (by simpa [hS, add_comm, add_left_comm, add_assoc] using hsplit.symm)

  -- Now apply `Int.natAbs_sub_le` and then bound `|S|` by the sum of `|term|`.
  -- Convert everything to `disc` wrappers at the end.
  have hnatAbsS : Int.natAbs S ≤
      (Finset.range (q - 1)).sum (fun r =>
        Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)) := by
    -- unfold `S` and apply the helper lemma.
    simpa [hS] using (natAbs_sum_le_sum_natAbs (s := Finset.range (q - 1))
      (g := fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n))

  -- Main inequality.
  -- `disc f (q*d) (n+1) = |apSum ...|`.
  -- Use `hB` to rewrite and then triangle inequality.
  calc
    disc f (q * d) (n + 1)
        = Int.natAbs (apSum f (q * d) (n + 1)) := by rfl
    _ = Int.natAbs (apSum f d (q * (n + 1)) - S) := by simpa [hB]
    _ ≤ Int.natAbs (apSum f d (q * (n + 1))) + Int.natAbs S :=
          Int.natAbs_sub_le _ _
    _ ≤ Int.natAbs (apSum f d (q * (n + 1))) +
          (Finset.range (q - 1)).sum (fun r =>
            Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)) := by
          exact Nat.add_le_add_left hnatAbsS _
    _ = disc f d (q * (n + 1)) +
          (Finset.range (q - 1)).sum (fun r =>
            Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)) := by
          rfl

end MoltResearch
