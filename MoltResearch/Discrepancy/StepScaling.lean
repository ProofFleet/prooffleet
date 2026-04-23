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

/-!
## Common-step refinement/coarsening wrappers

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Common-step refinement/coarsening wrappers”.

These lemmas specialize the step-scaling wrapper `disc_mul_step_le` to the common refinement
step `Nat.lcm d d'`, so downstream stages can synchronize steps without redoing the
`lcm`/division algebra by hand.
-/

/-- Track B convenience wrapper: specialize `disc_mul_step_le` to the common refinement
step `Nat.lcm d d'`, viewing it as a multiple of `d`.

References: Problems/erdos_discrepancy.md (Track B) — “Common-step refinement/coarsening wrappers”.
-/
theorem disc_lcm_step_le_left (f : ℕ → ℤ) (d d' n : ℕ) (hd : d > 0) (hd' : d' > 0) :
    disc f (Nat.lcm d d') (n + 1) ≤
      disc f d (Nat.lcm d d' / d * (n + 1)) +
        (Finset.range (Nat.lcm d d' / d - 1)).sum (fun r =>
          Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (Nat.lcm d d') n)) := by
  classical
  -- Write `lcm d d'` as a multiple of `d`.
  set q : ℕ := Nat.lcm d d' / d
  have hdvd : d ∣ Nat.lcm d d' := Nat.dvd_lcm_left d d'
  have hqpos : q > 0 := by
    have hlcmpos : Nat.lcm d d' > 0 := Nat.lcm_pos hd hd'
    have hqne : q ≠ 0 := by
      intro hq0
      have : Nat.lcm d d' = 0 := by
        -- `(lcm/d)*d = lcm`, so if `lcm/d = 0` then `lcm = 0`.
        simpa [q, hq0] using (Nat.div_mul_cancel hdvd).symm
      exact (Nat.ne_of_gt hlcmpos) this
    exact Nat.pos_of_ne_zero hqne

  -- Apply the step-scaling wrapper at step `q*d`, then rewrite `q*d` as `lcm d d'`.
  simpa [q, Nat.div_mul_cancel hdvd] using
    (disc_mul_step_le (f := f) (d := d) (q := q) (n := n) hqpos)

/-- Track B convenience wrapper: symmetric version of `disc_lcm_step_le_left`, viewing
`Nat.lcm d d'` as a multiple of `d'`.

References: Problems/erdos_discrepancy.md (Track B) — “Common-step refinement/coarsening wrappers”.
-/
theorem disc_lcm_step_le_right (f : ℕ → ℤ) (d d' n : ℕ) (hd : d > 0) (hd' : d' > 0) :
    disc f (Nat.lcm d d') (n + 1) ≤
      disc f d' (Nat.lcm d d' / d' * (n + 1)) +
        (Finset.range (Nat.lcm d d' / d' - 1)).sum (fun r =>
          Int.natAbs (f ((r + 1) * d') + apSumFrom f ((r + 1) * d') (Nat.lcm d d') n)) := by
  classical
  set q : ℕ := Nat.lcm d d' / d'
  have hdvd : d' ∣ Nat.lcm d d' := Nat.dvd_lcm_right d d'
  have hqpos : q > 0 := by
    have hlcmpos : Nat.lcm d d' > 0 := Nat.lcm_pos hd hd'
    have hqne : q ≠ 0 := by
      intro hq0
      have : Nat.lcm d d' = 0 := by
        simpa [q, hq0] using (Nat.div_mul_cancel hdvd).symm
      exact (Nat.ne_of_gt hlcmpos) this
    exact Nat.pos_of_ne_zero hqne

  simpa [q, Nat.div_mul_cancel hdvd] using
    (disc_mul_step_le (f := f) (d := d') (q := q) (n := n) hqpos)

/-!
## UpTo-level common-step coarsening wrappers

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Coarsen to gcd/lcm normalization lemma (UpTo-level)”.

These are `discUpTo` analogues of `disc_lcm_step_le_left/right`, packaged with explicit
triangle-inequality style error terms as suprema over `n ≤ N`.
-/

/-- UpTo-level wrapper: specialize `disc_lcm_step_le_left` and take a supremum over
`n ≤ N+1`.

This is the `discUpTo` analogue of `disc_lcm_step_le_left`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Coarsen to gcd/lcm normalization lemma (UpTo-level)”.
-/
theorem discUpTo_lcm_step_le_left (f : ℕ → ℤ) (d d' N : ℕ) (hd : d > 0) (hd' : d' > 0) :
    discUpTo f (Nat.lcm d d') (N + 1) ≤
      discUpTo f d (Nat.lcm d d' / d * (N + 1)) +
        (Finset.range (Nat.lcm d d' / d - 1)).sum (fun r =>
          (Finset.range (N + 1)).sup (fun n =>
            Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (Nat.lcm d d') n))) := by
  classical
  -- Abbreviate the left multiplier.
  set q : ℕ := Nat.lcm d d' / d
  have hdvd : d ∣ Nat.lcm d d' := Nat.dvd_lcm_left d d'
  -- We take a supremum over `n ≤ N+1` and apply `disc_lcm_step_le_left` pointwise.
  unfold discUpTo
  refine Finset.sup_le ?_
  intro n hn
  have hnle : n ≤ N + 1 := Nat.le_of_lt_succ (Finset.mem_range.1 hn)
  cases n with
  | zero =>
      -- `disc .. 0 = 0`.
      simp
  | succ n' =>
      have hn'le : n' ≤ N := Nat.succ_le_succ_iff.1 hnle
      have hdisc :=
        disc_lcm_step_le_left (f := f) (d := d) (d' := d') (n := n') hd hd'
      -- Bound the main `disc` term by `discUpTo`.
      have hmain : disc f d (q * (n' + 1)) ≤ discUpTo f d (q * (N + 1)) := by
        refine disc_le_discUpTo (f := f) (d := d) (n := q * (n' + 1)) (N := q * (N + 1)) ?_
        exact Nat.mul_le_mul_left q (Nat.succ_le_succ hn'le)
      -- Bound each error term by its `sup` over `n ≤ N`.
      have herr :
          (Finset.range (q - 1)).sum (fun r =>
              Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (Nat.lcm d d') n'))
            ≤ (Finset.range (q - 1)).sum (fun r =>
              (Finset.range (N + 1)).sup (fun n =>
                Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (Nat.lcm d d') n))) := by
        refine Finset.sum_le_sum ?_
        intro r hr
        have hnmem : n' ∈ Finset.range (N + 1) := by
          exact Finset.mem_range.2 (Nat.lt_succ_of_le hn'le)
        exact (Finset.le_sup (s := Finset.range (N + 1))
          (f := fun n =>
            Int.natAbs (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (Nat.lcm d d') n)) hnmem)

      -- Combine the pointwise inequality with the `discUpTo`/`sup` bounds.
      exact le_trans hdisc (Nat.add_le_add hmain herr)

/-- UpTo-level wrapper: symmetric version of `discUpTo_lcm_step_le_left`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Coarsen to gcd/lcm normalization lemma (UpTo-level)”.
-/
theorem discUpTo_lcm_step_le_right (f : ℕ → ℤ) (d d' N : ℕ) (hd : d > 0) (hd' : d' > 0) :
    discUpTo f (Nat.lcm d d') (N + 1) ≤
      discUpTo f d' (Nat.lcm d d' / d' * (N + 1)) +
        (Finset.range (Nat.lcm d d' / d' - 1)).sum (fun r =>
          (Finset.range (N + 1)).sup (fun n =>
            Int.natAbs (f ((r + 1) * d') + apSumFrom f ((r + 1) * d') (Nat.lcm d d') n))) := by
  classical
  set q : ℕ := Nat.lcm d d' / d'
  have hdvd : d' ∣ Nat.lcm d d' := Nat.dvd_lcm_right d d'
  unfold discUpTo
  refine Finset.sup_le ?_
  intro n hn
  have hnle : n ≤ N + 1 := Nat.le_of_lt_succ (Finset.mem_range.1 hn)
  cases n with
  | zero =>
      simp
  | succ n' =>
      have hn'le : n' ≤ N := Nat.succ_le_succ_iff.1 hnle
      have hdisc :=
        disc_lcm_step_le_right (f := f) (d := d) (d' := d') (n := n') hd hd'
      have hmain : disc f d' (q * (n' + 1)) ≤ discUpTo f d' (q * (N + 1)) := by
        refine disc_le_discUpTo (f := f) (d := d') (n := q * (n' + 1)) (N := q * (N + 1)) ?_
        exact Nat.mul_le_mul_left q (Nat.succ_le_succ hn'le)
      have herr :
          (Finset.range (q - 1)).sum (fun r =>
              Int.natAbs (f ((r + 1) * d') + apSumFrom f ((r + 1) * d') (Nat.lcm d d') n'))
            ≤ (Finset.range (q - 1)).sum (fun r =>
              (Finset.range (N + 1)).sup (fun n =>
                Int.natAbs (f ((r + 1) * d') + apSumFrom f ((r + 1) * d') (Nat.lcm d d') n))) := by
        refine Finset.sum_le_sum ?_
        intro r hr
        have hnmem : n' ∈ Finset.range (N + 1) := by
          exact Finset.mem_range.2 (Nat.lt_succ_of_le hn'le)
        exact (Finset.le_sup (s := Finset.range (N + 1))
          (f := fun n =>
            Int.natAbs (f ((r + 1) * d') + apSumFrom f ((r + 1) * d') (Nat.lcm d d') n)) hnmem)

      exact le_trans hdisc (Nat.add_le_add hmain herr)

end MoltResearch
