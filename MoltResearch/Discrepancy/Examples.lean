import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Witness
import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.AffineTail

/-!
# Discrepancy: sanity-check examples

These are small, fully verified theorems that demonstrate the nucleus API.
They also serve as regression tests for the intended surface forms.
-/

namespace MoltResearch

/-- The constant `+1` sequence is a sign sequence. -/
lemma isSignSequence_const_one : IsSignSequence (fun _n : ℕ => (1 : ℤ)) := by
  intro n
  left
  rfl

/-- For the constant `+1` sequence, `apSum` is just the length `n`. -/
lemma apSum_const_one (d n : ℕ) : apSum (fun _k : ℕ => (1 : ℤ)) d n = (n : ℤ) := by
  classical
  unfold apSum
  -- sum of `n` copies of 1 in ℤ
  simpa using (Finset.sum_const_one : (Finset.range n).sum (fun _ => (1 : ℤ)) = n)

/-- For the constant `+1` sequence, `apSumOffset` is also just the length `n`.

This is a tiny regression test that `apSumOffset` really is “the next `n` terms after skipping `m`”,
not something that accidentally depends on `d` or `m` for constant sequences.
-/
lemma apSumOffset_const_one (d m n : ℕ) :
    apSumOffset (fun _k : ℕ => (1 : ℤ)) d m n = (n : ℤ) := by
  classical
  unfold apSumOffset
  simpa using (Finset.sum_const_one : (Finset.range n).sum (fun _ => (1 : ℤ)) = n)

/-! ### Offset/affine bridge regression -/

/-- Regression test for `apSumOffset_shift_add_eq_apSumFrom` (constant `+1` sequence).

This ensures the bridge lemma keeps typechecking and reduces correctly in a simple case.
-/
lemma apSumOffset_shift_add_eq_apSumFrom_const_one (d m n : ℕ) :
    apSumOffset (fun _t : ℕ => (1 : ℤ)) d m n = apSumFrom (fun _t : ℕ => (1 : ℤ)) (m * d) d n := by
  -- The bridge lemma with `a = 0`.
  simpa [Nat.zero_add] using
    (apSumOffset_shift_add_eq_apSumFrom_bridge (f := fun _t : ℕ => (1 : ℤ)) (a := 0) (d := d) (m := m) (n := n))

/-! ### Constant `-1` sequence -/

/-- The constant `-1` sequence is a sign sequence. -/
lemma isSignSequence_const_neg_one : IsSignSequence (fun _n : ℕ => (-1 : ℤ)) := by
  intro n
  right
  rfl

/-- For the constant `-1` sequence, `apSum` is `-n`. -/
lemma apSum_const_neg_one (d n : ℕ) : apSum (fun _k : ℕ => (-1 : ℤ)) d n = -(n : ℤ) := by
  classical
  unfold apSum
  -- sum of `n` copies of -1 in ℤ
  simp

/-- For the constant `-1` sequence, `apSumOffset` is `-n`.

This pairs with `apSumOffset_const_one` as a sanity check for offset sums on constant sequences.
-/
lemma apSumOffset_const_neg_one (d m n : ℕ) :
    apSumOffset (fun _k : ℕ => (-1 : ℤ)) d m n = -(n : ℤ) := by
  classical
  unfold apSumOffset
  simp

/-- Sanity check: there exists a sign sequence with unbounded discrepancy.

This does **not** prove Erdős discrepancy (which quantifies over *all* sign sequences),
but it verifies that the nucleus definitions match the intended meaning.
-/
theorem exists_signSequence_unbounded_discrepancy :
    ∃ f : ℕ → ℤ, IsSignSequence f ∧ ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine ⟨fun _ => (1 : ℤ), isSignSequence_const_one, ?_⟩
  intro C
  -- take d = 1 and n = C+1
  refine ⟨1, C + 1, by decide, ?_⟩
  -- `apSum` evaluates to `C+1`, so natAbs is `C+1` and hence > C
  have hsum : apSum (fun _k : ℕ => (1 : ℤ)) 1 (C + 1) = ((C + 1 : ℕ) : ℤ) := by
    simpa using apSum_const_one (d := 1) (n := C + 1)
  have hnatAbs : Int.natAbs (((C + 1 : ℕ) : ℤ)) = C + 1 := by
    -- `natAbs` of a natural cast is the original natural.
    simpa using (Int.natAbs_natCast (C + 1))
  -- finish
  rw [hsum, hnatAbs]
  exact Nat.lt_succ_self C

/-! ### Unbounded discrepancy for the constant `-1` sequence -/

/-- Sanity check: there exists a sign sequence with unbounded discrepancy, using the constant `-1`
sequence.

This is the same witness as `exists_signSequence_unbounded_discrepancy`, but it exercises the
normalization lemmas on a negative constant.
-/
theorem exists_signSequence_unbounded_discrepancy_neg :
    ∃ f : ℕ → ℤ, IsSignSequence f ∧ ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine ⟨fun _ => (-1 : ℤ), isSignSequence_const_neg_one, ?_⟩
  intro C
  -- take d = 1 and n = C+1
  refine ⟨1, C + 1, by decide, ?_⟩
  -- `apSum` evaluates to `-(C+1)`, so natAbs is `C+1` and hence > C
  have hsum : apSum (fun _k : ℕ => (-1 : ℤ)) 1 (C + 1) = -((C + 1 : ℕ) : ℤ) := by
    simpa using apSum_const_neg_one (d := 1) (n := C + 1)
  have hnatAbs : Int.natAbs (-((C + 1 : ℕ) : ℤ)) = C + 1 := by
    calc
      Int.natAbs (-((C + 1 : ℕ) : ℤ)) = Int.natAbs (((C + 1 : ℕ) : ℤ)) := by
        simpa using (Int.natAbs_neg (((C + 1 : ℕ) : ℤ)))
      _ = C + 1 := by
        simpa using (Int.natAbs_natCast (C + 1))
  rw [hsum, hnatAbs]
  exact Nat.lt_succ_self C

/-! ### Witness normal-form API illustration -/

/-- The constant `+1` sign sequence has unbounded discrepancy, expressed in the structured
`DiscrepancyWitnessPos` normal form.

This is a small regression test for the normalization boundary
`HasDiscrepancyAtLeast f C ↔ Nonempty (DiscrepancyWitnessPos f C)`.
-/
theorem exists_signSequence_unbounded_discrepancy_witnessPos :
    ∃ f : ℕ → ℤ, IsSignSequence f ∧ ∀ C : ℕ, Nonempty (DiscrepancyWitnessPos f C) := by
  -- We reuse the constant `+1` construction from `exists_signSequence_unbounded_discrepancy`.
  refine ⟨fun _ => (1 : ℤ), isSignSequence_const_one, ?_⟩
  intro C
  -- First prove the `HasDiscrepancyAtLeast` form, then convert using the witness equivalence.
  have h : HasDiscrepancyAtLeast (fun _ => (1 : ℤ)) C := by
    -- take d = 1 and n = C+1
    refine ⟨1, C + 1, by decide, ?_⟩
    have hsum : apSum (fun _k : ℕ => (1 : ℤ)) 1 (C + 1) = ((C + 1 : ℕ) : ℤ) := by
      simpa using apSum_const_one (d := 1) (n := C + 1)
    have hnatAbs : Int.natAbs (((C + 1 : ℕ) : ℤ)) = C + 1 := by
      simpa using (Int.natAbs_natCast (C + 1))
    rw [hsum, hnatAbs]
    exact Nat.lt_succ_self C
  exact (HasDiscrepancyAtLeast.iff_nonempty_witnessPos (f := fun _ => (1 : ℤ)) (C := C)).1 h

/-! ### Affine discrepancy for the constant `+1` sequence -/

/-! #### Offset-tail ↔ affine-tail bridge (regression)

This is a small compile-time check that the stable surface import

`import MoltResearch.Discrepancy`

exposes the canonical lemma rewriting an offset tail on a shifted sequence into an affine tail.
-/
example (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun t => f (t + a)) d m n = apSumFrom f (a + m * d) d n := by
  simpa using
    (apSumOffset_shift_add_eq_apSumFrom_tail_firstTerm (f := f) (a := a) (d := d) (m := m) (n := n))

/-- For the constant `+1` sequence, `apSumFrom` is just the length `n`. -/
lemma apSumFrom_const_one (a d n : ℕ) : apSumFrom (fun _ => (1 : ℤ)) a d n = (n : ℤ) := by
  classical
  unfold apSumFrom
  -- sum of `n` copies of 1 in ℤ
  simpa using (Finset.sum_const_one : (Finset.range n).sum (fun _ => (1 : ℤ)) = n)

/-- Sanity check: there exists a sign sequence with unbounded *affine* discrepancy.

This exercises the affine discrepancy predicate `HasAffineDiscrepancyAtLeast` (as opposed to the
homogeneous predicate `HasDiscrepancyAtLeast`).
-/
theorem exists_signSequence_unbounded_affine_discrepancy :
    ∃ f : ℕ → ℤ, IsSignSequence f ∧ ∀ C : ℕ, HasAffineDiscrepancyAtLeast f C := by
  refine ⟨fun _ => (1 : ℤ), isSignSequence_const_one, ?_⟩
  intro C
  -- take a = 0, d = 1, n = C+1
  refine ⟨0, 1, C + 1, by decide, ?_⟩
  have hsum : apSumFrom (fun _ => (1 : ℤ)) 0 1 (C + 1) = ((C + 1 : ℕ) : ℤ) := by
    simpa using apSumFrom_const_one (a := 0) (d := 1) (n := C + 1)
  have hnatAbs : Int.natAbs (((C + 1 : ℕ) : ℤ)) = C + 1 := by
    simpa using (Int.natAbs_natCast (C + 1))
  rw [hsum, hnatAbs]
  exact Nat.lt_succ_self C

end MoltResearch
