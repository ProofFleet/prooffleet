import MoltResearch.Discrepancy.Basic

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

end MoltResearch
