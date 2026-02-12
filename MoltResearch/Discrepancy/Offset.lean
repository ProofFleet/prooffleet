import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: offset sums

Extra lemmas about `apSumOffset` and its relation to differences of `apSum`.
-/

namespace MoltResearch

lemma apSumOffset_eq_sub (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  have h0 := (apSum_add_length (f := f) (d := d) (m := m) (n := n)).symm
  have h : apSumOffset f d m n + apSum f d m = apSum f d (m + n) := by
    simpa [add_comm] using h0
  exact eq_sub_of_add_eq h

/-- Express `apSumOffset` as an `apSum` with step `1`. -/
lemma apSumOffset_eq_apSum_step_one (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
  unfold apSumOffset apSum
  -- `simp` reduces `((i+1)*1)` and normalizes `(m + (i+1))`.
  simp [Nat.add_assoc]

-- (lemma `apSumOffset_add_length` moved to `MoltResearch/Discrepancy/Basic.lean`)

/-- First term of an offset AP sum. -/
lemma apSumOffset_succ_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 1) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  have h := apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := 1) (n₂ := n)
  simpa [Nat.add_comm, apSumOffset_one, add_comm] using h

/-- Rearranged version of `apSumOffset_succ_length`. -/
lemma apSumOffset_succ_offset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d (m + 1) n = apSumOffset f d m (n + 1) - f ((m + 1) * d) := by
  have h : apSumOffset f d (m + 1) n + f ((m + 1) * d) = apSumOffset f d m (n + 1) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n)).symm
  simpa using eq_sub_of_add_eq h

/-- Sum of offset AP sums over a pointwise sum of functions. -/
lemma apSumOffset_add (f g : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f k + g k) d m n = apSumOffset f d m n + apSumOffset g d m n := by
  classical
  unfold apSumOffset
  simp [Finset.sum_add_distrib]

/-- Offset AP sum of a negated function. -/
lemma apSumOffset_neg (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => - f k) d m n = - apSumOffset f d m n := by
  classical
  unfold apSumOffset
  simp [Finset.sum_neg_distrib]

/-- Offset AP sum of a pointwise subtraction of functions. -/
lemma apSumOffset_sub (f g : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f k - g k) d m n = apSumOffset f d m n - apSumOffset g d m n := by
  classical
  unfold apSumOffset
  simp [Finset.sum_sub_distrib]

/-- Multiplication by a constant on the left commutes with `apSumOffset`. -/
lemma apSumOffset_mul_left (c : ℤ) (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => c * f k) d m n = c * apSumOffset f d m n := by
  classical
  unfold apSumOffset
  simp [Finset.mul_sum]

/-- Multiplication by a constant on the right commutes with `apSumOffset`. -/
lemma apSumOffset_mul_right (f : ℕ → ℤ) (c : ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f k * c) d m n = apSumOffset f d m n * c := by
  classical
  unfold apSumOffset
  simp [Finset.sum_mul]

lemma IsSignSequence.natAbs_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  -- Define the shifted sign sequence.
  have hf' : IsSignSequence (fun k => f ((m + k) * d)) := by
    intro k
    exact hf ((m + k) * d)
  -- Rewrite the offset sum as an `apSum` with step `1`.
  have h_eq := apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)
  -- Apply the existing bound for `apSum`.
  have h_le := (IsSignSequence.natAbs_apSum_le (hf := hf') (d := 1) (n := n))
  simpa [h_eq] using h_le

lemma IsSignSequence.natAbs_apSum_sub_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n := by
  have h := hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)] using h

end MoltResearch
