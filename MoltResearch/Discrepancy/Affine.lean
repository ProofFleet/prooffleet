import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: affine arithmetic progression sums

(Work in progress.)
-/

namespace MoltResearch

/-- Sum of `f` along the arithmetic progression `a + d, a + 2d, …, a + nd`. -/
def apSumFrom (f : ℕ → ℤ) (a d n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f (a + (i + 1) * d))

@[simp] lemma apSumFrom_zero (f : ℕ → ℤ) (a d : ℕ) :
  apSumFrom f a d 0 = 0 := by
  unfold apSumFrom
  simp

@[simp] lemma apSumFrom_one (f : ℕ → ℤ) (a d : ℕ) :
  apSumFrom f a d 1 = f (a + d) := by
  unfold apSumFrom
  simp

lemma apSumFrom_succ (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d (n + 1) = apSumFrom f a d n + f (a + (n + 1) * d) := by
  unfold apSumFrom
  simpa [Finset.sum_range_succ] using
    (Finset.sum_range_succ (fun i => f (a + (i + 1) * d)) n)

lemma apSum_eq_apSumFrom (f : ℕ → ℤ) (d n : ℕ) :
  apSum f d n = apSumFrom f 0 d n := by
  unfold apSum apSumFrom
  simp [Nat.zero_add]

lemma apSumOffset_eq_apSumFrom (f : ℕ → ℤ) (d m n : ℕ) :
  apSumOffset f d m n = apSumFrom f (m * d) d n := by
  unfold apSumOffset apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  have h : (m + i + 1) * d = m * d + (i + 1) * d := by
    simpa [Nat.add_assoc] using (Nat.add_mul m (i + 1) d)
  simp [h]

lemma apSumFrom_add_length (f : ℕ → ℤ) (a d m n : ℕ) :
  apSumFrom f a d (m + n) = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
  unfold apSumFrom
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_mul, Nat.mul_add,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Finset.sum_range_add (fun i => f (a + (i + 1) * d)) m n)

end MoltResearch
