import MoltResearch.Discrepancy.Affine

/-!
# Reindex lemmas for arithmetic progression sums

These lemmas allow us to reindex sums when the underlying function
is composed with a multiplication on the argument.
-/

namespace MoltResearch

lemma apSum_map_mul (f : ℕ → ℤ) (k d n : ℕ) :
  apSum (fun x => f (x * k)) d n = apSum f (d * k) n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_assoc]

lemma apSumOffset_map_mul (f : ℕ → ℤ) (k d m n : ℕ) :
  apSumOffset (fun x => f (x * k)) d m n = apSumOffset f (d * k) m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_assoc]

lemma apSumFrom_map_mul (f : ℕ → ℤ) (k a d n : ℕ) :
  apSumFrom (fun x => f (x * k)) a d n = apSumFrom f (a * k) (d * k) n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.add_mul, Nat.mul_assoc]

lemma HasDiscrepancyAtLeast.of_map_mul {f : ℕ → ℤ} {k C : ℕ} (hk : k > 0)
    (h : HasDiscrepancyAtLeast (fun x => f (x * k)) C) : HasDiscrepancyAtLeast f C := by
  rcases h with ⟨d, n, hd, hsum⟩
  refine ⟨d * k, n, ?_, ?_⟩
  · exact Nat.mul_pos hd hk
  · simpa [apSum_map_mul] using hsum

lemma HasAffineDiscrepancyAtLeast.of_map_mul {f : ℕ → ℤ} {k C : ℕ} (hk : k > 0)
    (h : HasAffineDiscrepancyAtLeast (fun x => f (x * k)) C) :
    HasAffineDiscrepancyAtLeast f C := by
  rcases h with ⟨a, d, n, hd, hsum⟩
  refine ⟨a * k, d * k, n, ?_, ?_⟩
  · exact Nat.mul_pos hd hk
  · simpa [apSumFrom_map_mul] using hsum

end MoltResearch
