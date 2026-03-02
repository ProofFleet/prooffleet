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

/-- Factor a product step size `d * k` by pushing `d` into the summand.

This is the inverse-orientation of `apSum_map_mul` (up to commutativity): it lets you normalize an
AP sum along step `d * k` into an AP sum along step `k` on the multiplied sequence `x ↦ f (x * d)`.

This is useful as a canonical “compare different steps” normal form in multiplicative reindexing
arguments.
-/
lemma apSum_mul_eq_apSum_map_mul (f : ℕ → ℤ) (d k n : ℕ) :
    apSum f (d * k) n = apSum (fun x => f (x * d)) k n := by
  -- `apSum_map_mul` gives the forward direction with step `k * d`.
  simpa [Nat.mul_comm] using (apSum_map_mul (f := f) (k := d) (d := k) (n := n)).symm

lemma apSumOffset_map_mul (f : ℕ → ℤ) (k d m n : ℕ) :
  apSumOffset (fun x => f (x * k)) d m n = apSumOffset f (d * k) m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_assoc]

lemma apSum_map_mul_div_of_dvd (f : ℕ → ℤ) (k d n : ℕ) (hk : k > 0) (hd : k ∣ d) :
  apSum (fun x => f (x * k)) (d / k) n = apSum f d n := by
  rcases hd with ⟨d0, rfl⟩
  have hd' : k * d0 / k = d0 := Nat.mul_div_right d0 hk
  have d0k : d0 * k = k * d0 := Nat.mul_comm d0 k
  simpa [hd', d0k] using (apSum_map_mul (f := f) (k := k) (d := d0) (n := n))

lemma apSumOffset_map_mul_div_of_dvd (f : ℕ → ℤ) (k d m n : ℕ) (hk : k > 0) (hd : k ∣ d) :
  apSumOffset (fun x => f (x * k)) (d / k) m n = apSumOffset f d m n := by
  rcases hd with ⟨d0, rfl⟩
  have hd' : k * d0 / k = d0 := Nat.mul_div_right d0 hk
  have d0k : d0 * k = k * d0 := Nat.mul_comm d0 k
  simpa [hd', d0k] using (apSumOffset_map_mul (f := f) (k := k) (d := d0) (m := m) (n := n))

lemma apSumFrom_map_mul (f : ℕ → ℤ) (k a d n : ℕ) :
  apSumFrom (fun x => f (x * k)) a d n = apSumFrom f (a * k) (d * k) n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.add_mul, Nat.mul_assoc]

/-- Undo the `(· * k)` reindexing when `a` and `d` are multiples of `k`. -/
lemma apSumFrom_map_mul_div_of_dvd (f : ℕ → ℤ) (k a d n : ℕ) (hk : k > 0)
    (ha : k ∣ a) (hd : k ∣ d) :
  apSumFrom (fun x => f (x * k)) (a / k) (d / k) n = apSumFrom f a d n := by
  rcases ha with ⟨a0, rfl⟩
  rcases hd with ⟨d0, rfl⟩
  have ha' : k * a0 / k = a0 := Nat.mul_div_right a0 hk
  have hd' : k * d0 / k = d0 := Nat.mul_div_right d0 hk
  have ha0 : a0 * k = k * a0 := Nat.mul_comm a0 k
  have hd0 : d0 * k = k * d0 := Nat.mul_comm d0 k
  simpa [ha', hd', ha0, hd0] using
    (apSumFrom_map_mul (f := f) (k := k) (a := a0) (d := d0) (n := n))

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
