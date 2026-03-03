import MoltResearch.Discrepancy.Affine

/-!
# Reindex lemmas for arithmetic progression sums

These lemmas allow us to reindex sums when the underlying function
is composed with a multiplication on the argument.
-/

namespace MoltResearch

/-!
## Affine reindexing glue

These lemmas provide a tiny library for reindexing `Finset.range` sums along an injective
affine map on indices `i ↦ a + b * i` (with `0 < b`).

They are used to expose a nucleus-friendly normal form for `apSumOffset` that avoids rewriting
under lambdas.
-/

/-- The affine map `i ↦ a + b*i` is injective when `b > 0`. -/
lemma injective_add_mul (a b : ℕ) (hb : 0 < b) :
    Function.Injective (fun i : ℕ => a + b * i) := by
  intro i j h
  have h' : b * i = b * j := Nat.add_left_cancel h
  exact Nat.mul_left_cancel hb h'

/-- An embedding version of `fun i => a + b*i` (usable with `Finset.map`). -/
def affineEmbedding (a b : ℕ) (hb : 0 < b) : ℕ ↪ ℕ :=
  ⟨fun i => a + b * i, injective_add_mul a b hb⟩

/-- Reindex a `Finset.range` sum along an injective affine map.

This is a controlled wrapper around `Finset.sum_map`.
-/
lemma sum_range_affine_reindex (a b n : ℕ) (hb : 0 < b) (f : ℕ → ℤ) :
    (Finset.range n).sum (fun i => f (a + b * i)) =
      ((Finset.range n).map (affineEmbedding a b hb)).sum f := by
  classical
  -- Reduce to `Finset.sum_map` for the embedding `i ↦ a + b*i`.
  -- We `unfold` so the definitional equality matches the `sum_map` statement without `simp` noise.
  unfold affineEmbedding
  -- `Finset.sum_map` gives the equality with the map on the right; we want its symmetric form.
  exact (Finset.sum_map (Finset.range n) ⟨fun i : ℕ => a + b * i, injective_add_mul a b hb⟩ f).symm

/-- Reindex a `Finset.range` sum along an injective affine map, when the summand also multiplies the
reindexed index by `d`.

This is a convenience wrapper around `sum_range_affine_reindex` that avoids re-proving `Finset`
boilerplate when normalizing sums of the form
`(Finset.range n).sum (fun i => f ((a + b * i) * d))`.
-/
lemma sum_range_affine_mul_reindex (a b d n : ℕ) (hb : 0 < b) (f : ℕ → ℤ) :
    (Finset.range n).sum (fun i => f ((a + b * i) * d)) =
      ((Finset.range n).map (affineEmbedding a b hb)).sum (fun k => f (k * d)) := by
  simpa using
    (sum_range_affine_reindex (a := a) (b := b) (n := n) (hb := hb)
      (f := fun k => f (k * d)))

/-- Reindex a range sum along an injective affine map inside an `apSumOffset`-style binder.

This is a small convenience wrapper around `sum_range_affine_reindex` that avoids repeated
`Finset` boilerplate when normalizing expressions like
`∑ i ∈ range n, f ((m + (a + b*i) + 1) * d)`.
-/
lemma sum_range_apSumOffset_affine_reindex (a b n m d : ℕ) (hb : 0 < b) (f : ℕ → ℤ) :
    (Finset.range n).sum (fun i => f ((m + (a + b * i) + 1) * d)) =
      ((Finset.range n).map (affineEmbedding a b hb)).sum (fun k => f ((m + k + 1) * d)) := by
  simpa using
    (sum_range_affine_reindex (a := a) (b := b) (n := n) (hb := hb)
      (f := fun k => f ((m + k + 1) * d)))

/-- Nucleus-friendly normal form: reindex `apSumOffset` via the injective affine map
`i ↦ (m+1) + 1*i`.

Downstream code can now use `Finset.sum_map` over the mapped finset without additional
`Finset.sum_congr` / arithmetic boilerplate.
-/
lemma apSumOffset_reindex_affine (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n =
      ((Finset.range n).map (affineEmbedding (m + 1) 1 (Nat.succ_pos 0))).sum
        (fun k => f (k * d)) := by
  unfold apSumOffset
  -- `m + i + 1 = (m+1) + 1*i`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (sum_range_affine_mul_reindex (a := m + 1) (b := 1) (d := d) (n := n)
      (hb := Nat.succ_pos 0) (f := f))

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

/-- Factor a product step size `d * k` by pushing `d` into the summand (offset-sum version).

This is the offset analogue of `apSum_mul_eq_apSum_map_mul`.
-/
lemma apSumOffset_mul_eq_apSumOffset_map_mul (f : ℕ → ℤ) (d k m n : ℕ) :
    apSumOffset f (d * k) m n = apSumOffset (fun x => f (x * d)) k m n := by
  -- `apSumOffset_map_mul` gives the forward direction with step `k * d`.
  simpa [Nat.mul_comm] using
    (apSumOffset_map_mul (f := f) (k := d) (d := k) (m := m) (n := n)).symm

/-- Variant oriented to match `apSumOffset f (d₁ * d₂) m n`.

This is a convenient wrapper for rewriting
`apSumOffset f (d₁*d₂) m n` into `apSumOffset (fun t => f (t*d₁)) d₂ m n`.
-/
lemma apSumOffset_mul_eq_apSumOffset_map_mul₁₂ (f : ℕ → ℤ) (d₁ d₂ m n : ℕ) :
    apSumOffset f (d₁ * d₂) m n = apSumOffset (fun t => f (t * d₁)) d₂ m n := by
  simpa using (apSumOffset_mul_eq_apSumOffset_map_mul (f := f) (d := d₁) (k := d₂) (m := m) (n := n))

/-- Left-multiplication-friendly variant: rewrite into a summand `t ↦ f (d₁ * t)`.

Useful when downstream normalization prefers keeping multiplication on the left.
-/
lemma apSumOffset_mul_eq_apSumOffset_map_mul_left (f : ℕ → ℤ) (d₁ d₂ m n : ℕ) :
    apSumOffset f (d₁ * d₂) m n = apSumOffset (fun t => f (d₁ * t)) d₂ m n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_mul_eq_apSumOffset_map_mul₁₂ (f := f) (d₁ := d₁) (d₂ := d₂) (m := m) (n := n))

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
