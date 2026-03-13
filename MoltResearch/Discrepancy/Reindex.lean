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

/-!
### Reindexing `apSumOffset` by permuting `Finset.range`

This is a small piece of “glue” for later arguments that split a sum into residue classes (e.g.
parity classes) and then swap / permute those classes by a change of variables.

We keep this lemma at the nucleus level (`apSumOffset …`), so downstream code can reindex without
dropping into raw `Finset` boilerplate.
-/

/-- Reindex an `apSumOffset` sum by a bijection on the range indices.

If `σ` is a permutation of the index set `{0,1,…,n-1}` (expressed as a map `ℕ → ℕ` that is
injective and surjective on `Finset.range n`), then we may rewrite the binder
`i ↦ f ((m + i + 1) * d)` to `i ↦ f ((m + σ i + 1) * d)`.

This is a controlled wrapper around `Finset.sum_bij` specialized to the `apSumOffset` normal form.
-/
lemma apSumOffset_reindex_range_bij (f : ℕ → ℤ) (d m n : ℕ) (σ : ℕ → ℕ)
    (hσ_range : ∀ i ∈ Finset.range n, σ i ∈ Finset.range n)
    (hσ_inj : ∀ i₁ ∈ Finset.range n, ∀ i₂ ∈ Finset.range n, σ i₁ = σ i₂ → i₁ = i₂)
    (hσ_surj : ∀ j ∈ Finset.range n, ∃ i ∈ Finset.range n, σ i = j) :
    apSumOffset f d m n = (Finset.range n).sum (fun i => f ((m + σ i + 1) * d)) := by
  classical
  unfold apSumOffset
  -- `Finset.sum_bij` gives the reindexing equality in the direction
  --   ∑ i, f (m + σ i + 1) = ∑ j, f (m + j + 1).
  -- We take its symmetric form to match the `apSumOffset` definition.
  symm
  refine Finset.sum_bij (s := Finset.range n) (t := Finset.range n)
    (i := fun i hi => σ i)
    (hi := fun i hi => hσ_range i hi)
    (i_inj := ?_)
    (i_surj := ?_)
    (h := ?_)
  · intro i₁ hi₁ i₂ hi₂ hEq
    exact hσ_inj i₁ hi₁ i₂ hi₂ hEq
  · intro j hj
    rcases hσ_surj j hj with ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · intro i hi
    rfl

/-- Reindex an `apSumOffset` sum by a permutation of the index type `Fin n`.

This is often the most ergonomic form for “swap residue classes / permute blocks” arguments,
since the change-of-variables is naturally a permutation on `Fin n`.

It is a nucleus-level wrapper that avoids dropping into raw `Finset` boilerplate.
-/
lemma apSumOffset_reindex_fin_perm (f : ℕ → ℤ) (d m n : ℕ) (σ : Equiv.Perm (Fin n)) :
    apSumOffset f d m n =
      (Finset.univ : Finset (Fin n)).sum (fun i => f ((m + (σ i).1 + 1) * d)) := by
  classical
  unfold apSumOffset
  -- Rewrite the `range` sum as a `Fin n` sum, then use invariance of `Fintype.sum` under
  -- reindexing by an equivalence.
  calc
    (Finset.range n).sum (fun i => f ((m + i + 1) * d))
        = (∑ i : Fin n, f ((m + (i : ℕ) + 1) * d)) := by
          -- `Fin.sum_univ_eq_sum_range` is stated for a function on `ℕ` (with implicit coercions
          -- from `Fin n`), so we feed it the `ℕ`-level summand.
          simpa using
            (Fin.sum_univ_eq_sum_range (n := n) (f := fun i : ℕ => f ((m + i + 1) * d))).symm
    _ = (∑ i : Fin n, f ((m + (σ i : Fin n) + 1) * d)) := by
          -- `Fintype.sum_equiv` reindexes sums.  We use it in the direction
          --   (sum over `i ↦ g (σ i)`) = (sum over `i ↦ g i`)
          -- and then take symmetry.
          symm
          simpa using
            (Fintype.sum_equiv σ
              (fun i : Fin n => f ((m + (σ i : Fin n) + 1) * d))
              (fun i : Fin n => f ((m + (i : ℕ) + 1) * d))
              (fun i => rfl))

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

/-! ### Step-factor coherence for `apSumFrom`

These lemmas are the affine analogues of the `apSum_mul_eq_apSum_map_mul` /
`apSumOffset_mul_eq_apSumOffset_map_mul…` family: they let us factor a product step size by
changing the summand.

Concretely, they rewrite an affine AP sum with step `d₁*d₂` into an affine AP sum with step `d₂`
on the sequence `t ↦ f (a + t*d₁)`.
-/

/-- Factor a product step size `d₁ * d₂` in `apSumFrom` by pushing `d₁` into the summand. -/
lemma apSumFrom_mul_eq_apSumFrom_map_mul₁₂ (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + t * d₁)) 0 d₂ n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `a + (i+1)*(d₁*d₂) = a + ((i+1)*d₂)*d₁`.
  simp [Nat.mul_assoc, Nat.mul_comm]

/-- Wrapper lemma mirroring `apSum_mul_eq_apSum_map_mul` (affine version).

This is a convenience alias for `apSumFrom_mul_eq_apSumFrom_map_mul₁₂`, letting us normalize an
affine AP sum along step `d₁*d₂` into an affine AP sum along step `d₂` on the sequence
`t ↦ f (a + t*d₁)`.
-/
lemma apSumFrom_mul_eq_apSumFrom_map_mul (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + t * d₁)) 0 d₂ n := by
  simpa using
    (apSumFrom_mul_eq_apSumFrom_map_mul₁₂ (f := f) (a := a) (d₁ := d₁) (d₂ := d₂) (n := n))

/-- Left-multiplication-friendly variant of `apSumFrom_mul_eq_apSumFrom_map_mul₁₂`. -/
lemma apSumFrom_mul_eq_apSumFrom_map_mul_left (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + d₁ * t)) 0 d₂ n := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSumFrom_mul_eq_apSumFrom_map_mul₁₂ (f := f) (a := a) (d₁ := d₁) (d₂ := d₂) (n := n))

/-! #### Step-factor coherence with a rebased index (`t - a`)

The lemmas above factor a product step size `d₁ * d₂` by *reindexing the affine sum to start at 0*.
Sometimes it is more convenient to keep the outer basepoint `a` (so the step is still `d₂` starting
from `a`), and instead rebase the index inside the summand using `(t - a)`.

Concretely, since the `apSumFrom` binder ranges over points of the form `t = a + (i+1) * d₂`, we
have `(t - a) = (i+1) * d₂`, so pushing `d₁` into the summand still yields the same endpoints.
-/

/-- Factor `d₁ * d₂` in an affine AP sum while keeping the outer basepoint `a`, by rebasing the
summand index via `(t - a)`.

This gives a convenient rewrite:

`apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + (t - a) * d₁)) a d₂ n`.
-/
lemma apSumFrom_mul_eq_apSumFrom_rebase_map_mul₁₂ (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + (t - a) * d₁)) a d₂ n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hsub : (a + (i + 1) * d₂) - a = (i + 1) * d₂ := by
    simpa [Nat.add_assoc] using Nat.add_sub_cancel a ((i + 1) * d₂)
  -- Now both sides are the same endpoint, up to associativity/commutativity of multiplication.
  simp [hsub, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Left-multiplication-friendly variant of `apSumFrom_mul_eq_apSumFrom_rebase_map_mul₁₂`. -/
lemma apSumFrom_mul_eq_apSumFrom_rebase_map_mul_left (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + d₁ * (t - a))) a d₂ n := by
  -- Swap multiplication order in the summand.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSumFrom_mul_eq_apSumFrom_rebase_map_mul₁₂ (f := f) (a := a) (d₁ := d₁) (d₂ := d₂) (n := n))

/-! #### Wrappers: step-factor coherence (keep basepoint `a`)

The Track B checklist (Problems/erdos_discrepancy.md) phrases step-factor coherence as rewriting
`apSumFrom f a (d₁*d₂) n` into an `apSumFrom` with step `d₂` while “pushing `d₁` into the summand”.

Since `apSumFrom` ranges over *points* `t = a + (i+1)*d₂`, the correct basepoint-preserving
formulation necessarily rebases the inner index via `t - a`.

These are just convenience aliases for the more explicit `…_rebase_map_mul…` lemmas above.
-/

/-- Step-factor coherence for `apSumFrom`, keeping the basepoint `a`.

Convenience wrapper (basepoint-preserving) for rewriting
`apSumFrom f a (d₁*d₂) n` into an `apSumFrom` with step `d₂`.
-/
lemma apSumFrom_mul_eq_apSumFrom_map_mul_keep_a (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + (t - a) * d₁)) a d₂ n := by
  simpa using
    (apSumFrom_mul_eq_apSumFrom_rebase_map_mul₁₂ (f := f) (a := a) (d₁ := d₁) (d₂ := d₂) (n := n))

/-- Left-multiplication-friendly variant of `apSumFrom_mul_eq_apSumFrom_map_mul_keep_a`. -/
lemma apSumFrom_mul_eq_apSumFrom_map_mul_keep_a_left (f : ℕ → ℤ) (a d₁ d₂ n : ℕ) :
    apSumFrom f a (d₁ * d₂) n = apSumFrom (fun t => f (a + d₁ * (t - a))) a d₂ n := by
  simpa using
    (apSumFrom_mul_eq_apSumFrom_rebase_map_mul_left (f := f) (a := a) (d₁ := d₁) (d₂ := d₂) (n := n))


/-- Step-factoring normal form for affine AP sums at a pure multiple start.

If the affine start is written as `a₀ * d₂`, then the endpoints
`a₀*d₂ + (i+1)*(d₁*d₂)` can be normalised in one hop to
`((i+1)*d₁ + a₀) * d₂` and expressed as an `apSumOffset` on a shifted sequence.
-/
lemma apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul (f : ℕ → ℤ) (a₀ d₁ d₂ n : ℕ) :
    apSumFrom f (d₂ * a₀) (d₁ * d₂) n = apSumOffset (fun k => f ((k + a₀) * d₂)) d₁ 0 n := by
  unfold apSumFrom apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Normalise: `d₂*a₀ + (i+1)*(d₁*d₂) = ((i+1)*d₁ + a₀) * d₂`.
  have h : d₂ * a₀ + (i + 1) * (d₁ * d₂) = ((i + 1) * d₁ + a₀) * d₂ := by
    calc
      d₂ * a₀ + (i + 1) * (d₁ * d₂)
          = a₀ * d₂ + ((i + 1) * d₁) * d₂ := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = (a₀ + (i + 1) * d₁) * d₂ := by
              simp [Nat.add_mul]
      _ = ((i + 1) * d₁ + a₀) * d₂ := by
              simp [Nat.add_comm]
  simpa [h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_assoc]

/-- Right-multiplication-friendly wrapper for `apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul`.

This version has the affine start written as `a₀ * d₂` (rather than `d₂ * a₀`), matching the
common “multiple start” presentation in surface statements.
-/
lemma apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul_right (f : ℕ → ℤ)
    (a₀ d₁ d₂ n : ℕ) :
    apSumFrom f (a₀ * d₂) (d₁ * d₂) n =
      apSumOffset (fun k => f ((k + a₀) * d₂)) d₁ 0 n := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul (f := f) (a₀ := a₀) (d₁ := d₁)
      (d₂ := d₂) (n := n))

/-- Dvd-based wrapper for `apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul`.

This is convenient when the start is given as an arbitrary `a` together with a hypothesis
`d₂ ∣ a`.
-/
lemma apSumFrom_mul_step_eq_apSumOffset_shift_mul_of_dvd (f : ℕ → ℤ) (a d₁ d₂ n : ℕ)
    (ha : d₂ ∣ a) :
    apSumFrom f a (d₁ * d₂) n = apSumOffset (fun k => f ((k + a / d₂) * d₂)) d₁ 0 n := by
  by_cases h0 : d₂ = 0
  · subst h0
    -- `0 ∣ a` forces `a = 0`.
    rcases ha with ⟨a₀, rfl⟩
    -- Everything is constant at `0`.
    have hconst : (fun k : ℕ => f ((k + (0 : ℕ) / 0) * 0)) = (fun _ : ℕ => f 0) := by
      funext k
      simp
    -- Both sides compute to `n • f 0`.
    simp [apSumFrom, apSumOffset, apSum, hconst]
  · have hd₂ : d₂ > 0 := Nat.pos_of_ne_zero h0
    rcases ha with ⟨a₀, rfl⟩
    have hdiv : d₂ * a₀ / d₂ = a₀ := by
      -- rewrite to `a₀*d₂` and use `Nat.mul_div_right`.
      simpa [Nat.mul_comm] using (Nat.mul_div_right a₀ hd₂)
    -- Prevent simp from rewriting `apSumOffset _ _ 0 _` into `apSum`.
    simpa [hdiv, apSumOffset] using
      (apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul (f := f) (a₀ := a₀) (d₁ := d₁)
        (d₂ := d₂) (n := n))

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
