import Mathlib

/-!
# Discrepancy: basic definitions

These definitions are intended as **reusable verified substrate** for discrepancy-style problems.

Design principles:
- keep definitions small and composable
- avoid baking in problem-specific choices too early
- prefer ℕ-indexed sequences with ℤ values for summation convenience
-/

namespace MoltResearch

/-- A ±1-valued sequence on ℕ (values in ℤ). -/
def IsSignSequence (f : ℕ → ℤ) : Prop := ∀ n, f n = 1 ∨ f n = -1

/-- Sum of `f` along the homogeneous arithmetic progression `d, 2d, ..., nd`.

We use `Finset.range n` with `i+1` so the progression starts at `d`.
- `n = 0` yields sum 0.
-/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f ((i + 1) * d))

/-! ### Discrepancy definition and basic API -/

/-- A convenient wrapper for the absolute value of an arithmetic-progression sum.

It is defined as the natural absolute value of `apSum f d n`.
-/
def discrepancy (f : ℕ → ℤ) (d n : ℕ) : ℕ :=
  Int.natAbs (apSum f d n)

/-- Definitional lemma exposing the definition. -/
lemma discrepancy_eq_natAbs_apSum (f : ℕ → ℤ) (d n : ℕ) :
    discrepancy f d n = Int.natAbs (apSum f d n) :=
  rfl

/-- Alias for the definitional lemma. -/
@[deprecated "Use `discrepancy_eq_natAbs_apSum`." (since := "2026-04-17")]
lemma discrepancy_def (f : ℕ → ℤ) (d n : ℕ) :
    discrepancy f d n = Int.natAbs (apSum f d n) :=
  rfl

/-- `simp` bridge: `Int.natAbs (apSum …)` simplifies to the `discrepancy` wrapper.

This direction avoids simp loops with `discrepancy_def`.
-/
@[simp] lemma natAbs_apSum_eq_discrepancy (f : ℕ → ℤ) (d n : ℕ) :
    Int.natAbs (apSum f d n) = discrepancy f d n :=
  rfl

/-!
### `disc`: homogeneous discrepancy wrapper (API coherence)

This is a homogeneous analogue of `discOffset` with the same naming convention.

It intentionally duplicates `discrepancy` as a more symmetric counterpart to `discOffset`.

Naming guidance:
- Prefer `disc`/`discOffset`/`discOffsetUpTo` when you want a uniform family of wrappers.
- `discrepancy` is kept as a readable synonym for the homogeneous case.
-/

/-- Homogeneous discrepancy wrapper: `disc f d n = |apSum f d n|`. -/
def disc (f : ℕ → ℤ) (d n : ℕ) : ℕ :=
  Int.natAbs (apSum f d n)

/-- Definitional lemma exposing the definition. -/
lemma disc_eq_natAbs_apSum (f : ℕ → ℤ) (d n : ℕ) :
    disc f d n = Int.natAbs (apSum f d n) :=
  rfl

/-- Alias for the definitional lemma. -/
@[deprecated "Use `disc_eq_natAbs_apSum`." (since := "2026-04-17")]
lemma disc_def (f : ℕ → ℤ) (d n : ℕ) :
    disc f d n = Int.natAbs (apSum f d n) :=
  rfl

/-- `simp` bridge: `Int.natAbs (apSum …)` simplifies to the `disc` wrapper.

This direction avoids simp loops with `disc_def`.
-/
@[simp] lemma natAbs_apSum_eq_disc (f : ℕ → ℤ) (d n : ℕ) :
    Int.natAbs (apSum f d n) = disc f d n :=
  rfl

/-- Coherence lemma: the two homogeneous wrappers are definitionally the same.

This exists purely for API consistency; prefer rewriting goals to the `disc`-family wrappers when
working with `discOffset` / `discOffsetUpTo` pipelines.
-/
lemma discrepancy_eq_disc (f : ℕ → ℤ) (d n : ℕ) : discrepancy f d n = disc f d n := rfl

/-- Coherence lemma: the two homogeneous wrappers are definitionally the same. -/
lemma disc_eq_discrepancy (f : ℕ → ℤ) (d n : ℕ) : disc f d n = discrepancy f d n := rfl

/-- The discrepancy of an empty progression is zero. -/
@[simp] lemma disc_zero (f : ℕ → ℤ) (d : ℕ) : disc f d 0 = 0 := by
  unfold disc apSum
  simp

/-- The discrepancy of an empty progression is zero. -/
@[simp] lemma discrepancy_zero (f : ℕ → ℤ) (d : ℕ) : discrepancy f d 0 = 0 := by
  unfold discrepancy apSum
  simp

/-- Sum of `f` over the next `n` terms of the arithmetic progression after skipping `m` terms.

It is defined as `∑ i in range n, f ((m + i + 1) * d)`. -/
def apSumOffset (f : ℕ → ℤ) (d m n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f ((m + i + 1) * d))

/-!
### `apSumOffset` argument-order coherence helper (API coherence)

`apSumFrom` uses argument order `(a d n)`, i.e. “start, step, length”.

For the offset nucleus `apSumOffset`, the historical order is `(d m n)`.
This file keeps that order (it is used widely), but we also provide the alias
`apSumOffset'` with the more uniform order `(m d n)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Nucleus API coherence”.
-/

/-- Alias for `apSumOffset` with argument order `(m d n)`.

This is purely an API-coherence convenience so that the “offset” parameter sits next to the
“start” parameter of `apSumFrom` when you are switching between the two nuclei.
-/
def apSumOffset' (f : ℕ → ℤ) (m d n : ℕ) : ℤ :=
  apSumOffset f d m n

/-- Coherence lemma: `apSumOffset'` is definitionally `apSumOffset`. -/
lemma apSumOffset'_eq (f : ℕ → ℤ) (m d n : ℕ) :
    apSumOffset' f m d n = apSumOffset f d m n :=
  rfl

/-!
### Multiplicative dilation normal forms

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.

These lemmas package the common rewrite “pull a common factor into the step”.
We provide both a `mul_right` and a `mul_left` variant to avoid commutativity noise under binders.
-/

/-- Multiplicative dilation normal form for homogeneous AP sums (`mul_right` summand convention).

`apSum (fun k => f (k * q)) d n` samples indices `((i+1)*d)*q`, which canonically rewrite to
`(i+1)*(d*q)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.
-/
lemma apSum_map_mul_right (f : ℕ → ℤ) (q d n : ℕ) :
    apSum (fun k => f (k * q)) d n = apSum f (d * q) n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `((i+1)*d)*q = (i+1)*(d*q)`.
  simp [Nat.mul_assoc]

/-- Multiplicative dilation normal form for homogeneous AP sums (`mul_left` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.
-/
lemma apSum_map_mul_left (f : ℕ → ℤ) (q d n : ℕ) :
    apSum (fun k => f (q * k)) d n = apSum f (q * d) n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `q*((i+1)*d) = (i+1)*(q*d)`.
  simp [Nat.mul_assoc, Nat.mul_comm]

/-- Multiplicative dilation normal form for offset AP sums (`mul_right` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.
-/
lemma apSumOffset_map_mul_right (f : ℕ → ℤ) (q d m n : ℕ) :
    apSumOffset (fun k => f (k * q)) d m n = apSumOffset f (d * q) m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_assoc]

/-- Multiplicative dilation normal form for offset AP sums (`mul_left` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.
-/
lemma apSumOffset_map_mul_left (f : ℕ → ℤ) (q d m n : ℕ) :
    apSumOffset (fun k => f (q * k)) d m n = apSumOffset f (q * d) m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_assoc, Nat.mul_comm]

/-- Canonical homogeneous view of offsets: push the start shift `m*d` into the summand.

(Track B normal-form checklist item.)
-/
lemma apSumOffset_eq_apSum_shift_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  unfold apSumOffset apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `(m + i + 1) * d = m*d + (i+1)*d`.
  have hmul : (m + i + 1) * d = m * d + (i + 1) * d := by
    -- reassociate to `m + (i+1)` and apply `Nat.add_mul`.
    calc
      (m + i + 1) * d = (m + (i + 1)) * d := by
        simp [Nat.add_assoc]
      _ = m * d + (i + 1) * d := by
        simpa using (Nat.add_mul m (i + 1) d)
  -- commute the addition to match `k + m*d`.
  have h : (m + i + 1) * d = (i + 1) * d + m * d := by
    simpa [hmul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  simpa [h]

/-!
### Shift–dilation coherence (Track B)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Shift–dilation coherence lemma.

These lemmas package the arithmetic needed to freely reorder the two most common
normal-form rewrites:
- “shift the sequence” (push the offset `m*d` into the summand), and
- “pull a common factor into the step” (contract a `q` into the step).

They are deliberately phrased so downstream proofs can use them with `simp`/`simpa`
without redoing the algebra.
-/

/-- Shift–dilation coherence for `apSum`.

Rewriting by shifting first and then contracting a common factor into the step agrees with
contracting first (which scales the offset shift by `q`).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Shift–dilation coherence lemma.
-/
lemma apSum_shift_mul_right_comm (f : ℕ → ℤ) (d m n q : ℕ) :
    apSum (fun k => f ((k + m * d) * q)) d n =
      apSum (fun k => f (k + m * (d * q))) (d * q) n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Compare summands at index `i`.
  -- The two sampled indices are definitionally the same after reassociating:
  -- `(((i+1)*d + m*d) * q) = (i+1)*(d*q) + m*(d*q)`.
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Shift–dilation coherence for `apSumOffset`.

This is the preferred “commutation lemma” used by the nucleus normal-form pipeline:
first pushing the offset into the summand (shift) and then pulling a factor into the step (dilation)
matches pulling the factor first.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Shift–dilation coherence lemma.
-/
lemma apSumOffset_shift_mul_right_comm (f : ℕ → ℤ) (d m n q : ℕ) :
    apSumOffset (fun k => f (k * q)) d m n =
      apSum (fun k => f (k + m * (d * q))) (d * q) n := by
  -- Shift first, then use `apSum_shift_mul_right_comm`.
  simpa [apSumOffset_eq_apSum_shift_mul] using
    (apSum_shift_mul_right_comm (f := f) (d := d) (m := m) (n := n) (q := q))

/-! ### Support finset for AP sums -/

/-- `apSupport d m n` is the finite set of indices accessed by `apSumOffset f d m n`.

Concretely, it is the image of `Finset.range n` under the map `i ↦ (m + i + 1) * d`.

This is intended as a **normal-form support object** for local-surgery arguments: rather than
phrasing “agreement on the relevant indices” using `Icc` bookkeeping, downstream code can assume
pointwise agreement on `apSupport d m n`.

Note: this is a `Finset`, so it forgets multiplicity (if different `i` map to the same index,
the support still contains that index just once).
-/
def apSupport (d m n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => (m + i + 1) * d)

/-!
### “Offset is just tail” packaging lemma (Track B)

Downstream, we often want to push `apSupport d m n` into the explicit `Finset.range` image form
without unfolding the definition. This lemma is a stable, simp-friendly rewrite target.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Offset is just tail” for `apSupport`.
-/
lemma apSupport_eq_image_range (d m n : ℕ) :
    apSupport d m n = (Finset.range n).image (fun i => (m + i + 1) * d) := by
  rfl

/-- Degenerate case: no indices are accessed when `n = 0`. -/
@[simp] lemma apSupport_zero (d m : ℕ) : apSupport d m 0 = ∅ := by
  unfold apSupport
  simp

/-- If `i < n` then the corresponding index `(m + i + 1) * d` belongs to `apSupport d m n`. -/
lemma mem_apSupport_of_lt {i d m n : ℕ} (hi : i < n) :
    (m + i + 1) * d ∈ apSupport d m n := by
  unfold apSupport
  refine Finset.mem_image.2 ?_
  exact ⟨i, Finset.mem_range.2 hi, rfl⟩

/-!
### Cardinality bounds (Track B)

Checklist item: Problems/erdos_discrepancy.md (Track B) — `apSupport` cardinality bookkeeping.

Because `apSupport d m n` is defined as an image of `Finset.range n`, its cardinality is always
bounded by `n`. When `d > 0`, the sampling map `i ↦ (m + i + 1) * d` is injective, so the support
contains *exactly* `n` indices.
-/

/-- Basic bookkeeping: `apSupport d m n` has cardinality at most `n`. -/
lemma card_apSupport_le (d m n : ℕ) : (apSupport d m n).card ≤ n := by
  classical
  -- `card (image ...) ≤ card (range n) = n`.
  simpa [apSupport] using (Finset.card_image_le (s := Finset.range n)
    (f := fun i => (m + i + 1) * d))

/-- Exact cardinality when the step is positive (no multiplicities collapse). -/
lemma card_apSupport_eq (d m n : ℕ) (hd : d > 0) : (apSupport d m n).card = n := by
  classical
  -- The sampling map is injective when `d > 0`.
  have hinj : Function.Injective (fun i : ℕ => (m + i + 1) * d) := by
    intro i j hij
    have hmul : m + i + 1 = m + j + 1 := Nat.mul_right_cancel hd hij
    have hmul' : m + (i + 1) = m + (j + 1) := by
      simpa [Nat.add_assoc] using hmul
    have : i + 1 = j + 1 := Nat.add_left_cancel hmul'
    exact Nat.succ_inj.mp (by simpa using this)
  -- `card (image) = card (range n) = n`.
  simpa [apSupport] using
    (Finset.card_image_of_injective (s := Finset.range n)
      (f := fun i : ℕ => (m + i + 1) * d) hinj)

/-!
### Membership characterization (Track B)

This is a small “unfold-free” interface lemma for the `apSupport` support finset.

We keep the core lemma (`mem_apSupport_iff`) free of `[simp]` to avoid aggressive rewriting.
For simp-friendly rewriting in proofs, use the binder-notation variant `mem_apSupport` below.
-/

lemma mem_apSupport_iff {d m n x : ℕ} :
    x ∈ apSupport d m n ↔ ∃ i, i < n ∧ x = (m + i + 1) * d := by
  unfold apSupport
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.1 hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩

/-- Simp-friendly binder-notation membership characterization for `apSupport`.

This lemma rewrites `x ∈ apSupport d m n` into an existential over `i < n`.
It is stated without mentioning `Finset.image` so it can be used as a stable interface.
-/
lemma mem_apSupport {d m n x : ℕ} :
    x ∈ apSupport d m n ↔ ∃ i < n, x = (m + i + 1) * d := by
  simpa [and_left_comm, and_assoc, and_comm] using
    (mem_apSupport_iff (d := d) (m := m) (n := n) (x := x))

/-!
### Canonical membership normal form (Track B)

In downstream proofs, the most common membership query is for an index already in the
`(m + i + 1) * d` normal form.

When `d > 0`, the sampling map `i ↦ (m + i + 1) * d` is injective, so membership in the support
finset reduces to the expected bound `i < n`.
-/

@[simp] lemma mem_apSupport_index_iff {d m n i : ℕ} (hd : d > 0) :
    (m + i + 1) * d ∈ apSupport d m n ↔ i < n := by
  constructor
  · intro hx
    rcases (mem_apSupport_iff (d := d) (m := m) (n := n) (x := (m + i + 1) * d)).1 hx with
      ⟨j, hj, hji⟩
    have hmul : m + i + 1 = m + j + 1 := Nat.mul_right_cancel hd hji
    have : i = j := by
      -- Peel off the common offset `m`.
      have hmul' : m + (i + 1) = m + (j + 1) := by
        simpa [Nat.add_assoc] using hmul
      have : i + 1 = j + 1 := Nat.add_left_cancel hmul'
      exact Nat.succ_inj.mp this
    simpa [this] using hj
  · intro hi
    exact mem_apSupport_of_lt (d := d) (m := m) (n := n) (i := i) hi

/-!
### Support concatenation normal form (Track B)

When we split a length `(n+k)` AP sum into its first `n` terms and its last `k` terms, the
corresponding support finset splits as the union of two “block supports”.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Support concatenation normal form (`apSupport`).
-/

lemma apSupport_add (d m n k : ℕ) :
    apSupport d m (n + k) = apSupport d m n ∪ apSupport d (m + n) k := by
  ext x
  constructor
  · intro hx
    rcases (mem_apSupport_iff (d := d) (m := m) (n := n + k) (x := x)).1 hx with ⟨i, hi, rfl⟩
    by_cases hin : i < n
    · -- First block.
      exact (Finset.mem_union).2 (Or.inl (mem_apSupport_of_lt (d := d) (m := m) (n := n) (i := i) hin))
    · -- Second block: write `i = n + (i-n)`.
      have hle : n ≤ i := Nat.le_of_not_gt hin
      have hj : i - n < k := by
        have hnk : n + (i - n) < n + k := by
          -- rewrite `i` as `n + (i-n)` using `n ≤ i`.
          simpa [Nat.add_sub_of_le hle] using hi
        exact (Nat.add_lt_add_iff_left).1 hnk
      have hbase : m + i + 1 = m + n + (i - n) + 1 := by
        calc
          m + i + 1 = m + (n + (i - n)) + 1 := by
            simp [Nat.add_sub_of_le hle, Nat.add_assoc]
          _ = m + n + (i - n) + 1 := by
            simp [Nat.add_assoc]
      have hrewrite : (m + i + 1) * d = (m + n + (i - n) + 1) * d := by
        simpa [hbase]
      exact (Finset.mem_union).2 (Or.inr (by
        simpa [hrewrite] using
          (mem_apSupport_of_lt (d := d) (m := m + n) (n := k) (i := i - n) hj)))
  · intro hx
    rcases (Finset.mem_union).1 hx with hx | hx
    · -- Left block inclusion.
      rcases (mem_apSupport_iff (d := d) (m := m) (n := n) (x := x)).1 hx with ⟨i, hi, rfl⟩
      exact (mem_apSupport_iff (d := d) (m := m) (n := n + k) (x := (m + i + 1) * d)).2
        ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_add_right n k), rfl⟩
    · -- Right block inclusion.
      rcases (mem_apSupport_iff (d := d) (m := m + n) (n := k) (x := x)).1 hx with ⟨j, hj, rfl⟩
      refine (mem_apSupport_iff (d := d) (m := m) (n := n + k)
        (x := (m + n + j + 1) * d)).2 ?_
      refine ⟨n + j, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.add_lt_add_left hj n)
      · simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Cut-stability for support-form agreement hypotheses.

If `f` and `g` agree on the accessed indices for a length `(n+k)` block, then they agree on both
cut pieces; conversely, agreement on both cut pieces implies agreement on the whole block.

This is the key glue lemma for transporting “agree on accessed indices” assumptions through
cut/split normal forms such as `apSumOffset_add_len`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Cut-stability for `apSupport`.
-/
lemma apSupport_agree_add_iff {β : Type} (f g : ℕ → β) (d m n k : ℕ) :
    (∀ x ∈ apSupport d m (n + k), f x = g x) ↔
      (∀ x ∈ apSupport d m n, f x = g x) ∧ (∀ x ∈ apSupport d (m + n) k, f x = g x) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      -- Promote membership in the left block to membership in the full `(n+k)` support.
      have hx' : x ∈ apSupport d m n ∪ apSupport d (m + n) k := (Finset.mem_union).2 (Or.inl hx)
      have hx'' : x ∈ apSupport d m (n + k) := by
        simpa [apSupport_add (d := d) (m := m) (n := n) (k := k)] using hx'
      exact h x hx''
    · intro x hx
      have hx' : x ∈ apSupport d m n ∪ apSupport d (m + n) k := (Finset.mem_union).2 (Or.inr hx)
      have hx'' : x ∈ apSupport d m (n + k) := by
        simpa [apSupport_add (d := d) (m := m) (n := n) (k := k)] using hx'
      exact h x hx''
  · rintro ⟨h₁, h₂⟩ x hx
    have hx' : x ∈ apSupport d m n ∪ apSupport d (m + n) k := by
      simpa [apSupport_add (d := d) (m := m) (n := n) (k := k)] using hx
    rcases (Finset.mem_union).1 hx' with hxL | hxR
    · exact h₁ x hxL
    · exact h₂ x hxR

/-- Cut-stability for support-form agreement hypotheses (cut at `k ≤ n`).

This is a convenience wrapper around `apSupport_agree_add_iff` that matches the common
“prefix/suffix after a cut” shape used by `apSumOffset` cut/split lemmas.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Cut-stability for `apSupport` through cuts.
-/
lemma apSupport_agree_cut_iff {β : Type} (f g : ℕ → β) (d m n k : ℕ) (hk : k ≤ n) :
    (∀ x ∈ apSupport d m n, f x = g x) ↔
      (∀ x ∈ apSupport d m k, f x = g x) ∧ (∀ x ∈ apSupport d (m + k) (n - k), f x = g x) := by
  -- Rewrite `n` as `k + (n-k)` and apply the concatenation lemma.
  simpa [Nat.add_sub_of_le hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSupport_agree_add_iff (f := f) (g := g) (d := d) (m := m) (n := k) (k := n - k))


/-!
### Cardinality (Track B)

Assuming `d > 0`, the map `i ↦ (m + i + 1) * d` is injective, so the support finset contains
exactly `n` distinct indices.

(Track B normal-form checklist item: `apSupport` size API / no-collision guarantee.)
-/

lemma card_apSupport {d m n : ℕ} (hd : d > 0) : (apSupport d m n).card = n := by
  classical
  unfold apSupport
  have hinj : Function.Injective (fun i : ℕ => (m + i + 1) * d) := by
    intro i j hij
    have hmul : m + i + 1 = m + j + 1 := Nat.mul_right_cancel hd hij
    have hmul' : m + (i + 1) = m + (j + 1) := by
      simpa [Nat.add_assoc] using hmul
    have : i + 1 = j + 1 := Nat.add_left_cancel hmul'
    exact Nat.succ_inj.mp this
  simpa [Finset.card_range] using
    (Finset.card_image_of_injective (s := Finset.range n)
      (f := fun i : ℕ => (m + i + 1) * d) hinj)

/-!
### Paper-endpoint membership normal form (Track B)

Many later arguments phrase “agreement on accessed indices” in the paper endpoint convention
`m < i ∧ i ≤ m+n` for the *multiplier* index `i` (so the accessed sequence index is `i*d`).

This lemma provides an unfold-free bridge between:
- the nucleus support object `apSupport d m n`, and
- the paper-style endpoint bounds.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `apSupport` image membership normal form.
-/

lemma mem_apSupport_iff_exists_endpoints {d m n x : ℕ} :
    x ∈ apSupport d m n ↔ ∃ i, m < i ∧ i ≤ m + n ∧ x = i * d := by
  constructor
  · intro hx
    rcases (mem_apSupport_iff (d := d) (m := m) (n := n) (x := x)).1 hx with ⟨k, hk, rfl⟩
    refine ⟨m + k + 1, ?_, ?_, rfl⟩
    · -- `m < m+k+1`
      have : m < m + (k + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos k)
      simpa [Nat.add_assoc] using this
    · -- `m+k+1 ≤ m+n`
      have hk' : k + 1 ≤ n := Nat.succ_le_of_lt hk
      -- cancel the common `m`
      have : m + (k + 1) ≤ m + n := Nat.add_le_add_left hk' m
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  · rintro ⟨i, hmi, hile, rfl⟩
    -- Write `i = m + k + 1` using `m < i`.
    rcases Nat.exists_eq_add_of_lt hmi with ⟨k, rfl⟩
    -- From `m + k + 1 ≤ m + n` derive `k < n`.
    have hk1 : k + 1 ≤ n := by
      have : m + (k + 1) ≤ m + n := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hile
      exact Nat.add_le_add_iff_left.mp this
    have hk : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk1
    exact mem_apSupport_of_lt (d := d) (m := m) (n := n) (i := k) hk

/-- Monotonicity in the length parameter: the accessed-index set can only grow when `n` increases.

(Track B normal-form checklist item: support monotonicity API.)
-/
lemma apSupport_mono_right (d m n k : ℕ) : apSupport d m n ⊆ apSupport d m (n + k) := by
  intro x hx
  rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
  have hin : i < n := Finset.mem_range.1 hi
  have hin' : i < n + k := lt_of_lt_of_le hin (Nat.le_add_right n k)
  exact mem_apSupport_of_lt (d := d) (m := m) (n := n + k) (i := i) hin'

/-- `apSupport` at length `n+1` is obtained by inserting the new endpoint index.

This is designed to be a simp-friendly rewrite for local-surgery arguments.

(Track B normal-form checklist item: support monotonicity API.)
-/
@[simp] lemma apSupport_add_one (d m n : ℕ) :
    apSupport d m (n + 1) = insert ((m + n + 1) * d) (apSupport d m n) := by
  unfold apSupport
  simpa [Finset.range_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Version of `apSupport_add_one` phrased with the intended `d > 0` side-condition.

(Track B normal-form checklist item: support monotonicity API.)
-/
lemma apSupport_succ (d m n : ℕ) (hd : d > 0) :
    apSupport d m (n + 1) = insert ((m + n + 1) * d) (apSupport d m n) := by
  simpa using (apSupport_add_one (d := d) (m := m) (n := n))

/-!
### Coherence under shifts / dilations (Track B)

These lemmas explain how the normal-form support object `apSupport d m n` behaves under the two
most common index transforms:
- shifting the *offset* parameter `m` (equivalently: adding a multiple of the step `d` to indices),
- multiplying indices by a common factor (equivalently: pulling a factor into the step).
-/

/-- Shift coherence: increasing `m` by `k` shifts the accessed indices by `k*d`.

(Track B normal-form checklist item: `apSupport` coherence under shift.)
-/
lemma apSupport_add_left (d m n k : ℕ) :
    apSupport d (m + k) n = (apSupport d m n).image (fun x => x + k * d) := by
  classical
  unfold apSupport
  -- Prove set equality by membership; the arithmetic is handled by `simp`.
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
    have hi' : i < n := Finset.mem_range.1 hi
    refine Finset.mem_image.2 ?_
    refine ⟨(m + i + 1) * d, mem_apSupport_of_lt (d := d) (m := m) (n := n) (i := i) hi', ?_⟩
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul]
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨i, hi, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨i, hi, ?_⟩
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul]

/-- Cardinalities of filtered supports commute with shifting the offset parameter.

This is the “translation” half of the Track B contracted-support API.
-/
lemma card_apSupport_add_left_filter (d m n k : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((apSupport d (m + k) n).filter p).card =
      ((apSupport d m n).filter (fun x => p (x + k * d))).card := by
  classical
  have hinj : Function.Injective (fun x : ℕ => x + k * d) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  -- Rewrite `apSupport d (m+k) n` as an image and cancel cardinality via injectivity.
  have hfilter : (apSupport d (m + k) n).filter p =
      ((apSupport d m n).filter (fun x => p (x + k * d))).image (fun x => x + k * d) := by
    classical
    ext x
    constructor
    · intro hx
      have hxSupp : x ∈ apSupport d (m + k) n := (Finset.mem_filter.1 hx).1
      have hpx : p x := (Finset.mem_filter.1 hx).2
      have : x ∈ (apSupport d m n).image (fun y => y + k * d) := by
        simpa [apSupport_add_left (d := d) (m := m) (n := n) (k := k)] using hxSupp
      rcases Finset.mem_image.1 this with ⟨y, hy, rfl⟩
      refine Finset.mem_image.2 ?_
      refine ⟨y, Finset.mem_filter.2 ?_, rfl⟩
      exact ⟨hy, by simpa using hpx⟩
    · intro hx
      rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
      have hy' := Finset.mem_filter.1 hy
      have hySupp : y ∈ apSupport d m n := hy'.1
      have hpy : p (y + k * d) := hy'.2
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, hpy⟩
      have : y + k * d ∈ (apSupport d m n).image (fun z => z + k * d) :=
        Finset.mem_image.2 ⟨y, hySupp, rfl⟩
      simpa [apSupport_add_left (d := d) (m := m) (n := n) (k := k)] using this

  calc
    ((apSupport d (m + k) n).filter p).card =
        (((apSupport d m n).filter (fun x => p (x + k * d))).image (fun x => x + k * d)).card := by
          simp [hfilter]
    _ = ((apSupport d m n).filter (fun x => p (x + k * d))).card := by
          simpa using (Finset.card_image_of_injective _ hinj)

/-- In particular, shifting the offset parameter does not change the support size. -/
lemma card_apSupport_add_left (d m n k : ℕ) :
    (apSupport d (m + k) n).card = (apSupport d m n).card := by
  simpa using (card_apSupport_add_left_filter (d := d) (m := m) (n := n) (k := k)
    (p := fun _ => True))

/-- Dilation coherence: pulling a common factor into the step multiplies the support indices.

(Track B normal-form checklist item: `apSupport` coherence under dilation.)
-/
lemma apSupport_mul_right (d m n q : ℕ) :
    apSupport (d * q) m n = (apSupport d m n).image (fun x => x * q) := by
  classical
  unfold apSupport
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
    have hi' : i < n := Finset.mem_range.1 hi
    refine Finset.mem_image.2 ?_
    refine ⟨(m + i + 1) * d, mem_apSupport_of_lt (d := d) (m := m) (n := n) (i := i) hi', ?_⟩
    simp [Nat.mul_assoc]
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨i, hi, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨i, hi, ?_⟩
    simp [Nat.mul_assoc]

/-! ### Degenerate-parameter simp lemmas (Track B)

These provide a small simp surface so “start-shift” and “dilation” bookkeeping doesn't force
unfolding `apSupport`.

We keep them minimal to avoid simp loops.
-/

@[simp] lemma apSupport_add_left_zero (d m n : ℕ) :
    apSupport d (m + 0) n = apSupport d m n := by
  simpa using (apSupport_add_left (d := d) (m := m) (n := n) (k := 0))

@[simp] lemma apSupport_mul_right_one (d m n : ℕ) :
    apSupport (d * 1) m n = apSupport d m n := by
  simpa [Nat.mul_one] using (apSupport_mul_right (d := d) (m := m) (n := n) (q := 1))

/-!
### “Contracted support” API (Track B)

When rewriting a discrepancy statement by “contracting” a common factor `q` into the step
(e.g. rewriting `d*q` ↔ `d` via a change of variables), we often want to transport hypotheses
stated on the support object `apSupport`.

The lemmas below package the two key facts needed for this transport:
- filtering `apSupport (d*q) m n` by a predicate `p` is the same as filtering `apSupport d m n`
  by the pulled-back predicate `x ↦ p (x*q)` and then mapping by `x ↦ x*q`;
- consequently, cardinality bounds on filtered supports commute with the contraction rewrite.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Contracted support” API.
-/

/-- A filtered `apSupport (d*q) m n` is the image of the corresponding filtered `apSupport d m n`
under multiplication by `q`.

We assume `q > 0` so that multiplication by `q` is injective and hence preserves cardinalities.
-/
lemma apSupport_mul_right_filter (d m n q : ℕ) (p : ℕ → Prop) [DecidablePred p] (hq : q > 0) :
    (apSupport (d * q) m n).filter p =
      ((apSupport d m n).filter (fun x => p (x * q))).image (fun x => x * q) := by
  classical
  ext x
  constructor
  · intro hx
    have hx' : x ∈ apSupport (d * q) m n := (Finset.mem_filter.1 hx).1
    have hpx : p x := (Finset.mem_filter.1 hx).2
    -- Use the dilation coherence to pull back membership to `apSupport d m n`.
    have : x ∈ (apSupport d m n).image (fun y => y * q) := by
      simpa [apSupport_mul_right (d := d) (m := m) (n := n) (q := q)] using hx'
    rcases Finset.mem_image.1 this with ⟨y, hy, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨y, Finset.mem_filter.2 ?_, rfl⟩
    exact ⟨hy, by simpa using hpx⟩
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
    have hy' := Finset.mem_filter.1 hy
    have hySupp : y ∈ apSupport d m n := hy'.1
    have hpy : p (y * q) := hy'.2
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, hpy⟩
    -- Push membership forward via the dilation coherence lemma.
    have : y * q ∈ (apSupport d m n).image (fun z => z * q) := Finset.mem_image.2 ⟨y, hySupp, rfl⟩
    simpa [apSupport_mul_right (d := d) (m := m) (n := n) (q := q)] using this

/-- Cardinalities of filtered supports commute with the dilation/contract rewrite.

This is the typical form needed to rewrite `card` hypotheses in edit-sensitivity arguments.
-/
lemma card_apSupport_mul_right_filter (d m n q : ℕ) (p : ℕ → Prop) [DecidablePred p] (hq : q > 0) :
    ((apSupport (d * q) m n).filter p).card =
      ((apSupport d m n).filter (fun x => p (x * q))).card := by
  classical
  -- Rewrite the filtered support as an image, then use injectivity of `x ↦ x*q`.
  have hinj : Function.Injective (fun x : ℕ => x * q) := by
    intro a b hab
    exact Nat.mul_right_cancel hq hab
  -- Use `apSupport_mul_right_filter` to rewrite, then cancel the image cardinality.
  calc
    ((apSupport (d * q) m n).filter p).card =
        (((apSupport d m n).filter (fun x => p (x * q))).image (fun x => x * q)).card := by
          simp [apSupport_mul_right_filter (d := d) (m := m) (n := n) (q := q) (p := p) hq]
    _ = ((apSupport d m n).filter (fun x => p (x * q))).card := by
          simpa using (Finset.card_image_of_injective _ hinj)

/-- In particular, dilation does not change the size of the support finset (when `q > 0`). -/
lemma card_apSupport_mul_right (d m n q : ℕ) (hq : q > 0) :
    (apSupport (d * q) m n).card = (apSupport d m n).card := by
  simpa using (card_apSupport_mul_right_filter (d := d) (m := m) (n := n) (q := q)
    (p := fun _ => True) hq)

/-- Shift normal form for offset AP sums: shifting the sequence by `k*d` is equivalent to
shifting the offset parameter `m` by `k`.

This is a one-line corollary used in local-surgery pipelines.

(Track B normal-form checklist item: `apSupport` coherence under shift/dilation.)
-/
lemma apSumOffset_map_add_mul (f : ℕ → ℤ) (k d m n : ℕ) :
    apSumOffset (fun t => f (t + k * d)) d m n = apSumOffset f d (m + k) n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Normalize `((m+k+i+1)*d)` into `((m+i+1)*d) + k*d`.
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul]

/-- Support-form congruence lemma: if `f` and `g` agree on every element of `apSupport d m n`,
then `apSumOffset f d m n = apSumOffset g d m n`.

This is a convenience wrapper around `apSumOffset_congr`.
-/
lemma apSumOffset_congr_support (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ x ∈ apSupport d m n, f x = g x) :
    apSumOffset f d m n = apSumOffset g d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.1 hi
  have hx : (m + i + 1) * d ∈ apSupport d m n := mem_apSupport_of_lt (d := d) (m := m) (n := n)
    (i := i) hi'
  exact h _ hx

/-- Support-form congruence lemma for `apSum` (i.e. `m = 0`), expressed via `apSupport`. -/
lemma apSum_congr_support (f g : ℕ → ℤ) (d n : ℕ)
    (h : ∀ x ∈ apSupport d 0 n, f x = g x) :
    apSum f d n = apSum g d n := by
  -- `apSum f d n` is definitionally `apSumOffset f d 0 n`.
  simpa [apSum, apSumOffset] using
    (apSumOffset_congr_support (f := f) (g := g) (d := d) (m := 0) (n := n) (h := h))

/-! ### Restriction to a finite window (support-form) -/

/-- Restricting `f` to `apSupport d m n` (with default value `0` outside the support)
does not change `apSumOffset f d m n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Restriction to finite window” API.
-/
lemma apSumOffset_restrict_support (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun x => if x ∈ apSupport d m n then f x else 0) d m n = apSumOffset f d m n := by
  -- The summand indices are always in `apSupport d m n`.
  refine (apSumOffset_congr_support (f := fun x => if x ∈ apSupport d m n then f x else 0)
      (g := f) (d := d) (m := m) (n := n) ?_)
  intro x hx
  simp [hx]

/-- Restricting `f` to `apSupport d 0 n` (with default value `0` outside the support)
does not change `apSum f d n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Restriction to finite window” API.
-/
lemma apSum_restrict_support (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun x => if x ∈ apSupport d 0 n then f x else 0) d n = apSum f d n := by
  -- `apSum f d n` is definitionally `apSumOffset f d 0 n`.
  simpa [apSum, apSumOffset] using
    (apSumOffset_restrict_support (f := f) (d := d) (m := 0) (n := n))

/-- Restricting `f` to `apSupport d 0 n` (with default value `0` outside the support)
does not change `disc f d n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Restriction to finite window” API.
-/
lemma disc_restrict_support (f : ℕ → ℤ) (d n : ℕ) :
    disc (fun x => if x ∈ apSupport d 0 n then f x else 0) d n = disc f d n := by
  unfold disc
  simp [apSum_restrict_support]

/-- A convenient wrapper for the absolute value of an offset arithmetic-progression sum.

It is defined as the natural absolute value of `apSumOffset f d m n`.
-/
def discOffset (f : ℕ → ℤ) (d m n : ℕ) : ℕ :=
  Int.natAbs (apSumOffset f d m n)

/-- Alias for `discOffset` with argument order `(m d n)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Nucleus API coherence”.
-/
def discOffset' (f : ℕ → ℤ) (m d n : ℕ) : ℕ :=
  discOffset f d m n

/-- Coherence lemma: `discOffset'` is definitionally `discOffset`. -/
lemma discOffset'_eq (f : ℕ → ℤ) (m d n : ℕ) :
    discOffset' f m d n = discOffset f d m n :=
  rfl

/-!
### Multiplicative dilation normal forms (`discOffset` / `discOffsetUpTo`)

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.

These are the wrapper-level analogues of `apSumOffset_map_mul_right` / `apSumOffset_map_mul_left`.
We keep them as plain rewrite lemmas (not `[simp]`) to avoid creating rewrite loops.
-/

/-- Dilation normal form for `discOffset` (`mul_right` summand convention).

`discOffset (fun k => f (k*q)) d m n` samples indices `((m+i+1)*d)*q`, which canonically rewrite to
`(m+i+1)*(d*q)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffset_map_mul_right (f : ℕ → ℤ) (q d m n : ℕ) :
    discOffset (fun k => f (k * q)) d m n = discOffset f (d * q) m n := by
  unfold discOffset
  simp [apSumOffset_map_mul_right]

/-- Dilation normal form for `discOffset` (`mul_left` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffset_map_mul_left (f : ℕ → ℤ) (q d m n : ℕ) :
    discOffset (fun k => f (q * k)) d m n = discOffset f (q * d) m n := by
  unfold discOffset
  simp [apSumOffset_map_mul_left]

/-- Shift–dilation coherence for the discrepancy wrapper `discOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Shift–dilation coherence lemma.
-/
lemma discOffset_shift_mul_right_comm (f : ℕ → ℤ) (d m n q : ℕ) :
    discOffset (fun k => f (k * q)) d m n =
      Int.natAbs (apSum (fun k => f (k + m * (d * q))) (d * q) n) := by
  unfold discOffset
  simp [apSumOffset_shift_mul_right_comm]

/-- `discOffset` on a constant sequence computes to `|n * c|` (independent of the offset `m` and step `d`).

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Constant/periodic sequence sanity checks: explicit computed examples for `apSum`/`discOffset`”.
-/
lemma discOffset_const (c : ℤ) (d m n : ℕ) :
    discOffset (fun _ => c) d m n = Int.natAbs ((n : ℤ) * c) := by
  unfold discOffset apSumOffset
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- `discOffset` on the constant sequence `1` computes to `n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Constant/periodic sequence sanity checks: explicit computed examples for `apSum`/`discOffset`”.
-/
@[simp] lemma discOffset_const_one (d m n : ℕ) :
    discOffset (fun _ => (1 : ℤ)) d m n = n := by
  simpa [discOffset_const]

/-- `discOffset` on the constant sequence `-1` also computes to `n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Constant/periodic sequence sanity checks: explicit computed examples for `apSum`/`discOffset`”.
-/
@[simp] lemma discOffset_const_neg_one (d m n : ℕ) :
    discOffset (fun _ => (-1 : ℤ)) d m n = n := by
  simpa [discOffset_const]

/-!
### Discrepancy up to a finite length

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/

/-- Maximal homogeneous discrepancy over lengths `n ≤ N`.

This is packaged in a finitary form (a `Finset.sup` over `range (N+1)`) so it is computable.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
def discUpTo (f : ℕ → ℤ) (d N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup (fun n => disc f d n)

/-- Maximal offset discrepancy over lengths `n ≤ N`.

This is packaged in a finitary form (a `Finset.sup` over `range (N+1)`) so it is computable.
-/
def discOffsetUpTo (f : ℕ → ℤ) (d m N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup (fun n => discOffset f d m n)

/-!
### Multiplicative dilation normal forms (`discOffsetUpTo`)

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.

These are the wrapper-level analogues of `discOffset_map_mul_right` / `discOffset_map_mul_left`.
We keep them as plain rewrite lemmas (not `[simp]`) to avoid creating rewrite loops.
-/

/-- Dilation normal form for `discOffsetUpTo` (`mul_right` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffsetUpTo_map_mul_right (f : ℕ → ℤ) (q d m N : ℕ) :
    discOffsetUpTo (fun k => f (k * q)) d m N = discOffsetUpTo f (d * q) m N := by
  classical
  unfold discOffsetUpTo
  simp [discOffset_map_mul_right]

/-- Dilation normal form for `discOffsetUpTo` (`mul_left` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffsetUpTo_map_mul_left (f : ℕ → ℤ) (q d m N : ℕ) :
    discOffsetUpTo (fun k => f (q * k)) d m N = discOffsetUpTo f (q * d) m N := by
  classical
  unfold discOffsetUpTo
  simp [discOffset_map_mul_left]

/-!
#### Step-scaling rewrite wrappers (orientation helpers)

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.

Downstream normal-form code often has the *step* written as `d*q`/`q*d` already and wants to
rewrite the expression into a form where the step multiplier is pushed into the function
argument (`k ↦ k*q` or `k ↦ q*k`).  The core lemmas above are oriented the other way, so we
provide these tiny wrappers for ergonomic rewriting.

These are **not** tagged `[simp]`.
-/

/-- Rewrite a multiplied step `d*q` into a multiplied input (`mul_right` convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffsetUpTo_step_mul_right (f : ℕ → ℤ) (q d m N : ℕ) :
    discOffsetUpTo f (d * q) m N = discOffsetUpTo (fun k => f (k * q)) d m N := by
  simpa using (discOffsetUpTo_map_mul_right (f := f) (q := q) (d := d) (m := m) (N := N)).symm

/-- Rewrite a multiplied step `q*d` into a multiplied input (`mul_left` convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffsetUpTo_step_mul_left (f : ℕ → ℤ) (q d m N : ℕ) :
    discOffsetUpTo f (q * d) m N = discOffsetUpTo (fun k => f (q * k)) d m N := by
  simpa using (discOffsetUpTo_map_mul_left (f := f) (q := q) (d := d) (m := m) (N := N)).symm

/-!
### `discOffsetUpTo` length-scaling normalization lemmas

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.

These are intentionally tiny rewrite lemmas: they normalize the *length* argument when it is
written as `q * N` (or `q * (N+1)`), so downstream code doesn’t need to do ad-hoc `Nat` algebra.

They are **not** tagged `[simp]` to avoid rewrite loops.
-/

lemma discOffsetUpTo_length_mul_comm (f : ℕ → ℤ) (d m q N : ℕ) :
    discOffsetUpTo f d m (q * N) = discOffsetUpTo f d m (N * q) := by
  simpa [Nat.mul_comm] using
    (rfl : discOffsetUpTo f d m (q * N) = discOffsetUpTo f d m (q * N))

lemma discOffsetUpTo_length_mul_succ_comm (f : ℕ → ℤ) (d m q N : ℕ) :
    discOffsetUpTo f d m (q * (N + 1)) = discOffsetUpTo f d m ((N + 1) * q) := by
  simpa [Nat.mul_comm] using
    (rfl : discOffsetUpTo f d m (q * (N + 1)) = discOffsetUpTo f d m (q * (N + 1)))

/-!
### `discOffsetUpTo` argument-order coherence helper (API coherence)

The historical argument order for the offset-up-to wrapper is `(d m N)`, matching `discOffset`.
For the same reason we provide `discOffset'`, we also provide the alias `discOffsetUpTo'` with the
more uniform order `(m d N)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Nucleus API coherence”.
-/

/-- Alias for `discOffsetUpTo` with argument order `(m d N)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Nucleus API coherence”.
-/
def discOffsetUpTo' (f : ℕ → ℤ) (m d N : ℕ) : ℕ :=
  discOffsetUpTo f d m N

/-- Coherence lemma: `discOffsetUpTo'` is definitionally `discOffsetUpTo`. -/
lemma discOffsetUpTo'_eq (f : ℕ → ℤ) (m d N : ℕ) :
    discOffsetUpTo' f m d N = discOffsetUpTo f d m N :=
  rfl

/-!
### `UpTo` API coherence simp lemmas (degenerate parameters)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Stable surface coherence for `UpTo` API.

These are deliberately small and oriented for `simp`:
- normalize away a spurious `m = 0` offset
- compute the degenerate cutoff `N = 0`

We are conservative here: these lemmas should be obviously terminating and orientation-safe.
-/

/-- `discUpTo` at cutoff `N = 0` is just `disc f d 0 = 0`. -/
@[simp] lemma discUpTo_zero (f : ℕ → ℤ) (d : ℕ) : discUpTo f d 0 = 0 := by
  classical
  simp [discUpTo]

/-- `discOffsetUpTo` at cutoff `N = 0` is just `discOffset f d m 0 = 0`. -/
@[simp] lemma discOffsetUpTo_zero (f : ℕ → ℤ) (d m : ℕ) : discOffsetUpTo f d m 0 = 0 := by
  classical
  -- `range (0+1)` is the singleton `{0}`.
  unfold discOffsetUpTo
  -- Reduce to `discOffset f d m 0 = 0` by computation.
  simp [discOffset, apSumOffset]

/-- Coherence: a spurious `m = 0` offset in `discOffsetUpTo` normalizes to `discUpTo`. -/
@[simp] lemma discOffsetUpTo_zero_start (f : ℕ → ℤ) (d N : ℕ) :
    discOffsetUpTo f d 0 N = discUpTo f d N := by
  classical
  unfold discOffsetUpTo discUpTo
  -- `discOffset f d 0 n` is definitionally `disc f d n`.
  simp [discOffset, disc, apSumOffset, apSum]

/-!
### Dilation/coarsening convenience wrappers

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.

These lemmas let downstream code rewrite `discOffsetUpTo` under a multiplicative dilation
`k ↦ q*k` of the underlying sequence, without mixing in manual `Nat` algebra.
They are oriented and marked `[simp]` so `simp` can normalize the dilated form.
-/

/-- Pull a dilation factor `q` out of the step size argument of `apSumOffset`. -/
@[simp] lemma apSumOffset_dilate_mul (f : ℕ → ℤ) (q d m n : ℕ) :
    apSumOffset (fun k => f (q * k)) d m n = apSumOffset f (q * d) m n := by
  unfold apSumOffset
  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Pull a dilation factor `q` out of the step size argument of `discOffset`. -/
@[simp] lemma discOffset_dilate_mul (f : ℕ → ℤ) (q d m n : ℕ) :
    discOffset (fun k => f (q * k)) d m n = discOffset f (q * d) m n := by
  unfold discOffset
  simp [apSumOffset_dilate_mul]

/-- Pull a dilation factor `q` out of the step size argument of `discOffsetUpTo`. -/
@[simp] lemma discOffsetUpTo_dilate_mul (f : ℕ → ℤ) (q d m N : ℕ) :
    discOffsetUpTo (fun k => f (q * k)) d m N = discOffsetUpTo f (q * d) m N := by
  classical
  unfold discOffsetUpTo
  simp [discOffset_dilate_mul]

/-!
### Degenerate-step (`d = 0`) normal forms

Checklist item: Problems/erdos_discrepancy.md (Track B) —
Degenerate-step normal forms (`d = 0`).

When the step is `0`, every index in the progression is `0`.
These lemmas provide a preferred simp/rewrite API so downstream code can normalize the `d = 0`
case without ad-hoc arithmetic.

We keep these lemmas forward-oriented and obviously terminating.
-/

@[simp] lemma apSum_zero_step (f : ℕ → ℤ) (n : ℕ) :
    apSum f 0 n = (n : ℤ) * f 0 := by
  unfold apSum
  -- `(i+1) * 0 = 0`, so this is a constant-sum over `range n`.
  simp

@[simp] lemma apSumOffset_zero_step (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 0 m n = (n : ℤ) * f 0 := by
  unfold apSumOffset
  -- `(m+i+1) * 0 = 0`, so this is also a constant-sum.
  simp

@[simp] lemma discOffset_zero_step (f : ℕ → ℤ) (m n : ℕ) :
    discOffset f 0 m n = Int.natAbs ((n : ℤ) * f 0) := by
  unfold discOffset
  simp

/-!
### Step-one (`d = 1`) coherence simp lemmas

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“API coherence for degenerate parameters at max-level”.

When the step is `1`, an offset progression is just a shift of the underlying sequence.
These lemmas expose that shift at the wrapper level, in `simp`-friendly normal form.
-/

/-- Step-one coherence: absorb the offset into a shift of the underlying sequence. -/
@[simp] lemma apSumOffset_one_shift (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 1 m n = apSum (fun k => f (k + m)) 1 n := by
  unfold apSumOffset apSum
  -- Both sides are `Finset.range n` sums; normalize arithmetic and `* 1`.
  simp [Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Step-one coherence: `discOffset` is just `disc` on the shifted sequence. -/
@[simp] lemma discOffset_one_shift (f : ℕ → ℤ) (m n : ℕ) :
    discOffset f 1 m n = disc (fun k => f (k + m)) 1 n := by
  unfold discOffset disc
  simp [apSumOffset_one_shift]

/-- Step-one coherence: `discOffsetUpTo` is `discUpTo` on the shifted sequence. -/
@[simp] lemma discOffsetUpTo_one_shift (f : ℕ → ℤ) (m N : ℕ) :
    discOffsetUpTo f 1 m N = discUpTo (fun k => f (k + m)) 1 N := by
  classical
  unfold discOffsetUpTo discUpTo
  simp [discOffset_one_shift]

/-- Max-recursion normal form for `discOffsetUpTo`.

This is the finitary analogue of “the max up to `N+1` is either the max up to `N` or the new value
at `N+1`”.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` max-recursion normal form.
-/
lemma discOffsetUpTo_succ (f : ℕ → ℤ) (d m N : ℕ) :
    discOffsetUpTo f d m (N + 1) =
      max (discOffsetUpTo f d m N) (discOffset f d m (N + 1)) := by
  classical
  unfold discOffsetUpTo
  -- `range ((N+1)+1) = insert (N+1) (range (N+1))`.
  -- Then `Finset.sup_insert` computes the new supremum as a `max`.
  simpa [Finset.range_add_one, max_comm, max_left_comm, max_assoc]

/-- Start-shift vs sequence-shift coherence at max level.

Normal form: rewriting a start advance `m ↦ m + k` is equivalent to shifting the underlying
sequence by `k*d`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Start-shift vs sequence-shift coherence
at the max level”.
-/
lemma discOffsetUpTo_add_start (f : ℕ → ℤ) (d m k N : ℕ) :
    discOffsetUpTo f d (m + k) N = discOffsetUpTo (fun t => f (t + k * d)) d m N := by
  classical
  unfold discOffsetUpTo
  -- Pointwise, `discOffset` is definitionally `Int.natAbs (apSumOffset ...)` and
  -- `apSumOffset_map_add_mul` performs the start/sequence shift rewrite.
  simp [discOffset, apSumOffset_map_add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Any particular `disc f d n` with `n ≤ N` is bounded by `discUpTo f d N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
lemma disc_le_discUpTo (f : ℕ → ℤ) (d n N : ℕ) (hn : n ≤ N) :
    disc f d n ≤ discUpTo f d N := by
  classical
  unfold discUpTo
  have hn' : n ∈ Finset.range (N + 1) := by
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hn)
  simpa using (Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => disc f d t) hn')

/-- Monotonicity in the cutoff: increasing `N` can only increase `discUpTo`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
lemma discUpTo_mono (f : ℕ → ℤ) (d : ℕ) {N N' : ℕ} (h : N ≤ N') :
    discUpTo f d N ≤ discUpTo f d N' := by
  classical
  unfold discUpTo
  refine Finset.sup_le ?_
  intro n hn
  have hnlt : n < N + 1 := Finset.mem_range.1 hn
  have hnlt' : n < N' + 1 := lt_of_lt_of_le hnlt (Nat.succ_le_succ h)
  have hn' : n ∈ Finset.range (N' + 1) := Finset.mem_range.2 hnlt'
  exact Finset.le_sup (s := Finset.range (N' + 1)) (f := fun t => disc f d t) hn'

/-- The maximum in `discUpTo` is attained by some `n ≤ N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
lemma exists_disc_eq_discUpTo (f : ℕ → ℤ) (d N : ℕ) :
    ∃ n ≤ N, disc f d n = discUpTo f d N := by
  classical
  unfold discUpTo
  have hne : (Finset.range (N + 1)).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  rcases Finset.exists_mem_eq_sup (s := Finset.range (N + 1)) (f := fun t => disc f d t) hne with
    ⟨n, hnmem, hsup⟩
  refine ⟨n, ?_, ?_⟩
  · exact Nat.le_of_lt_succ (Finset.mem_range.1 hnmem)
  · exact hsup.symm

/-- Any particular `discOffset f d m n` with `n ≤ N` is bounded by `discOffsetUpTo f d m N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
lemma discOffset_le_discOffsetUpTo (f : ℕ → ℤ) (d m n N : ℕ) (hn : n ≤ N) :
    discOffset f d m n ≤ discOffsetUpTo f d m N := by
  classical
  unfold discOffsetUpTo
  -- `n ≤ N` implies `n ∈ range (N+1)`.
  have hn' : n ∈ Finset.range (N + 1) := by
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hn)
  simpa using (Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => discOffset f d m t) hn')

/-- Convenience wrapper: a tail discrepancy is always bounded by the corresponding `UpTo` cutoff.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` ≤ `discOffsetUpTo` wrapper.
-/
lemma discOffset_le_discOffsetUpTo_self (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n ≤ discOffsetUpTo f d m n := by
  simpa using
    (discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := n) (N := n) (le_rfl))

/-- Monotonicity in the cutoff: increasing `N` can only increase `discOffsetUpTo`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
lemma discOffsetUpTo_mono (f : ℕ → ℤ) (d m : ℕ) {N N' : ℕ} (h : N ≤ N') :
    discOffsetUpTo f d m N ≤ discOffsetUpTo f d m N' := by
  classical
  unfold discOffsetUpTo
  -- Show every element of `range (N+1)` is ≤ the `sup` over `range (N'+1)`.
  refine Finset.sup_le ?_
  intro n hn
  have hnlt : n < N + 1 := Finset.mem_range.1 hn
  have hnlt' : n < N' + 1 := lt_of_lt_of_le hnlt (Nat.succ_le_succ h)
  have hn' : n ∈ Finset.range (N' + 1) := Finset.mem_range.2 hnlt'
  exact Finset.le_sup (s := Finset.range (N' + 1)) (f := fun t => discOffset f d m t) hn'

/-- A convenience wrapper: extending the cutoff by `K` can only increase `discOffsetUpTo`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` monotone in length.
-/
lemma discOffsetUpTo_le_add (f : ℕ → ℤ) (d m N K : ℕ) :
    discOffsetUpTo f d m N ≤ discOffsetUpTo f d m (N + K) := by
  simpa using
    (discOffsetUpTo_mono (f := f) (d := d) (m := m) (N := N) (N' := N + K) (Nat.le_add_right N K))

/-- Convenience wrapper: `discOffsetUpTo` is monotone under multiplicative length scaling `N ↦ N*q`
when `q > 0`.

This is the “length scaling” half of the `discOffsetUpTo` dilation/coarsening checklist item.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` dilation/coarsening convenience wrappers.
-/
lemma discOffsetUpTo_le_mul (f : ℕ → ℤ) (d m N q : ℕ) (hq : q > 0) :
    discOffsetUpTo f d m N ≤ discOffsetUpTo f d m (N * q) := by
  -- monotonicity + `N ≤ N*q` for `q > 0`
  refine discOffsetUpTo_mono (f := f) (d := d) (m := m) (N := N) (N' := N * q) ?_
  simpa [Nat.mul_comm] using (Nat.le_mul_of_pos_left N hq)

/-- Convenience: `discOffsetUpTo` is monotone under `N ↦ N+1`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` monotone in the cutoff.
-/
lemma discOffsetUpTo_le_succ (f : ℕ → ℤ) (d m N : ℕ) :
    discOffsetUpTo f d m N ≤ discOffsetUpTo f d m (N + 1) := by
  simpa using (discOffsetUpTo_le_add (f := f) (d := d) (m := m) (N := N) (K := 1))

/-- Convenience: `discOffsetUpTo` is monotone under `N ↦ Nat.succ N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` monotone in the cutoff.
-/
lemma discOffsetUpTo_le_succNat (f : ℕ → ℤ) (d m N : ℕ) :
    discOffsetUpTo f d m N ≤ discOffsetUpTo f d m (Nat.succ N) := by
  simpa [Nat.succ_eq_add_one] using (discOffsetUpTo_le_succ (f := f) (d := d) (m := m) (N := N))

/-- The maximum in `discOffsetUpTo` is attained by some `n ≤ N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API.
-/
lemma exists_discOffset_eq_discOffsetUpTo (f : ℕ → ℤ) (d m N : ℕ) :
    ∃ n ≤ N,
      discOffset f d m n = discOffsetUpTo f d m N ∧
      ∀ n' ≤ N, discOffset f d m n' ≤ discOffset f d m n := by
  classical
  unfold discOffsetUpTo
  -- `range (N+1)` is nonempty, so `sup` is attained.
  have hne : (Finset.range (N + 1)).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  -- Use the standard `sup`-attainment lemma.
  rcases Finset.exists_mem_eq_sup (s := Finset.range (N + 1)) (f := fun t => discOffset f d m t) hne with
    ⟨n, hnmem, hsup⟩
  refine ⟨n, ?_, ?_⟩
  · -- `n ∈ range (N+1)` implies `n ≤ N`.
    exact Nat.le_of_lt_succ (Finset.mem_range.1 hnmem)
  · refine ⟨hsup.symm, ?_⟩
    intro n' hn'le
    have hn'mem : n' ∈ Finset.range (N + 1) := by
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hn'le)
    have hle :=
      Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => discOffset f d m t) hn'mem
    simpa [hsup.symm] using hle

/-- In a fixed residue class modulo `q`, the maximum in `discUpTo` is attained by some `n ≤ N`.

This is a residue-friendly witness-extraction lemma: rather than maximizing over all `n ≤ N`, we
maximize over the filtered finset `{ n ≤ N | n ≡ r [MOD q] }`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API (residue-friendly).
-/
lemma exists_disc_eq_sup_filter_modEq (f : ℕ → ℤ) (d N q r : ℕ)
    (hne : ((Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q])).Nonempty) :
    ∃ n ≤ N, n ≡ r [MOD q] ∧
      disc f d n = ((Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q])).sup (fun t => disc f d t) := by
  classical
  rcases Finset.exists_mem_eq_sup
      (s := (Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q]))
      (f := fun t => disc f d t) hne with
    ⟨n, hnmem, hsup⟩
  have hnrange : n ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hnmem).1
  have hmod : n ≡ r [MOD q] := (Finset.mem_filter.1 hnmem).2
  refine ⟨n, Nat.le_of_lt_succ (Finset.mem_range.1 hnrange), hmod, ?_⟩
  exact hsup.symm

/-- In a fixed residue class modulo `q`, the maximum in `discOffsetUpTo` is attained by some
`n ≤ N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Max discrepancy up to N” API (residue-friendly).
-/
lemma exists_discOffset_eq_sup_filter_modEq (f : ℕ → ℤ) (d m N q r : ℕ)
    (hne : ((Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q])).Nonempty) :
    ∃ n ≤ N, n ≡ r [MOD q] ∧
      discOffset f d m n =
        ((Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q])).sup (fun t => discOffset f d m t) := by
  classical
  rcases Finset.exists_mem_eq_sup
      (s := (Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q]))
      (f := fun t => discOffset f d m t) hne with
    ⟨n, hnmem, hsup⟩
  have hnrange : n ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hnmem).1
  have hmod : n ≡ r [MOD q] := (Finset.mem_filter.1 hnmem).2
  refine ⟨n, Nat.le_of_lt_succ (Finset.mem_range.1 hnrange), hmod, ?_⟩
  exact hsup.symm

/-- Residue-class `UpTo` wrapper: the supremum of `discOffset f d m ·` over `{ n ≤ N | n ≡ r [MOD q] }`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Residue-class `UpTo` extraction wrapper”.
-/
def discOffsetUpTo_modEq (f : ℕ → ℤ) (d m N q r : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q])).sup (fun t => discOffset f d m t)

/-- In a fixed residue class modulo `q`, the maximum in `discOffsetUpTo_modEq` is attained by some `n ≤ N`.

This is a packaged, stable wrapper around `exists_discOffset_eq_sup_filter_modEq` that avoids having
clients mention the filtered-`sup` expression directly.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Residue-class `UpTo` extraction wrapper”.
-/
lemma exists_discOffset_eq_discOffsetUpTo_modEq (f : ℕ → ℤ) (d m N q r : ℕ)
    (hne : ((Finset.range (N + 1)).filter (fun n => n ≡ r [MOD q])).Nonempty) :
    ∃ n ≤ N, n ≡ r [MOD q] ∧ discOffset f d m n = discOffsetUpTo_modEq f d m N q r := by
  rcases exists_discOffset_eq_sup_filter_modEq (f := f) (d := d) (m := m) (N := N) (q := q) (r := r) hne with
    ⟨n, hnle, hmod, hEq⟩
  refine ⟨n, hnle, hmod, ?_⟩
  simpa [discOffsetUpTo_modEq] using hEq

/-- Definitional lemma exposing the definition. -/
lemma discOffset_eq_natAbs_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumOffset f d m n) :=
  rfl

/-- Support-form version of “restriction to a finite window”: restricting `f` to the relevant
`apSupport` (with default value `0` outside) does not change `discOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Restriction to finite window” API.
-/
lemma discOffset_restrict_support (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset (fun x => if x ∈ apSupport d m n then f x else 0) d m n = discOffset f d m n := by
  unfold discOffset
  simp [apSumOffset_restrict_support]

/-- Alias for the definitional lemma. -/
@[deprecated "Use `discOffset_eq_natAbs_apSumOffset`." (since := "2026-04-17")]
lemma discOffset_def (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumOffset f d m n) :=
  rfl

/-- Canonical discrepancy view of offsets: push the start shift `m*d` into the summand.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Canonical discrepancy view of offsets.
-/
lemma discOffset_eq_discrepancy_shift_mul (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = discrepancy (fun k => f (k + m * d)) d n := by
  unfold discOffset discrepancy
  -- Reduce to the corresponding statement for the underlying AP sums.
  simp [apSumOffset_eq_apSum_shift_mul]

/-- `simp` bridge: `Int.natAbs (apSumOffset …)` simplifies to the `discOffset` wrapper.

This direction avoids simp loops with `discOffset_def`.
-/
@[simp] lemma natAbs_apSumOffset_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) = discOffset f d m n :=
  rfl


/-!
### Degenerate-step (`d = 0`) normal forms (deprecated surface)

The simp-oriented `d = 0` normal-form lemmas used to live in this file, but they are now
considered *corner-case surface* and have been moved behind:

```lean
import MoltResearch.Discrepancy.Deprecated
```

This keeps the stable surface (`import MoltResearch.Discrepancy`) focused on the `d ≥ 1` workflow.
-/

/-!
### `discAlong`: along-`d` API coherence (`m = 0` offset form)

This is a lightweight specialization of `discOffset` that packages the “no offset” case.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Along-`d` API coherence (`discAlong`).
-/

/-- Discrepancy along step `d` with no offset: `discAlong f d n = discOffset f d 0 n`. -/
def discAlong (f : ℕ → ℤ) (d n : ℕ) : ℕ :=
  discOffset f d 0 n

/-- Definitional lemma exposing `discAlong`. -/
lemma discAlong_def (f : ℕ → ℤ) (d n : ℕ) : discAlong f d n = discOffset f d 0 n :=
  rfl

/-- Bridge lemma: `discAlong` agrees with the original homogeneous wrapper `discrepancy`. -/
lemma discAlong_eq_discrepancy (f : ℕ → ℤ) (d n : ℕ) : discAlong f d n = discrepancy f d n := by
  unfold discAlong discOffset discrepancy apSumOffset apSum
  simp

/-!
### Negation invariance

Checklist item: Problems/erdos_discrepancy.md (Track B) — Negation invariance (disc-level).

These lemmas let downstream code normalize sign-flips (`f ↦ -f`) with a one-line `simp`/`rw`.
-/

/-- Negation invariance for offset AP sums. -/
@[simp] lemma apSumOffset_neg (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => -f k) d m n = -apSumOffset f d m n := by
  unfold apSumOffset
  simp

/-- Linearity normal form for offset AP sums: push pointwise addition out of `apSumOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Linearity normal form (sum-level).
-/
lemma apSumOffset_add (f g : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f k + g k) d m n = apSumOffset f d m n + apSumOffset g d m n := by
  classical
  unfold apSumOffset
  simp [Finset.sum_add_distrib]

/-- Negation invariance for the offset discrepancy wrapper `discOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Negation invariance (disc-level).
-/
@[simp] lemma discOffset_neg (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset (fun k => -f k) d m n = discOffset f d m n := by
  unfold discOffset
  simp [apSumOffset_neg]

/-!
## Quantifier normal form: explicit bounds for `discOffset`

For many later statements, we want a *fixed bound* `B` that controls all lengths `n` for a given
triple `(f, d, m)`.  The definition below is intentionally `discOffset`-native so downstream
code can avoid unfolding `Int.natAbs (apSumOffset ...)`.
-/

/-- `BoundedDiscOffset f d m B` means: all offset discrepancies `discOffset f d m n` are
uniformly bounded by `B` (as `n` varies).

This is the “discOffset-native” boundedness predicate used in Track B normal forms.
-/
def BoundedDiscOffset (f : ℕ → ℤ) (d m B : ℕ) : Prop :=
  ∀ n : ℕ, discOffset f d m n ≤ B

/-- Stable lemma name: expose the quantifier normal form of `BoundedDiscOffset`.

Downstream code should prefer this lemma over unfolding the definition.
Checklist item: Problems/erdos_discrepancy.md (Track B) — Quantifier normal form (boundedness, discOffset-native).
-/
theorem boundedDiscOffset_iff_forall_discOffset_le (f : ℕ → ℤ) (d m B : ℕ) :
    BoundedDiscOffset f d m B ↔ ∀ n : ℕ, discOffset f d m n ≤ B :=
  Iff.rfl

/-- `BoundedDiscOffset f d m B` is equivalent to a uniform bound on the finitary maxima
`discOffsetUpTo f d m N`.

This is the main bridge lemma that lets downstream code turn a “∀ n” boundedness hypothesis into
an `UpTo` bound (and conversely) without unfolding definitions.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness ↔ `discOffsetUpTo` growth bound.
-/
theorem boundedDiscOffset_iff_forall_discOffsetUpTo_le (f : ℕ → ℤ) (d m B : ℕ) :
    BoundedDiscOffset f d m B ↔ ∀ N : ℕ, discOffsetUpTo f d m N ≤ B := by
  constructor
  · intro h N
    classical
    unfold discOffsetUpTo
    refine Finset.sup_le ?_
    intro n hn
    -- Every term in the `sup` is bounded by `B`.
    exact h n
  · intro h n
    -- Specialize the `UpTo` bound at `N = n` and use the pointwise ≤ max lemma.
    have hUpTo : discOffsetUpTo f d m n ≤ B := h n
    have hle : discOffset f d m n ≤ discOffsetUpTo f d m n :=
      discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := n) (N := n) (by rfl)
    exact le_trans hle hUpTo

/-!
### Exists-bound normal form

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness normal form (exists-bound).

These predicates package the common pattern “there exists a uniform bound” without requiring
call-sites to carry an explicit `B` parameter.
-/

/-- `BoundedDiscOffsetExists f d m` means: there exists a uniform bound on all `discOffset f d m n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness normal form (exists-bound, discOffset).
-/
def BoundedDiscOffsetExists (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ∃ B : ℕ, BoundedDiscOffset f d m B

/-- Stable lemma name: quantifier normal form for `BoundedDiscOffsetExists`. -/
theorem boundedDiscOffsetExists_iff_exists_forall_discOffset_le (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffsetExists f d m ↔ ∃ B : ℕ, ∀ n : ℕ, discOffset f d m n ≤ B := by
  rfl

/-- `BoundedDiscAlongExists f d` means: there exists a uniform bound on all `discAlong f d n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness normal form (exists-bound, discAlong).
-/
def BoundedDiscAlongExists (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discAlong f d n ≤ B

/-- Stable lemma name: quantifier normal form for `BoundedDiscAlongExists`. -/
theorem boundedDiscAlongExists_iff_exists_forall_discAlong_le (f : ℕ → ℤ) (d : ℕ) :
    BoundedDiscAlongExists f d ↔ ∃ B : ℕ, ∀ n : ℕ, discAlong f d n ≤ B :=
  Iff.rfl

/-!
### Unboundedness normal forms

Checklist item: Problems/erdos_discrepancy.md (Track B) — Unboundedness normal form (forall-exists).

These predicates package the “∀ B, ∃ n, …” normal form, primarily as the logical negation of the
corresponding boundedness-exists predicate when one exists.
-/

/-- `UnboundedDiscOffset f d m` means: there is no uniform bound on `discOffset f d m n`.

Defined as the negation of `BoundedDiscOffsetExists`, so the duality lemma below is the canonical
bridge to the `∀ B, ∃ n, …` witness form.
-/
def UnboundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ¬ BoundedDiscOffsetExists f d m

/-!
### Predicate-level sign-flip invariance

Checklist item: Problems/erdos_discrepancy.md (Track B) — Predicate-level sign-flip invariance.

These lemmas let downstream code normalize away sign-flips (`f ↦ -f`) at the level of the
boundedness/unboundedness predicates, without unfolding definitions.
-/

@[simp] theorem boundedDiscOffset_neg_iff (f : ℕ → ℤ) (d m B : ℕ) :
    BoundedDiscOffset (fun k => -f k) d m B ↔ BoundedDiscOffset f d m B := by
  constructor <;> intro h <;> intro n
  · simpa [BoundedDiscOffset] using (h n)
  · simpa [BoundedDiscOffset] using (h n)

@[simp] theorem boundedDiscOffsetExists_neg_iff (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffsetExists (fun k => -f k) d m ↔ BoundedDiscOffsetExists f d m := by
  constructor <;> rintro ⟨B, hB⟩
  · exact ⟨B, (boundedDiscOffset_neg_iff (f := f) (d := d) (m := m) (B := B)).1 hB⟩
  · exact ⟨B, (boundedDiscOffset_neg_iff (f := f) (d := d) (m := m) (B := B)).2 hB⟩

@[simp] theorem unboundedDiscOffset_neg_iff (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset (fun k => -f k) d m ↔ UnboundedDiscOffset f d m := by
  unfold UnboundedDiscOffset
  simpa using not_congr (boundedDiscOffsetExists_neg_iff (f := f) (d := d) (m := m))

/-- Canonical witness normal form for `UnboundedDiscOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Unboundedness normal form (forall-exists, discOffset).
-/
theorem unboundedDiscOffset_iff_forall_exists_discOffset_lt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔ ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n := by
  classical
  -- Expand the definitional sugar and push negations.
  -- `UnboundedDiscOffset` is defined as `¬ ∃ B, (∀ n, discOffset … n ≤ B)`.
  unfold UnboundedDiscOffset BoundedDiscOffsetExists BoundedDiscOffset
  constructor
  · intro h B
    by_contra h'
    have hB : ∀ n : ℕ, discOffset f d m n ≤ B := by
      intro n
      have : ¬ B < discOffset f d m n := by
        exact fun hn => h' ⟨n, hn⟩
      exact le_of_not_gt this
    exact h ⟨B, hB⟩
  · intro h hex
    rcases hex with ⟨B, hB⟩
    rcases h B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n) hn)

/-- Canonical witness normal form for `UnboundedDiscOffset` using the `discOffsetUpTo` max wrapper.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Unboundedness witness via `discOffsetUpTo`.
-/
theorem unboundedDiscOffset_iff_forall_exists_discOffsetUpTo_lt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔ ∀ B : ℕ, ∃ N : ℕ, B < discOffsetUpTo f d m N := by
  classical
  constructor
  · intro hunb B
    rcases (unboundedDiscOffset_iff_forall_exists_discOffset_lt (f := f) (d := d) (m := m)).1 hunb B with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- `discOffsetUpTo … n` dominates the particular value at `n`.
    exact lt_of_lt_of_le hn
      (discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := n) (N := n) (le_rfl))
  · intro h
    -- Reduce to the `discOffset` witness form using attainment of the `sup`.
    refine (unboundedDiscOffset_iff_forall_exists_discOffset_lt (f := f) (d := d) (m := m)).2 ?_
    intro B
    rcases h B with ⟨N, hN⟩
    rcases exists_discOffset_eq_discOffsetUpTo (f := f) (d := d) (m := m) (N := N) with
      ⟨n, hn, hnEq, -⟩
    refine ⟨n, ?_⟩
    simpa [hnEq] using hN

/-- Unboundedness normal form for homogeneous discrepancy `discrepancy f d n`. -/
def UnboundedDiscrepancy (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discrepancy f d n

/-- Unboundedness normal form for the along-`d` wrapper `discAlong f d n`. -/
def UnboundedDiscAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discAlong f d n

/-- Stable lemma name: negation-pushed quantifier normal form for *unboundedness* of `discOffset`.

This is the standard boundedness dual:
`¬ ∃ B, (∀ n, discOffset … ≤ B)` iff `∀ B, ∃ n, B < discOffset …`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Quantifier normal form (unboundedness, discOffset-native).
-/
theorem not_exists_boundedDiscOffset_iff_forall_exists_discOffset_lt (f : ℕ → ℤ) (d m : ℕ) :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔ ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n := by
  classical
  constructor
  · intro h B
    by_contra h'
    have hB : BoundedDiscOffset f d m B := by
      intro n
      have : ¬ B < discOffset f d m n := by
        -- `h' : ¬ ∃ n, B < discOffset … n`
        exact fun hn => h' ⟨n, hn⟩
      exact le_of_not_gt this
    exact h ⟨B, hB⟩
  · intro h hex
    rcases hex with ⟨B, hB⟩
    rcases h B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n) hn)

/-!
### `BoundedDiscOffset` API lemmas

These lemmas are intentionally lightweight: they let downstream code *move boundedness hypotheses*
around without unfolding `BoundedDiscOffset` or `discOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness API hygiene.
-/

/-- Monotonicity in the bound parameter `B`. -/
theorem BoundedDiscOffset.mono_B {f : ℕ → ℤ} {d m B B' : ℕ}
    (h : BoundedDiscOffset f d m B) (hBB' : B ≤ B') :
    BoundedDiscOffset f d m B' := by
  intro n
  exact le_trans (h n) hBB'

/-!
### `BoundedDiscrepancyAlong` (finite-length along-`d` boundedness)

This predicate is the finite-length “along `d`” analogue of `BoundedDiscOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness API hygiene.
-/

/-- `BoundedDiscrepancyAlong f d len B` means: for all `n ≤ len`, the along-`d` discrepancies
`discAlong f d n` are bounded by `B`.

This is intentionally formulated in terms of the stable wrapper `discAlong`.
-/
def BoundedDiscrepancyAlong (f : ℕ → ℤ) (d len B : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ len → discAlong f d n ≤ B

/-- Stable lemma name: expose the quantifier normal form of `BoundedDiscrepancyAlong`. -/
theorem boundedDiscrepancyAlong_iff_forall_le_discAlong_le (f : ℕ → ℤ) (d len B : ℕ) :
    BoundedDiscrepancyAlong f d len B ↔ ∀ n : ℕ, n ≤ len → discAlong f d n ≤ B :=
  Iff.rfl

/-- Bridge lemma: finite-length along-`d` boundedness is equivalent to a bound on the finitary
maximum `discOffsetUpTo f d 0 len`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
Bridge lemma: `BoundedDiscrepancyAlong` ↔ max-level bound.
-/
theorem boundedDiscrepancyAlong_iff_discOffsetUpTo_le (f : ℕ → ℤ) (d len B : ℕ) :
    BoundedDiscrepancyAlong f d len B ↔ discOffsetUpTo f d 0 len ≤ B := by
  constructor
  · intro h
    classical
    unfold discOffsetUpTo
    refine Finset.sup_le ?_
    intro n hn
    have hn' : n ≤ len := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    -- Rewrite `discAlong` to the nucleus wrapper `discOffset`.
    simpa [discAlong] using h n hn'
  · intro h
    intro n hn
    have hle : discOffset f d 0 n ≤ discOffsetUpTo f d 0 len :=
      discOffset_le_discOffsetUpTo (f := f) (d := d) (m := 0) (n := n) (N := len) hn
    have : discOffset f d 0 n ≤ B := le_trans hle h
    simpa [discAlong] using this

namespace BoundedDiscrepancyAlong

/-- Monotonicity in the bound parameter `B`. -/
theorem mono_B {f : ℕ → ℤ} {d len B B' : ℕ}
    (h : BoundedDiscrepancyAlong f d len B) (hBB' : B ≤ B') :
    BoundedDiscrepancyAlong f d len B' := by
  intro n hn
  exact le_trans (h n hn) hBB'

/-- Monotonicity in the length parameter `len` (shrinking the range keeps boundedness). -/
theorem mono_len {f : ℕ → ℤ} {d len len' B : ℕ}
    (h : BoundedDiscrepancyAlong f d len' B) (hlen : len ≤ len') :
    BoundedDiscrepancyAlong f d len B := by
  intro n hn
  exact h n (le_trans hn hlen)

end BoundedDiscrepancyAlong

/-! ### Congruence lemmas -/

/-- `disc` is stable under “local surgery”: if `f` and `g` agree on the indices actually
accessed by the underlying homogeneous progression sum, then the discrepancies coincide.

This is the `natAbs`/`ℕ`-valued analogue of `apSum_congr_support`.
-/
lemma disc_congr_support (f g : ℕ → ℤ) (d n : ℕ)
    (h : ∀ x ∈ apSupport d 0 n, f x = g x) :
    disc f d n = disc g d n := by
  unfold disc
  exact congrArg Int.natAbs
    (apSum_congr_support (f := f) (g := g) (d := d) (n := n) (h := h))

/-- `discOffset` is stable under “local surgery”: if `f` and `g` agree on the indices actually
accessed by the underlying offset progression sum, then the offset discrepancies coincide.

This is the `natAbs`/`ℕ`-valued analogue of `apSumOffset_congr_support`.
-/
lemma discOffset_congr_support (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ x ∈ apSupport d m n, f x = g x) :
    discOffset f d m n = discOffset g d m n := by
  -- Reduce to `apSumOffset_congr_support` and take `Int.natAbs` (avoid `simp` loops).
  unfold discOffset
  exact congrArg Int.natAbs
    (apSumOffset_congr_support (f := f) (g := g) (d := d) (m := m) (n := n) (h := h))

/-- If two functions agree pointwise on the indices used in `apSum`, then the AP sums are equal. -/
lemma apSum_congr (f g : ℕ → ℤ) (d n : ℕ)
    (h : ∀ i, i < n → f ((i + 1) * d) = g ((i + 1) * d)) :
    apSum f d n = apSum g d n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact h i hi'

/-- Pointwise congruence variant of `disc_congr_support`, expressed over `i < n`. -/
lemma disc_congr (f g : ℕ → ℤ) (d n : ℕ)
    (h : ∀ i, i < n → f ((i + 1) * d) = g ((i + 1) * d)) :
    disc f d n = disc g d n := by
  unfold disc
  exact congrArg Int.natAbs
    (apSum_congr (f := f) (g := g) (d := d) (n := n) (h := h))

/-- Range-form congruence lemma for `apSumOffset`.

If `f` and `g` agree on every summation index `i ∈ Finset.range n` in the `range`-expanded normal
form of `apSumOffset`, then `apSumOffset f d m n = apSumOffset g d m n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Range-form stability at AP-sum level.
-/
lemma apSumOffset_congr_range (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ∈ Finset.range n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact h i hi

/-- If two functions agree pointwise on the indices used in `apSumOffset`, then the offset sums are equal.

This is a pointwise-inequality wrapper around `apSumOffset_congr_range`.
-/
lemma apSumOffset_congr (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i < n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr_range (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact h i hi'

/-- Translation-invariance wrapper: if `f` and `g` agree pointwise on the progression indices
`(m+i)*d` for `i ≤ n`, then the offset AP sums of length `n` agree.

This packages the common hypothesis form `∀ i ≤ n, f ((m+i)*d) = g ((m+i)*d)` without requiring
manual `Finset.range` bookkeeping.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Translation invariance wrappers.
-/
lemma apSumOffset_congr_le (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ≤ n → f ((m + i) * d) = g ((m + i) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
  -- rewrite `(m+i+1)` as `m+(i+1)` to match the hypothesis.
  simpa [Nat.add_assoc] using (h (i + 1) hle)

/-- Support statement: if `f` and `g` agree on every *progression index* used by `apSumOffset`
(i.e. on `Set.Icc (m+1) (m+n)`), then the offset sums are equal.

This is convenient as “glue” for later local-surgery arguments where you know that `f` and `g`
coincide on a bounded interval, and you want to change `f` outside that interval.
-/
lemma apSumOffset_congr_Icc (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ∈ Set.Icc (m + 1) (m + n) → f (i * d) = g (i * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have hlow : m + 1 ≤ m + i + 1 := by
    have : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
    have : m + 1 ≤ m + (i + 1) := Nat.add_le_add_left this m
    simpa [Nat.add_assoc] using this
  have hhigh : m + i + 1 ≤ m + n := by
    have : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have : m + (i + 1) ≤ m + n := Nat.add_le_add_left this m
    simpa [Nat.add_assoc] using this
  exact h (m + i + 1) ⟨hlow, hhigh⟩

/-- Endpoint-form congruence wrapper for `apSumOffset`.

This packages a very common hypothesis shape in discrepancy arguments:

`∀ i, m < i ∧ i ≤ m+n → f (i*d) = g (i*d)`

into the normal-form congruence statement
`apSumOffset f d m n = apSumOffset g d m n`,
without mentioning `Finset.range` or `Set.Icc` in the statement.

Checklist item: Problems/erdos_discrepancy.md (Track B) — AP-sum congruence on `Icc` endpoints.
-/
lemma apSumOffset_congr_endpoints (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, (m < i ∧ i ≤ m + n) → f (i * d) = g (i * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr_Icc (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have hlow : m < i := by
    -- `m < m+1 ≤ i`.
    have hm : m < m + 1 := Nat.lt_succ_self m
    exact lt_of_lt_of_le hm hi.1
  exact h i ⟨hlow, hi.2⟩

/-- Finset-membership variant of `apSumOffset_congr_Icc`.

This matches paper notation where the relevant progression indices are written as
`Finset.Icc (m+1) (m+n)`.
-/
lemma apSumOffset_congr_finset_Icc (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ∈ Finset.Icc (m + 1) (m + n) → f (i * d) = g (i * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr_Icc (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have : i ∈ Finset.Icc (m + 1) (m + n) := by
    exact Finset.mem_Icc.2 hi
  exact h i this

/-- Endpoint-form congruence wrapper for `discOffset` (paper notation).

This packages a very common hypothesis shape in discrepancy arguments:

`∀ i, m < i ∧ i ≤ m+n → f (i*d) = g (i*d)`

into the normal-form congruence statement
`discOffset f d m n = discOffset g d m n`,
without mentioning `Finset.range` or `Set.Icc` in the statement.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Endpoint-congruence wrapper (disc-level, paper notation).
-/
lemma discOffset_congr_endpoints (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, (m < i ∧ i ≤ m + n) → f (i * d) = g (i * d)) :
    discOffset f d m n = discOffset g d m n := by
  unfold discOffset
  refine congrArg Int.natAbs ?_
  exact apSumOffset_congr_endpoints (f := f) (g := g) (d := d) (m := m) (n := n) (h := h)

/-!
### Endpoint-normalization lemmas (Track B)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Endpoint-normalization for `discOffset` witnesses.

These lemmas package the small Nat arithmetic conversions that routinely arise when moving between
endpoint-style hypotheses (paper notation) and finitary `Finset.Icc` membership hypotheses.

We keep them **simp-friendly** (usable via `simp`/`simpa`) but avoid adding aggressive global
`[simp]` attributes to prevent loops.
-/

/-- Endpoint-normalization lemma: endpoint-style constraints are `Finset.Icc` membership.

Concretely,
`m < i ∧ i ≤ m+n` is equivalent to `i ∈ Finset.Icc (m+1) (m+n)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Endpoint-normalization for `discOffset` witnesses.
-/
lemma endpoints_lt_le_iff_mem_finset_Icc (m n i : ℕ) :
    (m < i ∧ i ≤ m + n) ↔ i ∈ Finset.Icc (m + 1) (m + n) := by
  constructor
  · intro h
    exact Finset.mem_Icc.2 ⟨(Nat.succ_le_iff).2 h.1, h.2⟩
  · intro h
    have h' : m + 1 ≤ i ∧ i ≤ m + n := (Finset.mem_Icc).1 h
    exact ⟨(Nat.succ_le_iff).1 h'.1, h'.2⟩

/-- Endpoint-normalization lemma: endpoint constraints in `≤` form can be written in `lt` form.

Concretely,
`m < i ∧ i ≤ m+n` is equivalent to `m+1 ≤ i ∧ i < m+n+1`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Endpoint-normalization for `discOffset` witnesses.
-/
lemma endpoints_lt_le_iff_succ_le_lt_succ (m n i : ℕ) :
    (m < i ∧ i ≤ m + n) ↔ (m + 1 ≤ i ∧ i < m + n + 1) := by
  constructor
  · intro h
    refine ⟨(Nat.succ_le_iff).2 h.1, ?_⟩
    -- `i ≤ m+n` iff `i < m+n+1`.
    exact (Nat.lt_succ_iff).2 (by simpa [Nat.add_assoc] using h.2)
  · intro h
    refine ⟨(Nat.succ_le_iff).1 h.1, ?_⟩
    -- `i < m+n+1` iff `i ≤ m+n`.
    exact (Nat.lt_succ_iff).1 (by simpa [Nat.add_assoc] using h.2)

/-!
### Endpoint-normalization: small arithmetic simp helpers (Track B)

These are intentionally tiny rewrite lemmas that steer `simp` towards the exact endpoint shapes
that the stable witness APIs use (`m+1`, `m+n`, etc.).

We only orient them towards a **right-associated** normal form to avoid simp loops.
-/

lemma add_assoc_right (m n k : ℕ) : m + (n + k) = m + n + k := by
  simpa [Nat.add_assoc]

lemma add_assoc_right' (m n k : ℕ) : (m + n) + k = m + n + k := by
  rfl

/-- Normalize the common upper-endpoint algebra `m+1+(n-1)` into `m+n` (for `n>0`). -/
lemma add_one_add_pred_eq_add (m n : ℕ) (hn : 0 < n) : m + 1 + (n - 1) = m + n := by
  cases n with
  | zero => cases hn
  | succ n =>
      -- `Nat.succ` case: `n+1-1 = n`.
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Variant of `add_one_add_pred_eq_add` with the trailing `+1` on the right. -/
lemma add_pred_add_one_eq_add (m n : ℕ) (hn : 0 < n) : m + (n - 1) + 1 = m + n := by
  cases n with
  | zero => cases hn
  | succ n =>
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Range-form congruence lemma for `discOffset`.

If `f` and `g` agree on every summation index `i ∈ Finset.range n` in the `range`-expanded normal
form of `apSumOffset`, then `discOffset f d m n = discOffset g d m n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Range-form stability at discrepancy level.
-/
lemma discOffset_congr_range (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ∈ Finset.range n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    discOffset f d m n = discOffset g d m n := by
  unfold discOffset
  refine congrArg Int.natAbs ?_
  exact apSumOffset_congr_range (f := f) (g := g) (d := d) (m := m) (n := n) h

/-- Pointwise congruence variant of `discOffset_congr_support`, expressed over `i < n`.

This is the `discOffset` analogue of `apSumOffset_congr`.

This is a pointwise-inequality wrapper around `discOffset_congr_range`.
-/
lemma discOffset_congr (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i < n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    discOffset f d m n = discOffset g d m n := by
  apply discOffset_congr_range (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact h i hi'

/-- Translation-invariance wrapper for `discOffset`.

If `f` and `g` agree on the affine tail indices `(m+i)*d` for `i ≤ n`, then the corresponding
offset discrepancies of length `n` agree.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Translation invariance wrappers.
-/
lemma discOffset_congr_le (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ≤ n → f ((m + i) * d) = g ((m + i) * d)) :
    discOffset f d m n = discOffset g d m n := by
  unfold discOffset
  refine congrArg Int.natAbs ?_
  exact apSumOffset_congr_le (f := f) (g := g) (d := d) (m := m) (n := n) h

/-!
### Congruence wrappers for `discOffsetUpTo`

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Max-level congruence wrapper: `discOffsetUpTo_congr` / `discOffsetUpTo_congr_le`”.

These mirror the existing `discOffset_congr` / `discOffset_congr_le` wrappers, but lift them
through the outer `Finset.sup` so callers don’t have to manually manage `n ∈ range (N+1)`.
-/

/-- Pointwise congruence wrapper for `discOffsetUpTo`, expressed over `i < N + 1`.

If `f` and `g` agree on every tail index that can appear in any length `n ≤ N`, then the
corresponding max-offset discrepancies up to `N` agree.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Max-level congruence wrappers.
-/
lemma discOffsetUpTo_congr (f g : ℕ → ℤ) (d m N : ℕ)
    (h : ∀ i, i < N + 1 → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    discOffsetUpTo f d m N = discOffsetUpTo g d m N := by
  classical
  unfold discOffsetUpTo
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.1 hn
    have hfg : discOffset f d m n = discOffset g d m n := by
      apply discOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
      intro i hi
      exact h i (lt_trans hi hnlt)
    -- transport the pointwise equality into the `sup` bound
    simpa [hfg] using
      (Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => discOffset g d m t) hn)
  · refine Finset.sup_le ?_
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.1 hn
    have hgf : discOffset g d m n = discOffset f d m n := by
      apply discOffset_congr (f := g) (g := f) (d := d) (m := m) (n := n)
      intro i hi
      simpa using (h i (lt_trans hi hnlt)).symm
    simpa [hgf] using
      (Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => discOffset f d m t) hn)

/-- Translation-invariance wrapper for `discOffsetUpTo`.

If `f` and `g` agree on the affine tail indices `(m+i)*d` for `i ≤ N+1`, then the corresponding
max-offset discrepancies up to `N` agree.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Max-level congruence wrappers.
-/
lemma discOffsetUpTo_congr_le (f g : ℕ → ℤ) (d m N : ℕ)
    (h : ∀ i, i ≤ N + 1 → f ((m + i) * d) = g ((m + i) * d)) :
    discOffsetUpTo f d m N = discOffsetUpTo g d m N := by
  classical
  unfold discOffsetUpTo
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.1 hn
    have hfg : discOffset f d m n = discOffset g d m n := by
      apply discOffset_congr_le (f := f) (g := g) (d := d) (m := m) (n := n)
      intro i hi
      -- `i ≤ n` and `n < N+1` gives `i ≤ N+1`.
      have hin : i ≤ N := le_trans hi (Nat.le_of_lt_succ hnlt)
      have hiN1 : i ≤ N + 1 := le_trans hin (Nat.le_succ N)
      exact h i hiN1
    simpa [hfg] using
      (Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => discOffset g d m t) hn)
  · refine Finset.sup_le ?_
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.1 hn
    have hgf : discOffset g d m n = discOffset f d m n := by
      apply discOffset_congr_le (f := g) (g := f) (d := d) (m := m) (n := n)
      intro i hi
      have hin : i ≤ N := le_trans hi (Nat.le_of_lt_succ hnlt)
      have hiN1 : i ≤ N + 1 := le_trans hin (Nat.le_succ N)
      have : f ((m + i) * d) = g ((m + i) * d) := h i hiN1
      simpa using this.symm
    simpa [hgf] using
      (Finset.le_sup (s := Finset.range (N + 1)) (f := fun t => discOffset f d m t) hn)

/-!
Deprecated `discOffset` congruence variants over explicit `Icc` index sets have been moved behind
`import MoltResearch.Discrepancy.Deprecated`.

Preferred stable-surface congruence lemma: `discOffset_congr_range`.
-/

/-- `congr` variant: if `P` holds on every *index* used in `apSumOffset`, and the summands agree
whenever `P i` holds, then the offset AP sums are equal.

This is convenient when you have a hypothesis stated on the summation range `i < n` (or
`i ∈ range n`) and want to apply it without rewriting the whole function.
-/
lemma apSumOffset_congrOn (f g : ℕ → ℤ) (P : ℕ → Prop) (d m n : ℕ)
    (hP : ∀ i, i < n → P i)
    (hfg : ∀ i, P i → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  exact hfg i (hP i hi)

/-- Value-predicate variant of `apSumOffset_congrOn`: if `P` holds on every value used in
`apSumOffset`, and `f = g` on `P`, then the offset AP sums are equal.

This is convenient when you have an ambient hypothesis like `∀ x, P x → f x = g x`.
-/
lemma apSumOffset_congrOn_val (f g : ℕ → ℤ) (P : ℕ → Prop) (d m n : ℕ)
    (hP : ∀ i, i < n → P ((m + i + 1) * d))
    (hfg : ∀ x, P x → f x = g x) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  exact hfg _ (hP i hi)

/-! ### Invariance / normal-form lemmas -/

/-- Shifting the input by `a*d` converts an `apSum` into an `apSumOffset`.

This is the natural “invariance normal form” for arithmetic progressions: the *sequence* shift
by `a*d` corresponds to an *offset* `a` in the progression index.
-/
lemma apSum_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    apSum (fun k => f (k + a * d)) d n = apSumOffset f d a n := by
  unfold apSum apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `((i+1)*d) + a*d = (a+i+1)*d`.
  have h : (i + 1) * d + a * d = (a + i + 1) * d := by
    calc
      (i + 1) * d + a * d = a * d + (i + 1) * d := by
        simpa [Nat.add_comm]
      _ = (a + (i + 1)) * d := by
        simpa [Nat.add_mul]
      _ = (a + i + 1) * d := by
        simp [Nat.add_assoc]
  simp [h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- One-way normal form for discrepancy of a shift by `a*d`: it expands to the `natAbs` of an
offset AP sum.

Marked `[simp]` since the rewrite goes from the wrapper `discrepancy` to a `natAbs` normal form.
-/
@[simp] lemma discrepancy_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    discrepancy (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n) := by
  unfold discrepancy
  simpa [apSum_shift_mul]

/-- `simp`-friendly variant of `apSum_shift_mul` under `Int.natAbs`.

This lets goals normalize after rewriting `discrepancy_def` without having to manually unfold
`apSum_shift_mul`.
-/
@[simp] lemma natAbs_apSum_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    Int.natAbs (apSum (fun k => f (k + a * d)) d n) = Int.natAbs (apSumOffset f d a n) := by
  simpa [apSum_shift_mul]

/-- Normal form: shifting by `m*d` becomes `apSumOffset`. (Not a `[simp]` lemma: it can loop.) -/
lemma apSum_shift_mul_simp (f : ℕ → ℤ) (m d n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  simpa using (apSum_shift_mul (f := f) (a := m) (d := d) (n := n))

/-- Normal form: discrepancy of a shift by `m*d` becomes `natAbs (apSumOffset ...)`. (Not `[simp]`.) -/
lemma discrepancy_shift_mul_simp (f : ℕ → ℤ) (m d n : ℕ) :
    discrepancy (fun k => f (k + m * d)) d n = Int.natAbs (apSumOffset f d m n) := by
  simpa using (discrepancy_shift_mul (f := f) (a := m) (d := d) (n := n))

/-!
### `disc` API coherence: shift normal forms

These are homogeneous `disc`-level counterparts of the existing `discrepancy_*` shift lemmas.
They exist purely for naming/coherence with the `discOffset_*` API.
-/

/-- One-way normal form for `disc` of a shift by `a*d`: it expands to the `natAbs` of an
offset AP sum.

Marked `[simp]` since the rewrite goes from the wrapper `disc` to a `natAbs` normal form.
-/
@[simp] lemma disc_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    disc (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n) := by
  unfold disc
  simpa using (natAbs_apSum_shift_mul (f := f) (a := a) (d := d) (n := n))

/-- Normal form: `disc` of a shift by `m*d` becomes `natAbs (apSumOffset ...)`. (Not `[simp]`.) -/
lemma disc_shift_mul_simp (f : ℕ → ℤ) (m d n : ℕ) :
    disc (fun k => f (k + m * d)) d n = Int.natAbs (apSumOffset f d m n) := by
  simpa using (disc_shift_mul (f := f) (a := m) (d := d) (n := n))

/-- The corresponding `disc` normal form when `a = m*d`. -/
lemma disc_shift_of_eq_mul (f : ℕ → ℤ) (a d n m : ℕ) (ha : a = m * d) :
    disc (fun k => f (k + a)) d n = Int.natAbs (apSumOffset f d m n) := by
  subst ha
  simpa using (disc_shift_mul (f := f) (a := m) (d := d) (n := n))

/-! ### Shifting the “start index” in `apSumOffset` -/

/-- Normal form: shifting the skipped prefix `m` by `k` can be moved into the summand as a shift
by `k*d`.

Concretely, this rewrites
`apSumOffset f d (m + k) n`
into
`apSumOffset (fun t => f (t + k*d)) d m n`.
-/
lemma apSumOffset_add_start (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k * d)) d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Align the indices so we can use distributivity of `(* d)` over `+`.
  have hmk : m + k + i + 1 = (m + i + 1) + k := by
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hmul : (m + k + i + 1) * d = (m + i + 1) * d + k * d := by
    calc
      (m + k + i + 1) * d = ((m + i + 1) + k) * d := by
        simpa [hmk]
      _ = (m + i + 1) * d + k * d := by
        simpa [Nat.add_mul]
  -- Now the summands match definitionally.
  simp [hmul]

/-- Translation-friendly variant of `apSumOffset_add_start` with the constant shift on the left:
`k*d + t`.
-/
lemma apSumOffset_add_start_add_left (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (k * d + t)) d m n := by
  -- Just commute the addition inside the shifted summand.
  simpa [Nat.add_comm] using (apSumOffset_add_start (f := f) (d := d) (m := m) (k := k) (n := n))

/-! ### Normalization of nested shifts inside summands -/

/-- `simp` normal form for nested additive shifts under binders.

This is intentionally *function-level* (rather than a `[simp]` lemma about `Nat.add_assoc`) so it
only fires when a goal actually contains a shifted summand `fun k => f (k + a + b)`.

We orient the rewrite as
`fun k => f (k + a + b)` → `fun k => f (k + (a + b))`
to avoid simp loops.
-/
@[simp] lemma shift_summand_add_assoc {α : Type} (f : ℕ → α) (a b : ℕ) :
    (fun k => f (k + a + b)) = fun k => f (k + (a + b)) := by
  funext k
  simp [Nat.add_assoc]

/-! ### Shifts by a known multiple of `d` -/

/-- If `a` is (definitionally) a multiple of `d`, shifting by `a` is the same normal form
as shifting by `m*d` and rewriting via `apSumOffset`. -/
lemma apSum_shift_of_eq_mul (f : ℕ → ℤ) (a d n m : ℕ) (ha : a = m * d) :
    apSum (fun k => f (k + a)) d n = apSumOffset f d m n := by
  subst ha
  simpa using (apSum_shift_mul (f := f) (a := m) (d := d) (n := n))

/-- The corresponding `discrepancy` normal form when `a = m*d`. -/
lemma discrepancy_shift_of_eq_mul (f : ℕ → ℤ) (a d n m : ℕ) (ha : a = m * d) :
    discrepancy (fun k => f (k + a)) d n = Int.natAbs (apSumOffset f d m n) := by
  subst ha
  simpa using (discrepancy_shift_mul (f := f) (a := m) (d := d) (n := n))

/-! ### Normalizing shifts modulo the step -/

/-- Normal form: shifting by `a` can be reduced modulo the step `d`.

Concretely, for `d > 0` we rewrite the summand shift `k ↦ f (k + a)` as
`k ↦ f (k + (a % d))` while adjusting the AP start index by `a / d`.

This is aligned with the standard decomposition `a = (a / d) * d + (a % d)`.
-/
lemma apSumOffset_shift_mod (f : ℕ → ℤ) (d m n a : ℕ) (hd : 0 < d) :
    apSumOffset (fun k => f (k + a)) d m n =
      apSumOffset (fun k => f (k + (a % d))) d (m + a / d) n := by
  -- (We keep the hypothesis `d > 0` since this lemma is used as a normalization rule.)
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  have ha : a = (a / d) * d + a % d := by
    -- `Nat.div_add_mod` is stated with `d * (a / d)`; commute the factors.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod a d).symm
  have hadd : (m + i + 1) + a / d = m + a / d + i + 1 := by
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hmul : (m + i + 1) * d + (a / d) * d = ((m + i + 1) + a / d) * d := by
    simpa [Nat.add_mul] using (Nat.add_mul (m + i + 1) (a / d) d).symm
  have hidx : ((m + i + 1) * d) + a = ((m + a / d + i + 1) * d) + a % d := by
    calc
      ((m + i + 1) * d) + a
          = ((m + i + 1) * d) + ((a / d) * d + a % d) := by
              nth_rewrite 1 [ha]
              rfl
      _ = ((m + i + 1) * d + (a / d) * d) + a % d := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = (((m + i + 1) + a / d) * d) + a % d := by
              -- `x*d + y*d = (x+y)*d`
              rw [hmul]
      _ = ((m + a / d + i + 1) * d) + a % d := by
              simp [hadd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  exact congrArg f hidx

/-!
### Predicate-level translation invariance (Track B)

These lemmas lift the sum-level normalization lemma `apSumOffset_shift_mod` to the
boundedness/unboundedness predicates.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Predicate-level translation invariance.
-/

/-- `discOffset` is invariant under the shift-modulo rewrite of `apSumOffset_shift_mod`. -/
theorem discOffset_shift_mod (f : ℕ → ℤ) (d m n a : ℕ) (hd : 0 < d) :
    discOffset (fun k => f (k + a)) d m n =
      discOffset (fun k => f (k + (a % d))) d (m + a / d) n := by
  unfold discOffset
  simp [apSumOffset_shift_mod (f := f) (d := d) (m := m) (n := n) (a := a) hd]

/-- Predicate-level wrapper for `apSumOffset_shift_mod` (boundedness, discOffset-native). -/
theorem boundedDiscOffset_shift_mod_iff (f : ℕ → ℤ) (d m B a : ℕ) (hd : 0 < d) :
    BoundedDiscOffset (fun k => f (k + a)) d m B ↔
      BoundedDiscOffset (fun k => f (k + (a % d))) d (m + a / d) B := by
  constructor <;> intro h <;> intro n
  · simpa [BoundedDiscOffset, discOffset_shift_mod (f := f) (d := d) (m := m) (n := n) (a := a) hd] using
      h n
  · simpa [BoundedDiscOffset, discOffset_shift_mod (f := f) (d := d) (m := m) (n := n) (a := a) hd] using
      h n

/-- Predicate-level wrapper for `apSumOffset_shift_mod` (existence of a uniform bound). -/
theorem boundedDiscOffsetExists_shift_mod_iff (f : ℕ → ℤ) (d m a : ℕ) (hd : 0 < d) :
    BoundedDiscOffsetExists (fun k => f (k + a)) d m ↔
      BoundedDiscOffsetExists (fun k => f (k + (a % d))) d (m + a / d) := by
  constructor <;> rintro ⟨B, hB⟩
  · exact ⟨B, (boundedDiscOffset_shift_mod_iff (f := f) (d := d) (m := m) (B := B) (a := a) hd).1 hB⟩
  · exact ⟨B, (boundedDiscOffset_shift_mod_iff (f := f) (d := d) (m := m) (B := B) (a := a) hd).2 hB⟩

/-- Predicate-level wrapper for `apSumOffset_shift_mod` (unboundedness). -/
theorem unboundedDiscOffset_shift_mod_iff (f : ℕ → ℤ) (d m a : ℕ) (hd : 0 < d) :
    UnboundedDiscOffset (fun k => f (k + a)) d m ↔
      UnboundedDiscOffset (fun k => f (k + (a % d))) d (m + a / d) := by
  -- `UnboundedDiscOffset` is defined as the negation of `BoundedDiscOffsetExists`.
  simpa [UnboundedDiscOffset] using
    (not_congr (boundedDiscOffsetExists_shift_mod_iff (f := f) (d := d) (m := m) (a := a) hd))

/-!
### Special case: shifts by multiples of `d`

When `d ∣ a`, the modulo term `a % d` vanishes and the summand shift normalizes to `f`.
-/

/-- If `d ∣ a`, then shifting the summand by `a` only adjusts the start parameter (`m + a/d`). -/
@[simp] theorem boundedDiscOffset_shift_of_dvd_iff (f : ℕ → ℤ) (d m B a : ℕ) (hd : 0 < d)
    (ha : d ∣ a) :
    BoundedDiscOffset (fun k => f (k + a)) d m B ↔ BoundedDiscOffset f d (m + a / d) B := by
  -- Reduce via the shift-modulo normalization and simplify `a % d = 0`.
  simpa [Nat.mod_eq_zero_of_dvd ha] using
    (boundedDiscOffset_shift_mod_iff (f := f) (d := d) (m := m) (B := B) (a := a) hd)

/-- Exists-bound version of `boundedDiscOffset_shift_of_dvd_iff`. -/
@[simp] theorem boundedDiscOffsetExists_shift_of_dvd_iff (f : ℕ → ℤ) (d m a : ℕ) (hd : 0 < d)
    (ha : d ∣ a) :
    BoundedDiscOffsetExists (fun k => f (k + a)) d m ↔ BoundedDiscOffsetExists f d (m + a / d) := by
  simpa [Nat.mod_eq_zero_of_dvd ha] using
    (boundedDiscOffsetExists_shift_mod_iff (f := f) (d := d) (m := m) (a := a) hd)

/-- Unboundedness version of `boundedDiscOffset_shift_of_dvd_iff`. -/
@[simp] theorem unboundedDiscOffset_shift_of_dvd_iff (f : ℕ → ℤ) (d m a : ℕ) (hd : 0 < d)
    (ha : d ∣ a) :
    UnboundedDiscOffset (fun k => f (k + a)) d m ↔ UnboundedDiscOffset f d (m + a / d) := by
  simpa [Nat.mod_eq_zero_of_dvd ha] using
    (unboundedDiscOffset_shift_mod_iff (f := f) (d := d) (m := m) (a := a) hd)

/-! ### Triangle-inequality API for AP sums -/

/-- `apSumOffset` splits over addition of lengths. -/
lemma apSumOffset_add_len (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  unfold apSumOffset
  -- `range (n₁ + n₂)` splits into `range n₁` and a shifted `range n₂`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (f := fun i => f ((m + i + 1) * d)) n₁ n₂)

/-! ### Tails / differences for `apSumOffset` -/

/-- Tail of an offset AP sum as a difference of a longer sum and its initial segment.

This is a convenient normal form for “difference → later tail” pipelines.
-/
lemma apSumOffset_tail_eq_sub (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d (m + n₁) n₂ = apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ := by
  -- Start from the length-splitting lemma and rearrange.
  have h := apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
  -- `h : apSumOffset … (n₁+n₂) = apSumOffset … n₁ + apSumOffset … (m+n₁) n₂`.
  -- Subtract the prefix.
  have hsub := congrArg (fun z : ℤ => z - apSumOffset f d m n₁) h
  -- Clean up `(+ …) - …`.
  simpa [add_sub_cancel_left, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsub.symm

/-- Rewrite the normal-form difference
`apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁` as the tail `apSumOffset f d (m+n₁) n₂`.

This is the offset-sum analogue of `apSum_sub_eq_apSumOffset` / `apSumFrom_sub_eq_apSumFrom_tail`.
-/
lemma apSumOffset_sub_eq_apSumOffset_tail (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using (apSumOffset_tail_eq_sub (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)).symm

/-- `simp`-friendly corollary of `apSumOffset_add_len` for `n₁ = 0`. -/
@[simp] lemma apSumOffset_add_len_zero_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (0 + n) = apSumOffset f d m n := by
  simpa [apSumOffset_add_len] using
    (apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSumOffset_add_len` for `n₂ = 0`. -/
@[simp] lemma apSumOffset_add_len_zero_right (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 0) = apSumOffset f d m n := by
  simpa [apSumOffset_add_len] using
    (apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n) (n₂ := 0))

/-- Triangle inequality for concatenating two offset AP sums. -/
lemma natAbs_apSumOffset_add_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    Int.natAbs (apSumOffset f d m (n₁ + n₂)) ≤
      Int.natAbs (apSumOffset f d m n₁) + Int.natAbs (apSumOffset f d (m + n₁) n₂) := by
  -- `Int.natAbs` satisfies `|x + y| ≤ |x| + |y|`.
  simpa [apSumOffset_add_len] using
    (Int.natAbs_add_le (apSumOffset f d m n₁) (apSumOffset f d (m + n₁) n₂))

/-- Triangle inequality for concatenating two offset AP sums, at the `discOffset` level.

This proof stays at the discrepancy-normal-form level: we apply the `Int.natAbs` lemma and
rewrite using the simp bridge `natAbs_apSumOffset_eq_discOffset`, rather than unfolding
`discOffset`.
-/
lemma discOffset_add_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d m (n₁ + n₂) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  simpa using
    (natAbs_apSumOffset_add_le (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Reverse triangle inequality (prefix form) for offset AP sums.

If `S(n₁ + n₂) = S(n₁) + S'(n₂)` then `|S(n₁)| ≤ |S(n₁ + n₂)| + |S'(n₂)|`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` reverse triangle bounds.
-/
lemma natAbs_apSumOffset_left_le_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    Int.natAbs (apSumOffset f d m n₁) ≤
      Int.natAbs (apSumOffset f d m (n₁ + n₂)) + Int.natAbs (apSumOffset f d (m + n₁) n₂) := by
  -- `|x| = |(x+y) - y| ≤ |x+y| + |y|`.
  simpa [apSumOffset_add_len, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Int.natAbs_sub_le (apSumOffset f d m (n₁ + n₂)) (apSumOffset f d (m + n₁) n₂))

/-- Reverse triangle inequality (suffix form) for offset AP sums.

If `S(n₁ + n₂) = S(n₁) + S'(n₂)` then `|S'(n₂)| ≤ |S(n₁ + n₂)| + |S(n₁)|`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` reverse triangle bounds.
-/
lemma natAbs_apSumOffset_right_le_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    Int.natAbs (apSumOffset f d (m + n₁) n₂) ≤
      Int.natAbs (apSumOffset f d m (n₁ + n₂)) + Int.natAbs (apSumOffset f d m n₁) := by
  -- `|y| = |(x+y) - x| ≤ |x+y| + |x|`.
  simpa [apSumOffset_add_len, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Int.natAbs_sub_le (apSumOffset f d m (n₁ + n₂)) (apSumOffset f d m n₁))

/-- Reverse triangle inequality for `discOffset` (prefix form).

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` reverse triangle bounds.
-/
lemma discOffset_left_le_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d m n₁ ≤ discOffset f d m (n₁ + n₂) + discOffset f d (m + n₁) n₂ := by
  simpa using
    (natAbs_apSumOffset_left_le_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Reverse triangle inequality for `discOffset` (suffix form).

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` reverse triangle bounds.
-/
lemma discOffset_right_le_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d (m + n₁) n₂ ≤ discOffset f d m (n₁ + n₂) + discOffset f d m n₁ := by
  simpa using
    (natAbs_apSumOffset_right_le_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Two-cut normal form bound (discOffset-level): concatenate three segments.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Two-cut normal form (discOffset-level).
-/
lemma discOffset_add_add_le (f : ℕ → ℤ) (d m n₁ n₂ n₃ : ℕ) :
    discOffset f d m (n₁ + n₂ + n₃) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ + discOffset f d (m + n₁ + n₂) n₃ := by
  -- Apply the 2-segment triangle inequality twice.
  have h₁ : discOffset f d m (n₁ + n₂) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ :=
    discOffset_add_le (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
  have h₂ : discOffset f d m ((n₁ + n₂) + n₃) ≤
      discOffset f d m (n₁ + n₂) + discOffset f d (m + (n₁ + n₂)) n₃ :=
    discOffset_add_le (f := f) (d := d) (m := m) (n₁ := (n₁ + n₂)) (n₂ := n₃)
  -- Add `discOffset … n₃` to the inequality for the prefix.
  have h₃ :
      discOffset f d m (n₁ + n₂) + discOffset f d (m + (n₁ + n₂)) n₃ ≤
        (discOffset f d m n₁ + discOffset f d (m + n₁) n₂) + discOffset f d (m + (n₁ + n₂)) n₃ := by
    exact Nat.add_le_add_right h₁ _
  -- Chain and normalize associativity.
  have h := le_trans h₂ h₃
  -- Put both sides in the advertised normal form.
  simpa [Nat.add_assoc] using h

/-- Endpoint-algebra wrapper for `discOffset_add_add_le`.

This variant uses the right-associated length `n₁ + (n₂ + n₃)` and the right-associated
third-segment start index `m + (n₁ + n₂)`, so downstream proofs can `simpa` without manual
`Nat.add_assoc` bookkeeping.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Endpoint algebra helpers.
-/
lemma discOffset_add_add_le_assoc (f : ℕ → ℤ) (d m n₁ n₂ n₃ : ℕ) :
    discOffset f d m (n₁ + (n₂ + n₃)) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ + discOffset f d (m + (n₁ + n₂)) n₃ := by
  -- Reassociate to match `discOffset_add_add_le`, then reassociate the conclusion back.
  simpa [Nat.add_assoc] using (discOffset_add_add_le (f := f) (d := d) (m := m)
    (n₁ := n₁) (n₂ := n₂) (n₃ := n₃))

/-! ### Degenerate start simp lemmas

These mirror the “degenerate length” simp lemmas (`apSumOffset_zero` / `apSumOffset_one`) but for the
*start index* parameter.
-/

/-- Normal form: an offset sum with start index `m = 0` is just the homogeneous sum `apSum`.

Marked `[simp]` so that normalizing away a spurious `m = 0` offset is automatic.
(We intentionally do *not* simp in the other direction.)
-/
@[simp] lemma apSumOffset_zero_start (f : ℕ → ℤ) (d n : ℕ) :
    apSumOffset f d 0 n = apSum f d n := by
  unfold apSumOffset apSum
  simp

/-- Normal form: a `discOffset` with start index `m = 0` is just the homogeneous `disc`.

This is an API-coherence lemma: many offset lemmas specialize cleanly to homogeneous statements
once `m = 0` is normalized away.
-/
@[simp] lemma discOffset_zero_start (f : ℕ → ℤ) (d n : ℕ) :
    discOffset f d 0 n = disc f d n := by
  unfold discOffset disc
  simp

/-- Triangle inequality for `apSum` by splitting into a prefix and a shifted suffix. -/
lemma natAbs_apSum_add_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    Int.natAbs (apSum f d (n₁ + n₂)) ≤
      Int.natAbs (apSum f d n₁) + Int.natAbs (apSumOffset f d n₁ n₂) := by
  -- This is `natAbs_apSumOffset_add_le` at `m = 0`, with the definitional rewrite
  -- `apSumOffset f d 0 _ = apSum f d _`.
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_add_le (f := f) (d := d) (m := 0) (n₁ := n₁) (n₂ := n₂))

/-- Triangle inequality for `disc` by splitting into a prefix and a shifted suffix.

This is the homogeneous analogue of `discOffset_add_le`.
-/
lemma disc_add_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    disc f d (n₁ + n₂) ≤ disc f d n₁ + discOffset f d n₁ n₂ := by
  simpa using (natAbs_apSum_add_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))

/-! ### Basic inequalities for sign sequences -/

/-! ### General `Int.natAbs` bounds for offset AP sums -/

/-- Uniform bound on `Int.natAbs` gives a length-times-bound estimate for offset AP sums.

If `|f k| ≤ B` for every term, then the offset AP partial sums satisfy
`|apSumOffset f d m n| ≤ n * B`.

This is the nucleus form of the standard “triangle inequality + induction on length” bound,
parameterised by the per-term bound `B`.
-/
lemma natAbs_apSumOffset_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hterm : Int.natAbs (f ((m + n + 1) * d)) ≤ B := hf _
      have hsum :
          apSumOffset f d m (n + 1) =
            apSumOffset f d m n + f ((m + n + 1) * d) := by
        simp [apSumOffset, Finset.sum_range_succ, Nat.add_assoc]
      calc
        Int.natAbs (apSumOffset f d m (n + 1))
            = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
                simpa [hsum]
        _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
                simpa using
                  (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
        _ ≤ n * B + B := by
                exact Nat.add_le_add ih hterm
        _ = (n + 1) * B := by
                simpa [Nat.succ_mul, Nat.add_assoc]

/-- Uniform `Int.natAbs` bound gives a length-times-bound estimate for `discOffset`. -/
lemma discOffset_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (d m n : ℕ) :
    discOffset f d m n ≤ n * B := by
  simpa using
    (natAbs_apSumOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := m)
      (n := n))

/-- Uniform bound on `Int.natAbs` gives a length-times-bound estimate for homogeneous AP sums.

This is the `apSum` specialization of `natAbs_apSumOffset_le_mul_of_natAbs_le`.
-/
lemma natAbs_apSum_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n * B := by
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := 0)
      (n := n))

/-- Uniform `Int.natAbs` bound gives a length-times-bound estimate for `disc`. -/
lemma disc_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (d n : ℕ) :
    disc f d n ≤ n * B := by
  simpa using
    (natAbs_apSum_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (n := n))

/-- If the terms of `f` are uniformly bounded by `1` in `Int.natAbs`, then any offset AP sum has
`Int.natAbs` bounded by its length.

This is the nucleus form of the standard “triangle inequality + induction on length” bound.
-/
lemma natAbs_apSumOffset_le_of_natAbs_le_one {f : ℕ → ℤ}
    (hf : ∀ k, Int.natAbs (f k) ≤ 1) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hterm : Int.natAbs (f ((m + n + 1) * d)) ≤ 1 := hf _
      have hsum :
          apSumOffset f d m (n + 1) =
            apSumOffset f d m n + f ((m + n + 1) * d) := by
        simp [apSumOffset, Finset.sum_range_succ, Nat.add_assoc]
      calc
        Int.natAbs (apSumOffset f d m (n + 1))
            = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
                simpa [hsum]
        _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
                simpa using
                  (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
        _ ≤ n + 1 :=
                Nat.add_le_add ih hterm

/-- Uniform `Int.natAbs` bound by `1` gives a length bound for `discOffset`. -/
lemma discOffset_le_of_natAbs_le_one {f : ℕ → ℤ}
    (hf : ∀ k, Int.natAbs (f k) ≤ 1) (d m n : ℕ) :
    discOffset f d m n ≤ n := by
  simpa using
    (natAbs_apSumOffset_le_of_natAbs_le_one (f := f) (hf := hf) (d := d) (m := m) (n := n))

/-- A sign sequence has `Int.natAbs` bounded by length on any offset AP sum. -/
lemma natAbs_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  refine natAbs_apSumOffset_le_of_natAbs_le_one (f := f) (d := d) (m := m) (n := n) ?_ 
  intro k
  rcases hf k with h | h <;> simp [h]

/-- If the terms of `f` are uniformly bounded by `1` in `Int.natAbs`, then any AP sum has
`Int.natAbs` bounded by its length.

This is the `apSum` specialization of `natAbs_apSumOffset_le_of_natAbs_le_one`.
-/
lemma natAbs_apSum_le_of_natAbs_le_one {f : ℕ → ℤ}
    (hf : ∀ k, Int.natAbs (f k) ≤ 1) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n := by
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_le_of_natAbs_le_one (f := f) (hf := hf) (d := d) (m := 0) (n := n))

/-- If the terms of `f` are uniformly bounded by `1` in `Int.natAbs`, then `disc f d n ≤ n`. -/
lemma disc_le_of_natAbs_le_one {f : ℕ → ℤ}
    (hf : ∀ k, Int.natAbs (f k) ≤ 1) (d n : ℕ) :
    disc f d n ≤ n := by
  simpa using (natAbs_apSum_le_of_natAbs_le_one (f := f) (hf := hf) (d := d) (n := n))

/-- A sign sequence has `Int.natAbs` bounded by length on any AP sum. -/
lemma natAbs_apSum_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n := by
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_le (hf := hf) (d := d) (m := 0) (n := n))

/-- A sign sequence has discrepancy (at the `disc` level) bounded by length. -/
lemma disc_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    disc f d n ≤ n := by
  simpa using (natAbs_apSum_le (hf := hf) (d := d) (n := n))

/-!
### Size bound for sign sequences (`discOffset` / `discAlong`)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Basic size bound for sign sequences.
-/

/-- A sign sequence has offset discrepancy bounded by length.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Basic size bound for sign sequences.
-/
lemma discOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    discOffset f d m n ≤ n := by
  -- Avoid `simp` loops between `discOffset` and `Int.natAbs (apSumOffset ...)`.
  change Int.natAbs (apSumOffset f d m n) ≤ n
  simpa using (natAbs_apSumOffset_le (hf := hf) (d := d) (m := m) (n := n))

/-- A sign sequence has along-`d` discrepancy bounded by length.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Basic size bound for sign sequences.
-/
lemma discAlong_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    discAlong f d n ≤ n := by
  -- `discAlong` is definitionaly `discOffset f d 0`.
  simpa [discAlong] using (discOffset_le (f := f) (hf := hf) (d := d) (m := 0) (n := n))

/-- Bounding a *difference of discrepancies* (offset AP sums) by total length.

Useful for triangle-inequality pipelines: `|Sₙ - Sₙ'| ≤ |Sₙ| + |Sₙ'| ≤ n + n'`.
-/
lemma natAbs_apSumOffset_sub_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n n' : ℕ) :
    Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤ n + n' := by
  have hn : Int.natAbs (apSumOffset f d m n) ≤ n := natAbs_apSumOffset_le (hf := hf) d m n
  have hn' : Int.natAbs (apSumOffset f d m n') ≤ n' := natAbs_apSumOffset_le (hf := hf) d m n'
  -- `natAbs_sub_le` is the triangle inequality for subtraction.
  refine le_trans (Int.natAbs_sub_le (apSumOffset f d m n) (apSumOffset f d m n')) ?_
  -- Push the bound through addition.
  exact Nat.add_le_add hn hn'

/-- `f` has discrepancy at least `C` if some AP partial sum exceeds `C` in absolute value,
with a **positive** step size `d ≥ 1`.

We compare via `Int.natAbs` so `C : ℕ` stays natural.
-/
def HasDiscrepancyAtLeast (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSum f d n) > C

/-- Sign-flip invariance: negating the sequence does not change discrepancy. -/
@[simp] lemma HasDiscrepancyAtLeast_neg_iff (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast (fun k => -f k) C ↔ HasDiscrepancyAtLeast f C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    have hnatAbs : Int.natAbs (apSum (fun k => -f k) d n) = Int.natAbs (apSum f d n) := by
      unfold apSum
      simp
    simpa [hnatAbs] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    have hnatAbs : Int.natAbs (apSum (fun k => -f k) d n) = Int.natAbs (apSum f d n) := by
      unfold apSum
      simp
    -- Rewrite the goal to match `hgt`.
    simpa [hnatAbs] using hgt

/-- Monotonicity of `HasDiscrepancyAtLeast` in the bound.

⚠️ Note the direction: `HasDiscrepancyAtLeast f C` is **easier** to satisfy for smaller `C`
(because the witness inequality is `> C`). So the predicate is antitone in `C`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `HasDiscrepancyAtLeast` monotone-in-`C`
API (avoid unfolding definitions in quantifier manipulations).
-/
lemma HasDiscrepancyAtLeast.mono {f : ℕ → ℤ} {C₁ C₂ : ℕ}
    (h : HasDiscrepancyAtLeast f C₂) (hC : C₁ ≤ C₂) : HasDiscrepancyAtLeast f C₁ := by
  rcases h with ⟨d, n, hd, hn⟩
  exact ⟨d, n, hd, lt_of_le_of_lt hC hn⟩

/-- Contrapositive monotonicity: if you cannot beat a smaller bound, you cannot beat a larger one.

This is the logically convenient “negated” form used when normalizing boundedness hypotheses.
-/
lemma HasDiscrepancyAtLeast.not_mono {f : ℕ → ℤ} {C₁ C₂ : ℕ}
    (h : ¬ HasDiscrepancyAtLeast f C₁) (hC : C₁ ≤ C₂) : ¬ HasDiscrepancyAtLeast f C₂ := by
  intro h₂
  exact h (HasDiscrepancyAtLeast.mono (f := f) (C₁ := C₁) (C₂ := C₂) h₂ hC)

/-- Decrease the bound by one. -/
lemma HasDiscrepancyAtLeast.of_succ {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f (C + 1)) : HasDiscrepancyAtLeast f C := by
  exact
    HasDiscrepancyAtLeast.mono (f := f) (C₁ := C) (C₂ := C + 1) h (Nat.le_succ C)

/-- If we can beat every bound by one, we can beat every bound.

This is a small but frequently useful “quantifier-level” normal form: it lets you assume a
strictly-stronger hypothesis `HasDiscrepancyAtLeast f (C+1)` and immediately obtain the standard
unbounded-discrepancy statement.
-/
theorem forall_hasDiscrepancyAtLeast_of_succ (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f (C + 1)) → (∀ C : ℕ, HasDiscrepancyAtLeast f C) := by
  intro h C
  exact HasDiscrepancyAtLeast.of_succ (h C)

/-- From a discrepancy witness obtain `d` and `n` both positive. -/
lemma HasDiscrepancyAtLeast.exists_witness_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  cases n with
  | zero =>
      -- `apSum f d 0 = 0`, so `natAbs` cannot be strictly greater than `C`.
      exfalso
      have : (0 : ℕ) > C := by
        simpa [apSum] using hgt
      have hgt' : C < 0 := by
        simpa [gt_iff_lt] using this
      exact Nat.not_lt_zero C hgt'
  | succ n' =>
      refine ⟨d, Nat.succ n', hd, Nat.succ_pos n', ?_⟩
      exact hgt

/-- From a discrepancy witness obtain a step size `d ≥ 1`. -/
lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  exact ⟨d, n, Nat.succ_le_of_lt hd, hgt⟩

/-- From a discrepancy witness obtain `d ≥ 1` *and* `n > 0`.

This is a common “surface statement” normal form when working with natural step sizes.
-/
lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  rcases HasDiscrepancyAtLeast.exists_witness_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
  exact ⟨d, n, Nat.succ_le_of_lt hd, hn, hgt⟩

/-!
### Step-positivity witness normal forms (`d = Nat.succ d'`)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.

These lemmas package the (automatic) `d ≥ 1` side condition by writing the step as `Nat.succ d'`.
This lets downstream code avoid carrying separate inequalities.
-/

/-- From a discrepancy witness obtain a witness whose step is written as `Nat.succ d`. -/
lemma HasDiscrepancyAtLeast.exists_witness_succ {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n : ℕ, Int.natAbs (apSum f (Nat.succ d) n) > C := by
  rcases HasDiscrepancyAtLeast.exists_witness_d_ge_one (h := h) with ⟨d, n, hd, hgt⟩
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  rcases Nat.exists_eq_succ_of_ne_zero hd0 with ⟨d', rfl⟩
  exact ⟨d', n, hgt⟩

/-- Variant of `HasDiscrepancyAtLeast.exists_witness_succ` also recording `n > 0`. -/
lemma HasDiscrepancyAtLeast.exists_witness_succ_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n : ℕ, n > 0 ∧ Int.natAbs (apSum f (Nat.succ d) n) > C := by
  rcases HasDiscrepancyAtLeast.exists_witness_d_ge_one_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  rcases Nat.exists_eq_succ_of_ne_zero hd0 with ⟨d', rfl⟩
  exact ⟨d', n, hn, hgt⟩

/-- `HasDiscrepancyAtLeast` can be stated with `d` and `n` both positive.

This is often the most readable form for conjecture statements, and it lets you
convert back to the nucleus predicate without unfolding definitions.
-/
lemma HasDiscrepancyAtLeast_iff_exists_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  constructor
  · intro h
    exact HasDiscrepancyAtLeast.exists_witness_pos (h := h)
  · rintro ⟨d, n, hd, hn, hgt⟩
    exact ⟨d, n, hd, hgt⟩

/-- Normal form: rewrite `HasDiscrepancyAtLeast` using the offset-sum API `apSumOffset … 0 n`.

This is definitionally the same notion (since `apSumOffset f d 0 n = apSum f d n`), but it is
sometimes more convenient when downstream developments are already in the “tail sum” vocabulary.
-/
lemma HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_start {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset f d 0 n) > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    -- NOTE: `apSumOffset_zero_start` is proved later in this file, so we unfold here.
    have h0 : apSumOffset f d 0 n = apSum f d n := by
      unfold apSumOffset apSum
      simp
    simpa [h0] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    have h0 : apSumOffset f d 0 n = apSum f d n := by
      unfold apSumOffset apSum
      simp
    -- rewrite the offset-sum witness back into the homogeneous-sum form.
    simpa [h0] using hgt

/-- Normal form: rewrite `HasDiscrepancyAtLeast` into the `discOffset` wrapper.

This is the `discOffset`-valued analogue of
`HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_start`, and it avoids exposing
`Int.natAbs (apSumOffset …)` in downstream witness statements.
-/
lemma HasDiscrepancyAtLeast_iff_exists_discOffset_zero_start {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ discOffset f d 0 n > C := by
  -- Reduce to the existing offset-sum normal form and rewrite the absolute-value wrapper.
  simpa using (HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_start (f := f) (C := C))

-- Backwards-compatibility: earlier versions used the slightly confusing names
-- `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero` and
-- `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_m`; the deprecated aliases live in
-- `MoltResearch.Discrepancy.Deprecated`.

/-- Restate `HasDiscrepancyAtLeast` using the `discrepancy` wrapper. -/
lemma HasDiscrepancyAtLeast_iff_exists_discrepancy (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d > 0 ∧ discrepancy f d n > C := by
  unfold HasDiscrepancyAtLeast discrepancy
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, hd, hgt⟩
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, hd, hgt⟩

/-!
### Predicate-level wrappers: fixed-step discrepancy (`along d`)

These are small normal-form helpers used by the Tao 2015 reduction pipeline.
-/

/-- Fixed-step discrepancy predicate (“discrepancy at least `C` along step `d`”).

This is the `d`-fixed analogue of `HasDiscrepancyAtLeast`.
-/
def HasDiscrepancyAtLeastAlong (f : ℕ → ℤ) (d C : ℕ) : Prop :=
  ∃ n : ℕ, discrepancy f d n > C

namespace HasDiscrepancyAtLeastAlong

/-- Definitional witness form. -/
lemma iff_exists_discrepancy_gt (f : ℕ → ℤ) (d C : ℕ) :
    HasDiscrepancyAtLeastAlong f d C ↔ (∃ n : ℕ, discrepancy f d n > C) :=
  Iff.rfl

/-- Canonical bridge: `HasDiscrepancyAtLeastAlong` for a literal shift by `m*d` rewrites to a
`discOffset` witness normal form.

This is the Track B checklist item “bridge lemma: along-`d` predicate → `discOffset` witnesses”.
-/
lemma shift_mul_iff_exists_discOffset_lt (f : ℕ → ℤ) (d m C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔ (∃ n : ℕ, C < discOffset f d m n) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Normalize `discrepancy` of the shift to an `Int.natAbs (apSumOffset …)` statement,
    -- then repackage as `discOffset`.
    have hn' : Int.natAbs (apSumOffset f d m n) > C := by
      simpa [discrepancy_shift_mul] using hn
    -- Convert `>` to `<` (avoid simp loops between `discOffset` and `Int.natAbs`).
    unfold discOffset
    simpa [gt_iff_lt] using hn'
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Unfold `discOffset` back to the raw `Int.natAbs (apSumOffset …)` statement.
    have hn' : Int.natAbs (apSumOffset f d m n) > C := by
      -- First unfold, then switch between `<` and `>`.
      unfold discOffset at hn
      simpa [gt_iff_lt] using hn
    -- Package back into `discrepancy (shift)`.
    simpa [HasDiscrepancyAtLeastAlong, discrepancy_shift_mul] using hn'

/-- Canonical bridge: along-`d` predicate rewrites to the `discOffset … 0 n` witness normal form.

This is the unshifted specialization of `shift_mul_iff_exists_discOffset_lt`.
-/
lemma iff_exists_discOffset_zero_start_lt (f : ℕ → ℤ) (d C : ℕ) :
    HasDiscrepancyAtLeastAlong f d C ↔ (∃ n : ℕ, C < discOffset f d 0 n) := by
  -- Specialize the shift lemma to `m = 0`, then normalize the definitional shift.
  simpa using
    (HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt
      (f := f) (d := d) (m := 0) (C := C))

/-- Along-`d` witness normal form using the specialized wrapper `discAlong`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Along-`d` API coherence (`discAlong`).
-/
lemma iff_exists_discAlong_lt (f : ℕ → ℤ) (d C : ℕ) :
    HasDiscrepancyAtLeastAlong f d C ↔ (∃ n : ℕ, C < discAlong f d n) := by
  simpa [discAlong] using (HasDiscrepancyAtLeastAlong.iff_exists_discOffset_zero_start_lt (f := f) (d := d) (C := C))

end HasDiscrepancyAtLeastAlong

/-- Unbounded discrepancy along a fixed step `d` (witness normal form).

This is the “along `d`” analogue of the global statement `∀ C, HasDiscrepancyAtLeast f C`.
-/
def UnboundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∀ C : ℕ, HasDiscrepancyAtLeastAlong f d C

namespace UnboundedDiscrepancyAlong

/-- Canonical bridge: unbounded discrepancy for the literal shift `k ↦ f (k + m*d)` rewrites
to a `discOffset` witness normal form.
-/
theorem shift_mul_iff_forall_exists_discOffset_lt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscrepancyAlong (fun k => f (k + m * d)) d ↔
      (∀ C : ℕ, ∃ n : ℕ, C < discOffset f d m n) := by
  unfold UnboundedDiscrepancyAlong
  constructor
  · intro h C
    exact
      (HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt
          (f := f) (d := d) (m := m) (C := C)).1
        (h C)
  · intro h C
    exact
      (HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt
          (f := f) (d := d) (m := m) (C := C)).2
        (h C)

/-- Canonical bridge: unbounded discrepancy along `d` rewrites to the `discOffset … 0 n` ∀∃ normal form.

This is the unshifted specialization of `shift_mul_iff_forall_exists_discOffset_lt`.
-/
theorem iff_forall_exists_discOffset_zero_start_lt (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ (∀ C : ℕ, ∃ n : ℕ, C < discOffset f d 0 n) := by
  -- Specialize the shift lemma to `m = 0`, then normalize the definitional shift.
  simpa using
    (UnboundedDiscrepancyAlong.shift_mul_iff_forall_exists_discOffset_lt
      (f := f) (d := d) (m := 0))

end UnboundedDiscrepancyAlong

/-- API coherence: `UnboundedDiscrepancyAlong` agrees with the direct `discAlong` witness normal form.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Unboundedness normal form (forall-exists, discAlong).
-/
theorem unboundedDiscrepancyAlong_iff_unboundedDiscAlong (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ UnboundedDiscAlong f d := by
  unfold UnboundedDiscrepancyAlong UnboundedDiscAlong
  constructor
  · intro h B
    exact (HasDiscrepancyAtLeastAlong.iff_exists_discAlong_lt (f := f) (d := d) (C := B)).1 (h B)
  · intro h B
    exact (HasDiscrepancyAtLeastAlong.iff_exists_discAlong_lt (f := f) (d := d) (C := B)).2 (h B)


/-- Variant with the step-size side condition written as `d ≥ 1`. -/
lemma HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d ≥ 1 ∧ discrepancy f d n > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, Nat.succ_le_of_lt hd, hgt⟩
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, (Nat.succ_le_iff).1 hd, hgt⟩

/-- Variant with side conditions `d ≥ 1` and `n > 0` (useful for “surface statement” witnesses). -/
lemma HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one_witness_pos (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C := by
  constructor
  · intro h
    rcases HasDiscrepancyAtLeast.exists_witness_d_ge_one_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
    refine ⟨d, n, hd, hn, ?_⟩
    simpa using hgt
  · rintro ⟨d, n, hd, _hn, hgt⟩
    refine ⟨d, n, (Nat.succ_le_iff).1 hd, ?_⟩
    simpa using hgt

/-- The “unbounded discrepancy” statement `∀ C, HasDiscrepancyAtLeast f C` is equivalent to
the more explicit witness form `∀ C, ∃ d n > 0, …`.

This is the intended bridge for conjecture stubs: state the theorem using the nucleus predicate,
and rewrite to the quantifier-heavy version only when needed.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_witness_pos (f := f) (C := C)).2 (h C)

/-- The step-size side condition `d > 0` can be written as `d ≥ 1`. -/
lemma HasDiscrepancyAtLeast_iff_exists_d_ge_one {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d ≥ 1 ∧ Int.natAbs (apSum f d n) > C := by
  constructor
  · intro h
    exact HasDiscrepancyAtLeast.exists_witness_d_ge_one (h := h)
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, ?_, hgt⟩
    exact (Nat.succ_le_iff).1 hd

/-- Convenience witness normal form: `HasDiscrepancyAtLeast f C` has a witness with
`d ≥ 1` and `n > 0`.

The `n > 0` side condition is automatic from `Int.natAbs (apSum f d n) > C`, but it is often
useful to keep it explicit in “surface” statements.
-/
lemma HasDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  constructor
  · intro h
    rcases HasDiscrepancyAtLeast.exists_witness_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
    exact ⟨d, n, Nat.succ_le_of_lt hd, hn, hgt⟩
  · rintro ⟨d, n, hd, _hn, hgt⟩
    refine ⟨d, n, (Nat.succ_le_iff).1 hd, hgt⟩

/-- Bridge: the unbounded discrepancy statement `∀ C, HasDiscrepancyAtLeast f C` is equivalent to
an explicit witness form with side conditions `d ≥ 1` and `n > 0`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos (f := f) (C := C)).2 (h C)

/-- Unpack the defining property. -/
lemma IsSignSequence.eq_one_or_eq_neg_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    f n = 1 ∨ f n = -1 :=
  hf n

/-- A sign sequence stays a sign sequence after reindexing by any function `g : ℕ → ℕ`. -/
lemma IsSignSequence.comp {f : ℕ → ℤ} (g : ℕ → ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (g n)) := by
  intro n
  simpa using hf (g n)

/-- Reindexing a sign sequence by a fixed additive shift preserves the sign-sequence property.

This uses the translation-friendly convention `n ↦ n + k`.
-/
lemma IsSignSequence.shift_add {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (n + k)) :=
  IsSignSequence.comp (f := f) (fun n => n + k) hf

/-- Add-left variant of `IsSignSequence.shift_add`.

This uses the `n ↦ k + n` binder convention.
-/
lemma IsSignSequence.shift_add_left {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (k + n)) :=
  IsSignSequence.comp (f := f) (fun n => k + n) hf

/-- Reindexing a sign sequence by a fixed multiplicative map preserves the sign-sequence property. -/
lemma IsSignSequence.map_mul {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (n * k)) :=
  IsSignSequence.comp (f := f) (fun n => n * k) hf

lemma IsSignSequence.natAbs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    Int.natAbs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

/-- Normal form: a function is a sign sequence iff all its values have `Int.natAbs = 1`.

This is often the most convenient way to *consume* the `IsSignSequence` hypothesis in proofs,
while the `f n = 1 ∨ f n = -1` form is convenient to *produce* it.
-/
lemma isSignSequence_iff_forall_natAbs_eq_one (f : ℕ → ℤ) :
    IsSignSequence f ↔ ∀ n, Int.natAbs (f n) = 1 := by
  constructor
  · intro hf n
    exact IsSignSequence.natAbs_eq_one (hf := hf) n
  · intro h n
    -- use the `natAbs` normal form to recover the `±1` pointwise description
    have hn : (f n).natAbs = 1 := h n
    have h' : f n = (1 : ℤ) ∨ f n = - (1 : ℤ) := (Int.natAbs_eq_iff (a := f n) (n := 1)).1 hn
    simpa using h'

/-- Normal form: a function is a sign sequence iff all its values have `abs = 1`.

This is a sibling of `isSignSequence_iff_forall_natAbs_eq_one` that can be convenient when you
want to stay in `ℤ` instead of converting through `Int.natAbs`.
-/
lemma isSignSequence_iff_forall_abs_eq_one (f : ℕ → ℤ) :
    IsSignSequence f ↔ ∀ n, abs (f n) = (1 : ℤ) := by
  constructor
  · intro hf n
    rcases hf n with h | h <;> simp [h]
  · intro h n
    -- `abs x = 1` implies `x = 1 ∨ x = -1`.
    have h' : f n = (1 : ℤ) ∨ f n = - (1 : ℤ) :=
      (abs_eq (zero_le_one' ℤ)).1 (h n)
    simpa using h'

/-- Normal form: for a sign sequence, the integer absolute value satisfies `|f n| = 1`. -/
lemma IsSignSequence.abs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    abs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

/-- A sign sequence is pointwise bounded by `1` in absolute value. -/
lemma IsSignSequence.abs_le_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    abs (f n) ≤ 1 := by
  simp [hf.abs_eq_one n]

/-- Any ±1 sequence has discrepancy at least 0 (take d = 1, n = 1). -/
lemma IsSignSequence.hasDiscrepancyAtLeast_zero {f : ℕ → ℤ} (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  unfold HasDiscrepancyAtLeast
  refine ⟨1, 1, ?_, ?_⟩
  · decide
  · simp [apSum, IsSignSequence.natAbs_eq_one (hf := hf) 1]

lemma IsSignSequence.intNatAbs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    (Int.natAbs (f n) : ℤ) = 1 := by
  simpa using
    congrArg (fun k : ℕ => (k : ℤ)) (IsSignSequence.natAbs_eq_one (hf := hf) n)

lemma IsSignSequence.ne_zero {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) : f n ≠ 0 := by
  rcases hf n with h | h <;> simp [h]

/-- Helper lemmas for `Int.natAbs`. -/
lemma natAbs_pos_of_ne_zero {c : ℤ} (hc : c ≠ 0) : 0 < Int.natAbs c := by
  exact Int.natAbs_pos.2 hc

lemma one_le_natAbs_of_ne_zero {c : ℤ} (hc : c ≠ 0) : 1 ≤ Int.natAbs c := by
  exact Nat.succ_le_iff.2 (natAbs_pos_of_ne_zero (c := c) hc)

@[simp] lemma apSum_zero (f : ℕ → ℤ) (d : ℕ) : apSum f d 0 = 0 := by
  simp [apSum]

@[simp] lemma apSum_one (f : ℕ → ℤ) (d : ℕ) : apSum f d 1 = f d := by
  simp [apSum]

/-- Rewrite `apSum` as the more familiar sum `∑ i ∈ Icc 1 n, f (i*d)`.

This is intended for conjecture/theorem statements: it matches the usual notation
`∑_{i=1}^n f(i*d)` while the nucleus API continues to use `apSum`.
-/
lemma apSum_eq_sum_Icc (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  classical
  unfold apSum
  -- `Icc 1 n` is `Ico 1 (n+1)`; convert interval sums to `Finset.range`.
  have h :=
    (Finset.sum_Ico_eq_sum_range (f := fun i => f (i * d)) (m := 1) (n := n + 1))
  -- `h` is oriented from `Ico` to `range`; we use it backwards.
  calc
    (Finset.range n).sum (fun i => f ((i + 1) * d))
        = (Finset.range n).sum (fun i => f ((1 + i) * d)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- `i + 1 = 1 + i`
            simp [Nat.add_comm]
    _ = (Finset.Ico 1 (n + 1)).sum (fun i => f (i * d)) := by
            simpa [Nat.add_sub_cancel] using h.symm
    _ = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
            simp [Finset.Ico_add_one_right_eq_Icc]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (i*d)` back to `apSum`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSum (f : ℕ → ℤ) (d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using (apSum_eq_sum_Icc (f := f) (d := d) (n := n)).symm

/-!
### NEW (Track B): `Icc` ↔ `apSumOffset` normal form (affine endpoints)

Checklist item: Problems/erdos_discrepancy.md (Track B) —
Icc↔offset sum normal form (affine endpoints).

This lemma is designed to be a one-step rewrite from the common “paper notation”
interval sum `∑ i ∈ Icc (m+1) (m+n), f (a + i*d)` to the nucleus API
`apSumOffset (fun k => f (a + k)) d m n`.
-/

/-- Rewrite an affine-argument interval sum `∑ i ∈ Icc (m+1) (m+n), f (a + i*d)` as an
offset arithmetic-progression sum `apSumOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
Icc↔offset sum normal form (affine endpoints).
-/
lemma sum_Icc_affine_eq_apSumOffset (f : ℕ → ℤ) (a d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (a + k)) d m n := by
  classical
  unfold apSumOffset
  -- Rewrite `Icc` as `Ico` and then use the standard `Ico`-to-`range` conversion.
  have h :=
    (Finset.sum_Ico_eq_sum_range (f := fun i => f (a + i * d)) (m := m + 1) (n := m + n + 1))
  -- `m + n + 1 - (m + 1) = n`.
  have hsub : m + n + 1 - (m + 1) = n := by
    -- Use the canonical “subtract the same left addend” normal form.
    simpa [Nat.add_assoc] using (Nat.add_sub_add_left m (n + 1) 1)
  calc
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
        (Finset.Ico (m + 1) (m + n + 1)).sum (fun i => f (a + i * d)) := by
          simp [Finset.Ico_add_one_right_eq_Icc]
    _ = (Finset.range (m + n + 1 - (m + 1))).sum (fun i => f (a + (m + 1 + i) * d)) := by
          -- `h` is oriented from `Ico` to `range`.
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    _ = (Finset.range n).sum (fun i => f (a + (m + i + 1) * d)) := by
          -- Normalize the range length and reassociate `m+1+i`.
          refine Finset.sum_congr (by simpa [hsub]) ?_
          intro i hi
          -- `m + 1 + i = m + i + 1`.
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = (Finset.range n).sum (fun i => (fun k => f (a + k)) ((m + i + 1) * d)) := by
          rfl

/-!
Note: deprecated `*_mul_left` paper-notation wrappers live in `MoltResearch.Discrepancy.Deprecated`.
The stable surface uses the `i * d` convention (`apSum_eq_sum_Icc` / `sum_Icc_eq_apSum`).
-/


/-- Special case: step size `d = 1` turns `apSum` into the plain interval sum `∑ i ∈ Icc 1 n, f i`.

This is often the most readable surface form when you have already normalized the step size.
-/
lemma apSum_one_d (f : ℕ → ℤ) (n : ℕ) : apSum f 1 n = (Finset.Icc 1 n).sum f := by
  simpa using (apSum_eq_sum_Icc (f := f) (d := 1) (n := n))

/-- `HasDiscrepancyAtLeast` can be stated using the more familiar interval sum
`∑ i ∈ Icc 1 n, f (i*d)`.

This is a convenience lemma for conjecture/theorem statements: keep the nucleus
predicate as the normalization boundary, and rewrite to this form only at the surface.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt

/-- Variant of `HasDiscrepancyAtLeast_iff_exists_sum_Icc` writing the step-size side condition
as `d ≥ 1` instead of `d > 0`.

This is often the most readable surface form when `d : ℕ`.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d ≥ 1 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · intro h
    rcases (HasDiscrepancyAtLeast_iff_exists_d_ge_one (f := f) (C := C)).1 h with ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine (HasDiscrepancyAtLeast_iff_exists_d_ge_one (f := f) (C := C)).2 ?_
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt

/-- Variant of `HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one` that also records the (automatic)
side condition `n > 0`.

This is often the cleanest “paper notation” witness normal form: a positive step size `d ≥ 1`,
a positive length, and an interval sum exceeding the bound.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ,
        d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · intro h
    rcases HasDiscrepancyAtLeast.exists_witness_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
    refine ⟨d, n, Nat.succ_le_of_lt hd, hn, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt
  · rintro ⟨d, n, hd, _hn, hgt⟩
    refine ⟨d, n, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.zero_lt_one hd
    · simpa [apSum_eq_sum_Icc] using hgt

/-- Bridge: `∀ C, HasDiscrepancyAtLeast f C` written in the interval-sum witness normal form
with side conditions `d ≥ 1` and `n > 0`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).2 (h C)

/-- Variant of `HasDiscrepancyAtLeast_iff_exists_sum_Icc` that also records the (automatic)
side condition `n > 0`.

This is the closest match to the usual “paper statement” of the Erdős discrepancy problem: a
positive step size `d > 0`, a positive length, and an interval sum exceeding the bound.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ,
        d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · intro h
    rcases
        (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).1 h with
      ⟨d, n, hd, hn, hgt⟩
    exact ⟨d, n, lt_of_lt_of_le Nat.zero_lt_one hd, hn, hgt⟩
  · rintro ⟨d, n, hd, hn, hgt⟩
    refine (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).2 ?_
    exact ⟨d, n, Nat.succ_le_of_lt hd, hn, hgt⟩

/-- Bridge: `∀ C, HasDiscrepancyAtLeast f C` written in the interval-sum witness normal form
with side conditions `d > 0` and `n > 0`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos (f := f) (C := C)).2 (h C)

/-- Bridge: the unbounded discrepancy statement phrased using `HasDiscrepancyAtLeast`
is equivalent to the more explicit “interval sum” form `∑ i ∈ Icc 1 n, f (i*d)`.

This is intended for conjecture/theorem statements: downstream files can keep the nucleus
predicate as a normalization boundary, and then rewrite to the quantifier-heavy surface form
without unfolding definitions.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc (f := f) (C := C)).2 (h C)

/-- Bridge: the unbounded discrepancy statement `∀ C, HasDiscrepancyAtLeast f C` is equivalent to
an explicit witness form using the interval sum `∑ i ∈ Icc 1 n, f (i*d)` with side condition
`d ≥ 1` (instead of `d > 0`).

This is intended as a surface rewrite lemma: keep `HasDiscrepancyAtLeast` as the normalization
boundary and only expand to quantifiers when needed.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one (f := f) (C := C)).2 (h C)

/-! ### Degenerate length simp lemmas

These mirror `apSum_zero` / `apSum_one` for the offset nucleus `apSumOffset`.
-/
section apSumOffset_degenerate

@[simp] lemma apSumOffset_zero (f : ℕ → ℤ) (d m : ℕ) : apSumOffset f d m 0 = 0 := by
  simp [apSumOffset]

@[simp] lemma apSumOffset_one (f : ℕ → ℤ) (d m : ℕ) : apSumOffset f d m 1 = f ((m + 1) * d) := by
  simp [apSumOffset]

end apSumOffset_degenerate

/-! ### Degenerate length simp lemmas for `discOffset`

These are the `natAbs`/`ℕ`-valued counterparts of `apSumOffset_zero` / `apSumOffset_one`.
They are meant to reduce “degenerate tail” boilerplate at the discrepancy level.
-/
section discOffset_degenerate

@[simp] lemma discOffset_zero (f : ℕ → ℤ) (d m : ℕ) : discOffset f d m 0 = 0 := by
  unfold discOffset
  simp

@[simp] lemma discOffset_one (f : ℕ → ℤ) (d m : ℕ) :
    discOffset f d m 1 = Int.natAbs (f ((m + 1) * d)) := by
  unfold discOffset
  simp

end discOffset_degenerate

/-! ### Degenerate length simp lemmas for homogeneous wrappers -/
section disc_degenerate

@[simp] lemma disc_one (f : ℕ → ℤ) (d : ℕ) : disc f d 1 = Int.natAbs (f d) := by
  unfold disc
  simp [apSum_one]

@[simp] lemma discrepancy_one (f : ℕ → ℤ) (d : ℕ) : discrepancy f d 1 = Int.natAbs (f d) := by
  unfold discrepancy
  simp [apSum_one]

end disc_degenerate

-- (deprecated alias moved to `MoltResearch.Discrepancy.Deprecated`)

lemma apSumOffset_succ (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  classical
  -- expand definition and use `Finset.range_add_one`
  unfold apSumOffset
  simp [Finset.range_add_one, Finset.sum_insert, add_comm, add_assoc]

/-- (Track B checklist item) Canonical one-step difference lemma for `apSumOffset`.

This is a `simp`-friendly way to express that extending the length by one adds exactly the next term.
-/
lemma apSumOffset_succ_sub (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 1) - apSumOffset f d m n = f ((m + n + 1) * d) := by
  -- `S(n+1) = S(n) + term`, so subtracting `S(n)` leaves `term`.
  simp [apSumOffset_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Lipschitz-in-length: for a sign sequence, the offset AP partial sums change by at most `1`
(in `Int.natAbs`) when increasing the length by one.

Checklist item (Track B): `apSumOffset` one-step extension + Lipschitz bound.
- `apSumOffset f d m (n+1) = apSumOffset f d m n + f ((m+n+1)*d)` (`apSumOffset_succ`)
- `Int.natAbs (apSumOffset … (n+1)) ≤ Int.natAbs (apSumOffset … n) + 1` (this lemma)
-/
lemma IsSignSequence.natAbs_apSumOffset_succ_le {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m (n + 1)) ≤ Int.natAbs (apSumOffset f d m n) + 1 := by
  -- one-step extension, then triangle inequality
  calc
    Int.natAbs (apSumOffset f d m (n + 1))
        = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
          simp [apSumOffset_succ, Nat.add_assoc, Nat.add_left_comm]
    _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
          simpa using
            (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
    _ = Int.natAbs (apSumOffset f d m n) + 1 := by
          simp [IsSignSequence.natAbs_eq_one (hf := hf)]

/-! ### DiscOffset Lipschitz bounds -/

/-- (Track B checklist item) Canonical one-step inequality for `discOffset`.

This is the fully general triangle-inequality form:
`discOffset … (n+1)` is bounded by `discOffset … n` plus the `Int.natAbs` of the next term.

The sign-sequence specialization `IsSignSequence.discOffset_succ_le` follows by rewriting
`Int.natAbs (f _) = 1`. -/
lemma discOffset_succ_le_add_natAbs (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m (n + 1) ≤ discOffset f d m n + Int.natAbs (f ((m + n + 1) * d)) := by
  unfold discOffset
  -- one-step extension, then triangle inequality
  calc
    Int.natAbs (apSumOffset f d m (n + 1))
        = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
          simp [apSumOffset_succ, Nat.add_assoc, Nat.add_left_comm]
    _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
          simpa using
            (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))

/-- (Track B checklist item) `discOffset` grows by at most `1` when you extend the length by one,
for sign sequences.

This is the `ℕ`-valued wrapper form of `IsSignSequence.natAbs_apSumOffset_succ_le`. -/
lemma IsSignSequence.discOffset_succ_le {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m n : ℕ) :
    discOffset f d m (n + 1) ≤ discOffset f d m n + 1 := by
  -- unfold the definition and reuse the `Int.natAbs` lemma
  unfold discOffset
  simpa using (hf.natAbs_apSumOffset_succ_le (d := d) (m := m) (n := n))

/-- (Track B checklist item) `discOffset` also decreases by at most `1` when you extend the length
by one, for sign sequences.

Together with `IsSignSequence.discOffset_succ_le`, this gives the symmetric Lipschitz-by-1 bound
in the length parameter.
-/
lemma IsSignSequence.discOffset_le_succ_add_one {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m n : ℕ) :
    discOffset f d m n ≤ discOffset f d m (n + 1) + 1 := by
  -- Reduce to the underlying `Int.natAbs` statement.
  unfold discOffset
  -- Rewrite `S(n)` as `S(n+1) + (- nextTerm)`.
  have hs : apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) :=
    apSumOffset_succ (f := f) (d := d) (m := m) (n := n)
  have hrewrite :
      apSumOffset f d m n = apSumOffset f d m (n + 1) + (-f ((m + n + 1) * d)) := by
    -- Subtract the next term from both sides of `hs`.
    have := congrArg (fun x => x - f ((m + n + 1) * d)) hs
    -- `(S n + t) - t = S n`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
  -- Triangle inequality.
  calc
    Int.natAbs (apSumOffset f d m n)
        = Int.natAbs (apSumOffset f d m (n + 1) + (-f ((m + n + 1) * d))) := by
          simpa [hrewrite]
    _ ≤ Int.natAbs (apSumOffset f d m (n + 1)) + Int.natAbs (-f ((m + n + 1) * d)) := by
          simpa using
            (Int.natAbs_add_le (apSumOffset f d m (n + 1)) (-f ((m + n + 1) * d)))
    _ = Int.natAbs (apSumOffset f d m (n + 1)) + 1 := by
          simp [IsSignSequence.natAbs_eq_one (hf := hf)]

/-- (Track B checklist item) Convenience wrapper: Lipschitz-by-1 over `Nat` increments.

This packages repeated uses of `IsSignSequence.discOffset_le_succ_add_one` into the common form

`discOffset f d m n ≤ discOffset f d m (n + k) + k`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` monotone-in-length wrapper.
-/
lemma IsSignSequence.discOffset_le_add {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m n k : ℕ) :
    discOffset f d m n ≤ discOffset f d m (n + k) + k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Step: bound `discOffset … (n+k)` by `discOffset … (n+k+1) + 1`.
      have hstep : discOffset f d m (n + k) ≤ discOffset f d m (n + k + 1) + 1 := by
        simpa [Nat.add_assoc] using
          (IsSignSequence.discOffset_le_succ_add_one (f := f) (hf := hf) (d := d) (m := m)
            (n := n + k))
      -- Add `k` to both sides, then combine with the induction hypothesis.
      have hstep' : discOffset f d m (n + k) + k ≤ discOffset f d m (n + k + 1) + 1 + k :=
        Nat.add_le_add_right hstep k
      have : discOffset f d m n ≤ discOffset f d m (n + k + 1) + (k + 1) := by
        refine le_trans ih ?_
        -- Rearrange the RHS into the desired `+ (k+1)` form.
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep'
      -- Rewrite `n + (k+1)`.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

/-! ### Homogeneous `disc` one-step (stability) lemmas -/

/-- (Track B checklist item) Canonical one-step inequality for `disc`.

This is the homogeneous analogue of `discOffset_succ_le_add_natAbs`.
-/
lemma disc_succ_le_add_natAbs (f : ℕ → ℤ) (d n : ℕ) :
    disc f d (n + 1) ≤ disc f d n + Int.natAbs (f ((n + 1) * d)) := by
  classical
  unfold disc
  have hsucc : apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
    -- `Finset.range (n+1)` is `insert n (range n)`
    simp [apSum, Finset.range_add_one, Finset.sum_insert]
    -- remaining goal is just commutativity
    simp [add_comm]
  -- one-step extension, then triangle inequality
  calc
    Int.natAbs (apSum f d (n + 1))
        = Int.natAbs (apSum f d n + f ((n + 1) * d)) := by
          simpa [hsucc]
    _ ≤ Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) := by
          simpa using (Int.natAbs_add_le (apSum f d n) (f ((n + 1) * d)))

/-- (Track B checklist item) `disc` grows by at most `1` when you extend the length by one,
for sign sequences.

This is the homogeneous analogue of `IsSignSequence.discOffset_succ_le`.
-/
lemma IsSignSequence.disc_succ_le {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d n : ℕ) :
    disc f d (n + 1) ≤ disc f d n + 1 := by
  -- reduce to the general `Int.natAbs` form and rewrite the next term as `1`
  simpa [IsSignSequence.natAbs_eq_one (hf := hf)] using
    (disc_succ_le_add_natAbs (f := f) (d := d) (n := n))

lemma apSum_eq_apSumOffset (f : ℕ → ℤ) (d n : ℕ) : apSum f d n = apSumOffset f d 0 n := by
  unfold apSum apSumOffset
  simp

/- (deprecated aliases for `apSumOffset_zero_start` live in `MoltResearch.Discrepancy.Deprecated`). -/

/-- Normal form (“step-one”): express a homogeneous AP sum as an `apSum` with step size `1`
by bundling the step size `d` into the summand.

This is the homogeneous analogue of `apSumOffset_eq_apSum_step_one` and
`apSumFrom_eq_apSum_step_one`.
-/
lemma apSum_eq_apSum_step_one (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  unfold apSum
  simp

-- (deprecated alias `apSum_step_one_eq_apSum` moved to `MoltResearch.Discrepancy.Deprecated`)

/-! ### Normal forms for shifts (step-one presentation) -/

/-!
## Normalization of nested shifts

We frequently encounter functions of the form `fun k => f (k + a + b)`.
For a tidy normal form we prefer the addition to be grouped as `k + (a + b)`.

This is a tiny `[simp]` rule that rewrites the former into the latter without introducing a simp loop.
Only associativity is used, so the orientation is safe.
-/

@[simp] lemma fun_shift_add_assoc {α : Type*} (f : ℕ → α) (a b : ℕ) :
  (fun k => f (k + a + b)) = fun k => f (k + (a + b)) := by
  funext k
  simp [Nat.add_assoc]


/-- Normal form: shifting the index in the step-one presentation corresponds to `apSumOffset`.

This is the key rewrite used when we first normalize `apSum f d n` into the step-one form
`apSum (fun k => f (k*d)) 1 n`, then want to skip an initial segment.
-/
lemma apSum_step_one_shift_eq_apSumOffset (f : ℕ → ℤ) (d a n : ℕ) :
    apSum (fun k => f ((k + a) * d)) 1 n = apSumOffset f d a n := by
  unfold apSum apSumOffset
  simp [Nat.add_assoc, Nat.add_comm]

/-- The corresponding `discrepancy` normal form. -/
@[simp] lemma discrepancy_step_one_shift (f : ℕ → ℤ) (d a n : ℕ) :
    discrepancy (fun k => f ((k + a) * d)) 1 n = Int.natAbs (apSumOffset f d a n) := by
  unfold discrepancy
  simp [apSum_step_one_shift_eq_apSumOffset]

lemma apSum_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  classical
  -- `Finset.range (n+1)` is `insert n (range n)`
  simp [apSum, Finset.range_add_one, Finset.sum_insert]
  -- remaining goal is just commutativity
  simp [add_comm]

@[simp] lemma apSum_two (f : ℕ → ℤ) (d : ℕ) : apSum f d 2 = f d + f (2 * d) := by
  simpa [apSum_one] using (apSum_succ (f := f) (d := d) (n := 1))

/-- Split `apSum` over a sum of lengths: `apSum f d (m + n)` equals the sum over the first `m`
terms plus the sum over the next `n` terms. -/
lemma apSum_add_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) = apSum f d m + apSumOffset f d m n := by
  classical
  unfold apSum apSumOffset
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (fun i => f ((i + 1) * d)) m n)

/-- Alias of `apSum_add_length` with the more symmetric “`n₁`/`n₂`” naming. -/
lemma apSum_add_len (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    apSum f d (n₁ + n₂) = apSum f d n₁ + apSumOffset f d n₁ n₂ := by
  simpa using (apSum_add_length (f := f) (d := d) (m := n₁) (n := n₂))

/-- `simp`-friendly corollary of `apSum_add_len` for `n₁ = 0`. -/
@[simp] lemma apSum_add_len_zero_left (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (0 + n) = apSum f d n := by
  simpa [apSum_add_len] using
    (apSum_add_len (f := f) (d := d) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSum_add_len` for `n₂ = 0`. -/
@[simp] lemma apSum_add_len_zero_right (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 0) = apSum f d n := by
  simpa [apSum_add_len] using
    (apSum_add_len (f := f) (d := d) (n₁ := n) (n₂ := 0))

/-- `simp`-friendly corollary of `apSum_add_length` for `m = 0`. -/
@[simp] lemma apSum_add_length_zero_left (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (0 + n) = apSum f d n := by
  simpa [apSum_add_length] using (apSum_add_length (f := f) (d := d) (m := 0) (n := n))

/-- `simp`-friendly corollary of `apSum_add_length` for `n = 0`. -/
@[simp] lemma apSum_add_length_zero_right (f : ℕ → ℤ) (d m : ℕ) :
    apSum f d (m + 0) = apSum f d m := by
  simpa [apSum_add_length] using (apSum_add_length (f := f) (d := d) (m := m) (n := 0))

/-- First-term decomposition for a homogeneous AP sum.

This is a convenient “head + tail” normal form, pairing the first term `f d` with an offset sum.
Compare `apSumOffset_succ_length` for the analogous lemma on `apSumOffset`.
-/
lemma apSum_succ_length (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = f d + apSumOffset f d 1 n := by
  -- rewrite using the length-splitting lemma at `m = 1`
  have h := apSum_add_length (f := f) (d := d) (m := 1) (n := n)
  -- normalize `1 + n` to `n + 1` and `apSum f d 1` to `f d`
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

-- (See `MoltResearch/Discrepancy/Offset.lean` for `apSumOffset_eq_sub` and related lemmas.)

/-- Split an offset AP sum over a sum of lengths. -/
lemma apSumOffset_add_length (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  classical
  unfold apSumOffset
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (fun i => f ((m + i + 1) * d)) n₁ n₂)

/-- `simp`-friendly corollary of `apSumOffset_add_length` for `n₁ = 0`. -/
@[simp] lemma apSumOffset_add_length_zero_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (0 + n) = apSumOffset f d m n := by
  simpa [apSumOffset_add_length] using
    (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSumOffset_add_length` for `n₂ = 0`. -/
@[simp] lemma apSumOffset_add_length_zero_right (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 0) = apSumOffset f d m n := by
  simpa [apSumOffset_add_length] using
    (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n) (n₂ := 0))

/-- Triangle inequality API for splitting an offset AP sum by length. -/
lemma natAbs_apSumOffset_add_length_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    Int.natAbs (apSumOffset f d m (n₁ + n₂)) ≤
      Int.natAbs (apSumOffset f d m n₁) + Int.natAbs (apSumOffset f d (m + n₁) n₂) := by
  -- Normalize the LHS to a sum of two offset sums, then apply `natAbs_add_le`.
  simpa [apSumOffset_add_length] using
    (Int.natAbs_add_le (apSumOffset f d m n₁) (apSumOffset f d (m + n₁) n₂))

/-- Triangle inequality API for splitting `discOffset` by length.

This is a wrapper around `natAbs_apSumOffset_add_length_le`, using the `discOffset` simp bridge.
-/
lemma discOffset_add_length_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d m (n₁ + n₂) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  simpa using
    (natAbs_apSumOffset_add_length_le (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-!
### Boundedness transfer for `discOffsetUpTo`

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Boundedness transfer lemma (discOffsetUpTo)”.

The key point: for a sign sequence, extending the cutoff by `K` increases the max discrepancy by at
most `K` (Lipschitz-by-1).
-/

/-- Boundedness transfer for `discOffsetUpTo`: extending the cutoff by `K` increases the maximum by
at most `K`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Boundedness transfer lemma (discOffsetUpTo)”.
-/
lemma discOffsetUpTo_add_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m N K : ℕ) :
    discOffsetUpTo f d m (N + K) ≤ discOffsetUpTo f d m N + K := by
  classical
  unfold discOffsetUpTo
  refine Finset.sup_le ?_
  intro n hn
  have hnlt : n < N + K + 1 := Finset.mem_range.1 hn
  have hnle : n ≤ N + K := Nat.le_of_lt_succ hnlt
  by_cases h' : n ≤ N
  · -- If `n ≤ N`, it is already bounded by the `UpTo N` maximum.
    have hdisc : discOffset f d m n ≤ discOffsetUpTo f d m N :=
      discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := n) (N := N) h'
    exact le_trans hdisc (Nat.le_add_right _ _)
  · -- Otherwise write `n = N + t` and use triangle inequality + the length bound.
    have hN : N ≤ n := Nat.le_of_not_ge h'
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hN
    have ht : t ≤ K := by
      -- cancel `N` from `N + t ≤ N + K`.
      exact Nat.le_of_add_le_add_left hnle
    have hsplit := discOffset_add_length_le (f := f) (d := d) (m := m) (n₁ := N) (n₂ := t)
    have h1 : discOffset f d m N ≤ discOffsetUpTo f d m N :=
      discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := N) (N := N) (le_rfl)
    have h2 : discOffset f d (m + N) t ≤ t :=
      discOffset_le (f := f) (hf := hf) (d := d) (m := m + N) (n := t)
    have hNt : discOffset f d m (N + t) ≤ discOffsetUpTo f d m N + t := by
      exact le_trans hsplit (Nat.add_le_add h1 h2)
    exact le_trans hNt (Nat.add_le_add_left ht _)


/-- Lipschitz-by-1 in the cutoff parameter: extending from `N` to `N+1` increases the maximum by at
most `1` (for sign sequences).

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` Lipschitz-by-1 in `N`
(forward inequality direction).
-/
lemma discOffsetUpTo_succ_le_add_one {f : ℕ → ℤ} (hf : IsSignSequence f) (d m N : ℕ) :
    discOffsetUpTo f d m (N + 1) ≤ discOffsetUpTo f d m N + 1 := by
  simpa using (discOffsetUpTo_add_le (f := f) (hf := hf) (d := d) (m := m) (N := N) (K := 1))


/-- Concatenation inequality for `discOffsetUpTo`: extending the cutoff from `N` to `N + K` is
controlled by the max up to `N`, plus the max discrepancy on a tail segment of length `K`.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
"`discOffsetUpTo` concatenation inequality".
-/
lemma discOffsetUpTo_add_le_add_discOffsetUpTo {f : ℕ → ℤ} (d m N K : ℕ) :
    discOffsetUpTo f d m (N + K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m + N) K := by
  classical
  unfold discOffsetUpTo
  refine Finset.sup_le ?_
  intro n hn
  have hnlt : n < N + K + 1 := Finset.mem_range.1 hn
  have hnle : n ≤ N + K := Nat.le_of_lt_succ hnlt
  by_cases h' : n ≤ N
  · have hdisc : discOffset f d m n ≤ discOffsetUpTo f d m N :=
      discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := n) (N := N) h'
    -- pad with the nonnegative tail term
    exact le_trans hdisc (Nat.le_add_right _ _)
  · have hN : N ≤ n := Nat.le_of_not_ge h'
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hN
    have ht : t ≤ K := by
      -- cancel `N` from `N + t ≤ N + K`.
      exact Nat.le_of_add_le_add_left hnle
    have hsplit := discOffset_add_length_le (f := f) (d := d) (m := m) (n₁ := N) (n₂ := t)
    have h1 : discOffset f d m N ≤ discOffsetUpTo f d m N :=
      discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m) (n := N) (N := N) (le_rfl)
    have h2 : discOffset f d (m + N) t ≤ discOffsetUpTo f d (m + N) K := by
      exact discOffset_le_discOffsetUpTo (f := f) (d := d) (m := m + N) (n := t) (N := K) ht
    have hNt : discOffset f d m (N + t) ≤
        discOffsetUpTo f d m N + discOffsetUpTo f d (m + N) K := by
      exact le_trans hsplit (Nat.add_le_add h1 h2)
    simpa [Nat.add_assoc] using hNt


/-- Tail concatenation inequality for `discOffsetUpTo` (bookkeeping-friendly wrapper).

This is a max-level analogue of `discOffset_add_le`, expressed so later arguments can split an
initial segment of length `N` from a tail segment of length `K` without manual `Nat` algebra.

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`discOffsetUpTo` tail concatenation inequality.
-/
lemma discOffsetUpTo_tail_concat_le {f : ℕ → ℤ} (d m N K : ℕ) :
    discOffsetUpTo f d m (N + K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m + N) K := by
  simpa using
    (discOffsetUpTo_add_le_add_discOffsetUpTo (f := f) (d := d) (m := m) (N := N) (K := K))


/-- Triangle inequality API for splitting a homogeneous AP sum by length. -/
lemma natAbs_apSum_add_length_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    Int.natAbs (apSum f d (n₁ + n₂)) ≤
      Int.natAbs (apSum f d n₁) + Int.natAbs (apSumOffset f d n₁ n₂) := by
  -- `apSum_add_length` (with `m = n₁`) is the canonical length-splitting normal form.
  simpa [apSum_add_length] using
    (Int.natAbs_add_le (apSum f d n₁) (apSumOffset f d n₁ n₂))

/-- Triangle inequality API for splitting `disc` by length.

This is the homogeneous analogue of `discOffset_add_length_le`.
-/
lemma disc_add_length_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    disc f d (n₁ + n₂) ≤ disc f d n₁ + discOffset f d n₁ n₂ := by
  simpa using (natAbs_apSum_add_length_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))

-- Algebraic properties of `apSum`
lemma apSum_add (f g : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f k + g k) d n = apSum f d n + apSum g d n := by
  classical
  unfold apSum
  simp [Finset.sum_add_distrib]

@[simp] lemma apSum_neg (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => - f k) d n = - apSum f d n := by
  classical
  unfold apSum
  simp [Finset.sum_neg_distrib]

/-- `discrepancy` is invariant under pointwise negation. -/
@[simp] lemma discrepancy_neg (f : ℕ → ℤ) (d n : ℕ) :
    discrepancy (fun k => -f k) d n = discrepancy f d n := by
  unfold discrepancy
  simp [apSum_neg]

/-- `disc` is invariant under pointwise negation. -/
@[simp] lemma disc_neg (f : ℕ → ℤ) (d n : ℕ) :
    disc (fun k => -f k) d n = disc f d n := by
  unfold disc
  simp [apSum_neg]

/-- `discAlong` is invariant under pointwise negation.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Negation invariance (disc-level).
-/
@[simp] lemma discAlong_neg (f : ℕ → ℤ) (d n : ℕ) :
    discAlong (fun k => -f k) d n = discAlong f d n := by
  -- Reduce to the homogeneous wrapper `discrepancy`.
  simp [discAlong_eq_discrepancy]

lemma apSum_sub (f g : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f k - g k) d n = apSum f d n - apSum g d n := by
  classical
  unfold apSum
  simp [Finset.sum_sub_distrib]

/-- Multiplication by a fixed integer on the left commutes with `apSum`. -/
@[simp] lemma apSum_mul_left (c : ℤ) (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => c * f k) d n = c * apSum f d n := by
  classical
  unfold apSum
  simp [Finset.mul_sum]

/-- Multiplication by a fixed integer on the right commutes with `apSum`. -/
@[simp] lemma apSum_mul_right (f : ℕ → ℤ) (c : ℤ) (d n : ℕ) :
    apSum (fun k => f k * c) d n = apSum f d n * c := by
  classical
  unfold apSum
  simp [Finset.sum_mul]

/-- A sign sequence has AP partial sums bounded by length: `|∑_{i=1}^n f (i*d)| ≤ n`.

This is the basic triangle-inequality estimate used to show discrepancy is at most linear.
-/
lemma IsSignSequence.natAbs_apSum_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n := by
  induction n with
  | zero =>
      simp [apSum]
  | succ n ih =>
      -- triangle inequality, plus `Int.natAbs (f _) = 1`
      calc
        Int.natAbs (apSum f d (n + 1))
            = Int.natAbs (apSum f d n + f ((n + 1) * d)) := by
                simp [apSum_succ]
        _ ≤ Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) :=
              Int.natAbs_add_le _ _
        _ = Int.natAbs (apSum f d n) + 1 := by
              simp [IsSignSequence.natAbs_eq_one (hf := hf)]
        _ ≤ n + 1 := by
              simpa using Nat.add_le_add_right ih 1

/-- `discrepancy` is invariant under pointwise negation (as a method on `IsSignSequence`). -/
lemma IsSignSequence.discrepancy_neg {f : ℕ → ℤ} (_hf : IsSignSequence f) (d n : ℕ) :
    discrepancy (fun k => -f k) d n = discrepancy f d n := by
  simpa using (_root_.MoltResearch.discrepancy_neg (f := f) (d := d) (n := n))

/-- Normal form for discrepancy after shifting by `a*d` (as a method on `IsSignSequence`). -/
lemma IsSignSequence.discrepancy_shift_mul {f : ℕ → ℤ} (_hf : IsSignSequence f)
    (a d n : ℕ) :
    discrepancy (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n) := by
  simpa using (_root_.MoltResearch.discrepancy_shift_mul (f := f) (a := a) (d := d) (n := n))

/-- For a sign sequence, a discrepancy witness at level `C` forces a length `n > C`
(and can be chosen with step `d ≥ 1`). -/
lemma IsSignSequence.exists_witness_d_ge_one_and_length_gt {f : ℕ → ℤ} (hf : IsSignSequence f)
    {C : ℕ} (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n > C ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  refine ⟨d, n, Nat.succ_le_of_lt hd, ?_, hgt⟩
  have hle : Int.natAbs (apSum f d n) ≤ n :=
    IsSignSequence.natAbs_apSum_le (hf := hf) (d := d) (n := n)
  exact lt_of_lt_of_le hgt hle

lemma IsSignSequence.neg {f : ℕ → ℤ} (hf : IsSignSequence f) :
    IsSignSequence (fun n => - f n) := by
  intro n
  rcases hf n with h | h
  · right
    simp [h]
  · left
    simp [h]

lemma HasDiscrepancyAtLeast.neg_iff {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast (fun n => - f n) C ↔ HasDiscrepancyAtLeast f C := by
  unfold HasDiscrepancyAtLeast
  constructor
  · rintro ⟨d, n, hd, h⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_neg] using h
  · rintro ⟨d, n, hd, h⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_neg] using h

lemma IsSignSequence.exists_length_gt_of_hasDiscrepancyAtLeast {f : ℕ → ℤ}
    (hf : IsSignSequence f) {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d > 0 ∧ n > C := by
  rcases h with ⟨d, n, hd, hn⟩
  have hle := IsSignSequence.natAbs_apSum_le (hf := hf) d n
  have hC : C < n := by
    have : C < Int.natAbs (apSum f d n) := hn
    exact lt_of_lt_of_le this hle
  exact ⟨d, n, hd, hC⟩

@[simp] lemma apSum_zero_d (f : ℕ → ℤ) (n : ℕ) : apSum f 0 n = n • f 0 := by
  classical
  -- along step size 0, the AP is constant at 0
  simp [apSum]

@[simp] lemma apSumOffset_zero_d (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 0 m n = n • f 0 := by
  classical
  unfold apSumOffset
  simp

end MoltResearch
