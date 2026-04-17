import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: affine arithmetic progression sums

This file introduces the **nucleus** definition `apSumFrom` for affine arithmetic progressions
and a small directed API of normal-form lemmas.

Normal-form philosophy (Track B):
- Prefer `apSumFrom f a d n` as the canonical object for sums along `a + d, a + 2d, …, a + nd`.
- Rewrite to paper notation (`Finset.Icc`) only at the boundary of a statement.
- When you want to view an affine AP sum as a translated homogeneous AP sum, rewrite via
  `apSumFrom_eq_apSum_shift_add` (or the `_left` / constant-on-the-left variant `apSumFrom_eq_apSum_shift_add_left`).
  (The older `*_map_add` names are deprecated wrappers.)
-/

namespace MoltResearch

/-- Sum of `f` along the arithmetic progression `a + d, a + 2d, …, a + nd`. -/
def apSumFrom (f : ℕ → ℤ) (a d n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f (a + (i + 1) * d))

/-! ### Discrepancy wrapper for affine AP sums (`apSumFrom`) -/

/-- Affine discrepancy wrapper: `discFrom f a d n = |apSumFrom f a d n|`.

This is the affine analogue of `disc` / `discOffset`.
-/
def discFrom (f : ℕ → ℤ) (a d n : ℕ) : ℕ :=
  Int.natAbs (apSumFrom f a d n)

/-- Definitional lemma exposing the definition. -/
lemma discFrom_eq_natAbs_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    discFrom f a d n = Int.natAbs (apSumFrom f a d n) :=
  rfl

/-- `simp` bridge: `Int.natAbs (apSumFrom …)` simplifies to the `discFrom` wrapper.

This direction avoids simp loops with `discFrom_eq_natAbs_apSumFrom`.
-/
@[simp] lemma natAbs_apSumFrom_eq_discFrom (f : ℕ → ℤ) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) = discFrom f a d n :=
  rfl

/-- Coherence: `a = 0` recovers the homogeneous wrapper `disc`. -/
lemma discFrom_zero_start (f : ℕ → ℤ) (d n : ℕ) : discFrom f 0 d n = disc f d n := by
  -- unfold both wrappers and discharge the `0 + …` normalisation.
  simp [discFrom, disc, apSumFrom, apSum]

/-!
### Multiplicative dilation normal forms (affine nucleus)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.

Affine version: dilating indices by `q` scales both the start `a` and the step `d`.
We provide both `mul_right` and `mul_left` variants to avoid commutativity noise.
-/

/-- Multiplicative dilation normal form for affine AP sums (`mul_right` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.
-/
lemma apSumFrom_map_mul_right (f : ℕ → ℤ) (q a d n : ℕ) :
    apSumFrom (fun k => f (k * q)) a d n = apSumFrom f (a * q) (d * q) n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `(a + (i+1)*d) * q = a*q + (i+1)*(d*q)`.
  simp [Nat.add_mul, Nat.mul_assoc]

/-- Multiplicative dilation normal form for affine AP sums (`mul_left` summand convention).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Multiplicative dilation normal form.
-/
lemma apSumFrom_map_mul_left (f : ℕ → ℤ) (q a d n : ℕ) :
    apSumFrom (fun k => f (q * k)) a d n = apSumFrom f (q * a) (q * d) n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `q*(a + (i+1)*d) = q*a + (i+1)*(q*d)`.
  simp [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]

/-! ### `d = 1` simp-friendly normal forms (range-shift)

These are small convenience wrappers for rewriting affine AP sums with step size `1` into a plain
`Finset.range` sum, avoiding repeated `Nat.mul_one` / reassociation under binders.

We provide both a translation-friendly binder form `i ↦ f (i + const)` and a constant-on-the-left
variant.
-/

-- simp-friendly normal-form lemma for `d = 1`
@[simp] lemma apSumFrom_one_d_range (f : ℕ → ℤ) (a n : ℕ) :
    apSumFrom f a 1 n = (Finset.range n).sum (fun i => f (i + (a + 1))) := by
  unfold apSumFrom
  simp [Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma apSumFrom_one_d_range_add_left (f : ℕ → ℤ) (a n : ℕ) :
    apSumFrom f a 1 n = (Finset.range n).sum (fun i => f ((a + 1) + i)) := by
  simpa [Nat.add_comm] using (apSumFrom_one_d_range (f := f) (a := a) (n := n))

/-! ### Endpoint arithmetic normalisation lemmas

These lemmas help normalising the endpoint expressions that appear in `apSumFrom`-style
definitions.

We mark only the “forward” direction lemmas with `[simp]`, so `simp` can rewrite towards a
canonical form without causing rewrite loops.
-/

section NatEndpointNorm

/-- Normalise `a + d * (m+1)` to `a + (m+1) * d` (canonical affine endpoint form).

This matches the endpoint shape used by `apSumFrom` (`a + (i+1)*d`) and tends to reduce
binder-level commutativity noise in downstream rewrite pipelines.
-/
@[simp] lemma add_mul_succ_norm (a m d : ℕ) :
    a + d * (m + 1) = a + (m + 1) * d := by
  simp [Nat.mul_comm]

/-- Reverse direction of `add_mul_succ_norm` (not tagged `[simp]`). -/
lemma add_mul_succ_norm' (a m d : ℕ) :
    a + (m + 1) * d = a + d * (m + 1) := by
  simp [Nat.mul_comm]

/-- Normalise `a + (m+n) * d` to `a + m*d + n*d` (canonical form).

We do **not** tag this `[simp]` by default: it can be useful, but it is a powerful reassociation
rewrite that may increase simp search or cause recursion in downstream proofs.

If you explicitly want this as a simp rule, import `MoltResearch.Discrepancy.AffineEndpointSimp`.
-/
lemma add_mul_add_norm (a m n d : ℕ) :
    a + (m + n) * d = a + m * d + n * d := by
  -- Expand `(m+n)*d` and reassociate.
  simp [Nat.add_mul, Nat.add_assoc]

/-- Reverse direction of `add_mul_add_norm` (not tagged `[simp]`). -/
lemma add_mul_add_norm' (a m n d : ℕ) :
    a + m * d + n * d = a + (m + n) * d := by
  -- Compress back to `(m+n)*d`.
  calc
    a + m * d + n * d = a + (m * d + n * d) := by
      simp [Nat.add_assoc]
    _ = a + (m + n) * d := by
      simpa using congrArg (fun t => a + t) (Nat.add_mul m n d).symm

end NatEndpointNorm

/-! ### Bridge lemmas: `apSumOffset` vs `apSumFrom` -/

/-- Offset sum of a shifted sequence is an affine AP sum.

This is a convenient “two-way bridge” between the older offset nucleus
`apSumOffset` (homogeneous progression with a skipped prefix) and the Track B
preferred affine nucleus `apSumFrom`.

Concretely, the left-hand side expands to
`∑ i in range n, f (a + (m + i + 1) * d)`.
-/
lemma apSumOffset_shift_add_eq_apSumFrom_bridge (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun t => f (t + a)) d m n = apSumFrom f (a + m * d) d n := by
  unfold apSumOffset apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `((m+i+1)*d) + a = (a + m*d) + (i+1)*d`.
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul]

/-- Symmetric form of `apSumOffset_shift_add_eq_apSumFrom_bridge`. -/
lemma apSumFrom_eq_apSumOffset_shift_add_bridge (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumOffset (fun t => f (t + a)) d m n := by
  simpa [apSumOffset_shift_add_eq_apSumFrom_bridge] using
    (apSumOffset_shift_add_eq_apSumFrom_bridge (f := f) (a := a) (d := d) (m := m) (n := n)).symm

/-!
Direct normal-form wrappers.

These are intentionally lightweight lemmas that let you rewrite an affine AP sum whose start is
presented as a translated multiple `a + m*d` into an `apSumOffset` on the shifted function.

They avoid having to manually coax `simp` through intermediate arithmetic reassociations under
binders.
-/

/-- Normal form: rewrite `apSumFrom f (a + m*d) d n` as an offset AP sum on the shifted function
`k ↦ f (k + a)`. -/
lemma apSumFrom_add_mul_eq_apSumOffset_shift_add (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using (apSumFrom_eq_apSumOffset_shift_add_bridge (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Constant-on-the-left variant of `apSumFrom_add_mul_eq_apSumOffset_shift_add`. -/
lemma apSumFrom_add_mul_eq_apSumOffset_shift_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa [Nat.add_comm] using
    (apSumFrom_add_mul_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Mul-left-friendly variant of `apSumFrom_add_mul_eq_apSumOffset_shift_add` (i.e. with `a + d*m`). -/
lemma apSumFrom_add_mul_left_eq_apSumOffset_shift_add (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + d * m) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa [Nat.mul_comm] using
    (apSumFrom_add_mul_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Mul-left-friendly, constant-on-the-left variant of `apSumFrom_add_mul_eq_apSumOffset_shift_add_left`. -/
lemma apSumFrom_add_mul_left_eq_apSumOffset_shift_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + d * m) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa [Nat.mul_comm] using
    (apSumFrom_add_mul_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- `simp`-friendly variant of `apSumOffset_shift_add_eq_apSumFrom_bridge` under `Int.natAbs`.

This is useful after rewriting `discrepancy_def` / `affineDiscrepancy_def`, where goals often
contain `Int.natAbs (apSumOffset (fun t => f (t + a)) d m n)`.

We orient the rewrite towards the Track B nucleus `apSumFrom`.
-/
@[simp] lemma natAbs_apSumOffset_shift_add_eq_natAbs_apSumFrom_bridge (f : ℕ → ℤ) (a d m n : ℕ) :
    Int.natAbs (apSumOffset (fun t => f (t + a)) d m n) =
      Int.natAbs (apSumFrom f (a + m * d) d n) := by
  simpa [apSumOffset_shift_add_eq_apSumFrom_bridge]

/-! ### Congruence lemmas -/

/-- If two functions agree pointwise on the indices used in `apSumFrom`, then the affine AP sums are equal. -/
lemma apSumFrom_congr (f g : ℕ → ℤ) (a d n : ℕ)
    (h : ∀ i, i < n → f (a + (i + 1) * d) = g (a + (i + 1) * d)) :
    apSumFrom f a d n = apSumFrom g a d n := by
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact h i hi'

/-- Translation-invariance wrapper: if `f` and `g` agree pointwise on the affine tail
`a + i*d` up to length `n`, then the affine AP sums agree.

This packages the common hypothesis form `∀ i ≤ n, f (a + i*d) = g (a + i*d)` without requiring
manual `Finset.range` bookkeeping.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Translation invariance wrappers.
-/
lemma apSumFrom_congr_le (f g : ℕ → ℤ) (a d n : ℕ)
    (h : ∀ i, i ≤ n → f (a + i * d) = g (a + i * d)) :
    apSumFrom f a d n = apSumFrom g a d n := by
  apply apSumFrom_congr (f := f) (g := g) (a := a) (d := d) (n := n)
  intro i hi
  -- `i < n` implies `i+1 ≤ n`.
  have hle : i + 1 ≤ n := Nat.succ_le_of_lt hi
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using
    (h (i + 1) hle)

/-- `congr` variant: if `P` holds on every *index* used in `apSumFrom`, and the summands agree
whenever `P i` holds, then the affine AP sums are equal.

This is convenient when you have a hypothesis stated on the summation range `i < n` (or
`i ∈ range n`) and want to apply it without rewriting the whole function.
-/
lemma apSumFrom_congrOn (f g : ℕ → ℤ) (P : ℕ → Prop) (a d n : ℕ)
    (hP : ∀ i, i < n → P i)
    (hfg : ∀ i, P i → f (a + (i + 1) * d) = g (a + (i + 1) * d)) :
    apSumFrom f a d n = apSumFrom g a d n := by
  apply apSumFrom_congr (f := f) (g := g) (a := a) (d := d) (n := n)
  intro i hi
  exact hfg i (hP i hi)

/-- Value-predicate variant of `apSumFrom_congrOn`: if `P` holds on every value used in
`apSumFrom`, and `f = g` on `P`, then the affine AP sums are equal.

This is convenient when you have an ambient hypothesis like `∀ x, P x → f x = g x`.
-/
lemma apSumFrom_congrOn_val (f g : ℕ → ℤ) (P : ℕ → Prop) (a d n : ℕ)
    (hP : ∀ i, i < n → P (a + (i + 1) * d))
    (hfg : ∀ x, P x → f x = g x) :
    apSumFrom f a d n = apSumFrom g a d n := by
  apply apSumFrom_congr (f := f) (g := g) (a := a) (d := d) (n := n)
  intro i hi
  exact hfg _ (hP i hi)

/-! ### Normal-form lemmas relating homogeneous and affine AP sums -/

/-- Shifting the sequence by `a` turns a homogeneous AP sum into an affine AP sum. -/
lemma apSum_shift_add_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSum (fun k => f (k + a)) d n = apSumFrom f a d n := by
  unfold apSum apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `((i+1)*d) + a = a + (i+1)*d`.
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Corresponding discrepancy normal form: a shift by `a` is the `natAbs` of an affine AP sum.

Marked `[simp]` since it is a one-way expansion of `discrepancy` into a `natAbs` normal form.
-/
@[simp] lemma discrepancy_shift_add_eq_natAbs_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    discrepancy (fun k => f (k + a)) d n = Int.natAbs (apSumFrom f a d n) := by
  unfold discrepancy
  simpa [apSum_shift_add_eq_apSumFrom]

/-- `simp`-friendly variant of `apSum_shift_add_eq_apSumFrom` under `Int.natAbs`.

This is useful after rewriting `discrepancy_def` / `affineDiscrepancy_def`, where goals often
contain `Int.natAbs (apSum (fun k => f (k + a)) d n)` or `Int.natAbs (apSumFrom f a d n)`.
-/
@[simp] lemma natAbs_apSum_shift_add_eq_natAbs_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    Int.natAbs (apSum (fun k => f (k + a)) d n) = Int.natAbs (apSumFrom f a d n) := by
  simpa [apSum_shift_add_eq_apSumFrom]

/-! ### Triangle-inequality API for affine AP sums -/

/-- `apSumFrom` splits over addition of lengths. -/
lemma apSumFrom_add_len (f : ℕ → ℤ) (a d n₁ n₂ : ℕ) :
    apSumFrom f a d (n₁ + n₂) =
      apSumFrom f a d n₁ + apSumFrom f (a + n₁ * d) d n₂ := by
  unfold apSumFrom
  -- Split `range (n₁ + n₂)` into `range n₁` and a shifted `range n₂`.
  -- Then simplify the shifted index arithmetic.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add, Nat.add_mul] using
    (Finset.sum_range_add (f := fun i => f (a + (i + 1) * d)) n₁ n₂)

/-- `simp`-friendly corollary of `apSumFrom_add_len` for `n₁ = 0`. -/
@[simp] lemma apSumFrom_add_len_zero_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d (0 + n) = apSumFrom f a d n := by
  simpa [apSumFrom_add_len] using
    (apSumFrom_add_len (f := f) (a := a) (d := d) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSumFrom_add_len` for `n₂ = 0`. -/
@[simp] lemma apSumFrom_add_len_zero_right (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d (n + 0) = apSumFrom f a d n := by
  simpa [apSumFrom_add_len] using
    (apSumFrom_add_len (f := f) (a := a) (d := d) (n₁ := n) (n₂ := 0))

/-- Triangle inequality for concatenating two affine AP sums. -/
lemma natAbs_apSumFrom_add_len_le (f : ℕ → ℤ) (a d n₁ n₂ : ℕ) :
    Int.natAbs (apSumFrom f a d (n₁ + n₂)) ≤
      Int.natAbs (apSumFrom f a d n₁) + Int.natAbs (apSumFrom f (a + n₁ * d) d n₂) := by
  simpa [apSumFrom_add_len] using
    (Int.natAbs_add_le (apSumFrom f a d n₁) (apSumFrom f (a + n₁ * d) d n₂))

/-! ### Degenerate length simp lemmas

These mirror `apSum_zero` / `apSum_one` for the affine nucleus `apSumFrom`.
-/
section apSumFrom_degenerate

@[simp] lemma apSumFrom_zero (f : ℕ → ℤ) (a d : ℕ) :
  apSumFrom f a d 0 = 0 := by
  unfold apSumFrom
  simp

@[simp] lemma apSumFrom_one (f : ℕ → ℤ) (a d : ℕ) :
  apSumFrom f a d 1 = f (a + d) := by
  unfold apSumFrom
  simp

end apSumFrom_degenerate

/-- Corner case: step size `d = 0` collapses the affine AP to the constant value `a`. -/
@[simp] lemma apSumFrom_zero_d (f : ℕ → ℤ) (a n : ℕ) :
    apSumFrom f a 0 n = n • f a := by
  classical
  simp [apSumFrom]

/-- Rewrite `apSumFrom` as the familiar interval sum `∑ i ∈ Icc 1 n, f (a + i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumFrom`, and
rewrite to this form only when matching paper notation.
-/
lemma apSumFrom_eq_sum_Icc (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
  classical
  unfold apSumFrom
  have h := (Finset.sum_Ico_eq_sum_range (f := fun i => f (a + i * d)) (m := 1) (n := n + 1))
  calc
    (Finset.range n).sum (fun i => f (a + (i + 1) * d))
        = (Finset.range n).sum (fun i => f (a + (1 + i) * d)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- `i + 1 = 1 + i`
            simp [Nat.add_comm]
    _ = (Finset.Ico 1 (n + 1)).sum (fun i => f (a + i * d)) := by
            -- `h` is oriented from `Ico` to `range`; we use it backwards.
            simpa [Nat.add_sub_cancel] using h.symm
    _ = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
            simp [Finset.Ico_add_one_right_eq_Icc]

/-- Translation-friendly paper notation: rewrite `apSumFrom` as
`∑ i ∈ Icc 1 n, f (i*d + a)`.

This variant avoids commuting an `a + …` under a binder in downstream proofs.
-/
lemma apSumFrom_eq_sum_Icc_add (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (i * d + a)) := by
  classical
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n))

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (i*d + a)` back to
`apSumFrom`.

This is the inverse orientation of `apSumFrom_eq_sum_Icc_add`.
-/
lemma sum_Icc_eq_apSumFrom_add (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_sum_Icc_add (f := f) (a := a) (d := d) (n := n)).symm

/-!
Note: deprecated `*_mul_left` paper-notation wrappers live in `MoltResearch.Discrepancy.Deprecated`.
The stable surface prefers the `i * d` convention (`apSumFrom_eq_sum_Icc` / `apSumFrom_eq_sum_Icc_add`).
-/


/-- Special case: step size `d = 1` turns `apSumFrom` into the plain interval sum
`∑ i ∈ Icc 1 n, f (a + i)`.

This is often a convenient normal form when the AP step is already normalized.
-/
lemma apSumFrom_one_d (f : ℕ → ℤ) (a n : ℕ) :
    apSumFrom f a 1 n = (Finset.Icc 1 n).sum (fun i => f (a + i)) := by
  simpa using (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := 1) (n := n))

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (a + i*d)` back to
`apSumFrom`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)).symm

-- (moved below: depends on `apSumFrom_eq_apSumOffset_step_one`)

lemma apSumFrom_succ (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d (n + 1) = apSumFrom f a d n + f (a + (n + 1) * d) := by
  unfold apSumFrom
  simpa [Finset.sum_range_succ] using
    (Finset.sum_range_succ (fun i => f (a + (i + 1) * d)) n)

lemma apSum_eq_apSumFrom (f : ℕ → ℤ) (d n : ℕ) :
  apSum f d n = apSumFrom f 0 d n := by
  unfold apSum apSumFrom
  simp [Nat.zero_add]


/-- Paper↔nucleus bridge specialized to `a = 0`.

This is a convenience lemma for writing surface statements uniformly in terms of `apSumFrom` while
still matching paper notation on `Finset.Icc`.

Naming note: this is about the *start* parameter, so it uses the `_zero_start` suffix (compare
`apSumFrom_zero` for the degenerate-length lemma `n = 0`).
-/
lemma apSumFrom_zero_start_eq_sum_Icc (f : ℕ → ℤ) (d n : ℕ) :
    apSumFrom f 0 d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  simpa using (apSumFrom_eq_sum_Icc (f := f) (a := 0) (d := d) (n := n))

lemma sum_Icc_eq_apSumFrom_zero_start (f : ℕ → ℤ) (d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSumFrom f 0 d n := by
  simpa using (apSumFrom_zero_start_eq_sum_Icc (f := f) (d := d) (n := n)).symm

/-- Normal form: eliminate the explicit start parameter `a` by shifting the underlying sequence.

This is useful when you want to reduce affine AP sums to the `a = 0` case while keeping the step
size `d` unchanged.

It is the affine analogue of rewriting a translated sum `∑ f (a + ·)` into a sum of the shifted
function `fun k => f (k + a)`.
-/
lemma apSumFrom_eq_apSumFrom_shift_add (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumFrom (fun k => f (k + a)) 0 d n := by
  classical
  unfold apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Normalize `a + (i+1)*d` into the translation-friendly form `(i+1)*d + a`.
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Inverse orientation of `apSumFrom_eq_apSumFrom_shift_add`.

This lemma is handy when you have already shifted the summand and want to normalize back to the
canonical `apSumFrom f a d n` form.
-/
lemma apSumFrom_shift_add_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom (fun k => f (k + a)) 0 d n = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_apSumFrom_shift_add (f := f) (a := a) (d := d) (n := n)).symm

/-- Add-left variant of `apSumFrom_eq_apSumFrom_shift_add`.

This is the same normal form, but with the shifted function written in the `a + k` convention
instead of `k + a`. Keeping both orientations avoids commuting addition under binders in
downstream proofs.
-/
lemma apSumFrom_eq_apSumFrom_shift_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumFrom (fun k => f (a + k)) 0 d n := by
  have hfun : (fun k => f (k + a)) = fun k => f (a + k) := by
    funext k
    simp [Nat.add_comm]
  simpa [hfun] using
    (apSumFrom_eq_apSumFrom_shift_add (f := f) (a := a) (d := d) (n := n))

/-- Inverse orientation of `apSumFrom_eq_apSumFrom_shift_add_left`. -/
lemma apSumFrom_shift_add_left_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom (fun k => f (a + k)) 0 d n = apSumFrom f a d n := by
  simpa using
    (apSumFrom_eq_apSumFrom_shift_add_left (f := f) (a := a) (d := d) (n := n)).symm

/-! ### Degenerate start simp lemmas

These mirror the “degenerate length” simp lemmas (`apSumFrom_zero` / `apSumFrom_one`) but for the
*start* parameter.
-/

/-- Normal form: an affine AP sum with start `a = 0` is just a homogeneous AP sum.

This is the inverse orientation of `apSum_eq_apSumFrom`.
-/
@[simp] lemma apSumFrom_zero_start (f : ℕ → ℤ) (d n : ℕ) :
    apSumFrom f 0 d n = apSum f d n := by
  simpa using (apSum_eq_apSumFrom (f := f) (d := d) (n := n)).symm

lemma apSumOffset_eq_apSumFrom (f : ℕ → ℤ) (d m n : ℕ) :
  apSumOffset f d m n = apSumFrom f (m * d) d n := by
  unfold apSumOffset apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  have h : (m + i + 1) * d = m * d + (i + 1) * d := by
    simpa [Nat.add_assoc] using (Nat.add_mul m (i + 1) d)
  simp [h]

/-- Normal form: an affine AP sum whose start is a multiple of the step size can be rewritten as an
offset AP sum.

This is the inverse orientation of `apSumOffset_eq_apSumFrom`.
-/
lemma apSumFrom_mul_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)).symm

/-!
Mul-left paper-notation helpers (e.g. `d * m` vs `m * d`) are *not* part of the stable surface.

They live in `MoltResearch.Discrepancy.Deprecated` as deprecated compatibility wrappers.
-/

/-- Convenience wrapper: if the affine start `a` is *definitionally* a multiple of `d`, rewrite
`apSumFrom f a d n` to an offset sum.

This is a small normal-form helper when your context already contains a fact `a = m * d`.
-/
lemma apSumFrom_eq_apSumOffset_of_eq_mul (f : ℕ → ℤ) {a d m n : ℕ} (ha : a = m * d) :
    apSumFrom f a d n = apSumOffset f d m n := by
  simpa [ha] using (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-!
Mul-left variant of `apSumFrom_eq_apSumOffset_of_eq_mul` (i.e. with a hypothesis `a = d * m`)
was removed from the stable surface.

Import `MoltResearch.Discrepancy.Deprecated` if you need it.
-/

/-- Convenience wrapper: if the affine start `a` is a multiple of `d`, rewrite `apSumFrom` to an
offset sum.

This lemma is intentionally existential: downstream goals often know only “`d ∣ a`” (or an
explicit witness `∃ m, a = m*d`) and want to normalize into an `apSumOffset` form.
-/
lemma apSumFrom_exists_eq_apSumOffset_of_exists_eq_mul (f : ℕ → ℤ) {a d n : ℕ}
    (h : ∃ m, a = m * d) :
    ∃ m, apSumFrom f a d n = apSumOffset f d m n := by
  rcases h with ⟨m, rfl⟩
  refine ⟨m, ?_⟩
  simpa using (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Convenience wrapper: if the affine start `a` is a multiple of `d` in the form `d ∣ a`, rewrite
`apSumFrom` to an offset sum.

This is a small normal-form helper when your context contains a divisibility hypothesis.
-/
lemma apSumFrom_exists_eq_apSumOffset_of_dvd (f : ℕ → ℤ) {a d n : ℕ} (h : d ∣ a) :
    ∃ m, apSumFrom f a d n = apSumOffset f d m n := by
  refine apSumFrom_exists_eq_apSumOffset_of_exists_eq_mul (f := f) (a := a) (d := d) (n := n) ?_
  rcases h with ⟨m, rfl⟩
  refine ⟨m, ?_⟩
  simp [Nat.mul_comm]

/-- Normal form: if the affine start `a` is a multiple of the step `d` (i.e. `d ∣ a`), rewrite
`apSumFrom f a d n` directly to an `apSumOffset` with the quotient `a / d`.

This is a convenient shortcut when you want a canonical `apSumOffset` normal form without going
through the existential wrapper `apSumFrom_exists_eq_apSumOffset_of_dvd`.
-/
lemma apSumFrom_eq_apSumOffset_of_dvd (f : ℕ → ℤ) {a d n : ℕ} (h : d ∣ a) :
    apSumFrom f a d n = apSumOffset f d (a / d) n := by
  rcases h with ⟨m, rfl⟩
  -- Now `a = d*m`.
  by_cases hd : d = 0
  · subst hd
    -- Here `a = 0*m = 0` and `0/0 = 0`, so both sides are the same constant AP sum.
    simp [apSumFrom, apSumOffset]
  · have hdpos : d > 0 := Nat.pos_of_ne_zero hd
    have hdiv : d * m / d = m := by
      -- Reduce to the standard `m*d / d = m` lemma.
      simpa [Nat.mul_comm] using (Nat.mul_div_left m hdpos)
    -- Reduce to the `a = d*m` normal form and compute the quotient.
    simpa [hdiv, Nat.mul_comm] using
      (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Shifted version of `apSumFrom`.

This views the affine AP sum as a homogeneous AP sum on the shifted function `k ↦ f (a + k)`.
-/
lemma apSumFrom_eq_apSum_shift_add_left (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  unfold apSumFrom apSum
  rfl


/-- Translation-friendly variant of `apSumFrom_eq_apSum_shift_add_left`.

This writes the shift as `k + a` rather than `a + k`.
-/
lemma apSumFrom_eq_apSum_shift_add (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d n = apSum (fun k => f (k + a)) d n := by
  simpa [Nat.add_comm] using
    (apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := n))



/-- Normal form: express an affine AP sum as a homogeneous sum with step size `1` by bundling the
step size `d` into the summand.

This is occasionally convenient when you want to reuse lemmas stated for `apSum` without first
rewriting to `apSumFrom_eq_apSum_shift`.
-/
lemma apSumFrom_eq_apSum_step_one (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSum (fun k => f (a + k * d)) 1 n := by
  unfold apSumFrom apSum
  simp

/-- Normal form (“step-one”, offset-sum view): express an affine AP sum as an `apSumOffset` with
step size `1` and zero offset.

This is a small wrapper around `apSumFrom_eq_apSum_step_one`. It is useful when you want to apply
lemmas stated for `apSumOffset` (e.g. tail/difference normal forms) without first going through an
`apSum` intermediate.
-/
lemma apSumFrom_eq_apSumOffset_step_one (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  -- `apSumOffset g 1 0 n` simp-normalizes to `apSum g 1 n`.
  simpa [apSumFrom_eq_apSum_step_one] using
    (apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n))

/-- Paper → nucleus → step-one (offset) normal form.

This composes the standard paper-notation rewrite `sum_Icc_eq_apSumFrom` with the affine step-one
normal form `apSumFrom_eq_apSumOffset_step_one`.

It is a convenient one-shot lemma when you want to normalize a paper affine sum directly into the
step-one offset nucleus.
-/
lemma sum_Icc_eq_apSumOffset_step_one (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  calc
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
      simpa using sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)
    _ = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
      simpa using apSumFrom_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n)

/-- Translation-friendly variant of `apSumFrom_eq_apSumOffset_step_one`.

This packages the summand as `k * d + a` rather than `a + k * d`.
-/
lemma apSumFrom_eq_apSumOffset_step_one_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa [Nat.add_comm] using
    (apSumFrom_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n))

/-- Translation-friendly variant of `apSumFrom_eq_apSum_step_one`.

This lemma packages the affine AP sum into step-one form where the summand is written as
`k * d + a` rather than `a + k * d`.

This is often the more convenient normal form when rewriting under `fun k => …` where the
offset `a` is syntactically on the right.
-/
lemma apSumFrom_eq_apSum_step_one_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa [Nat.add_comm] using
    (apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n))

-- (deprecated alias `apSum_step_one_eq_apSumFrom` moved to `MoltResearch.Discrepancy.Deprecated`)

/-- Tail version of `apSumFrom_eq_apSum_step_one`.

In “paper” notation, this rewrites
`∑_{i=1}^n f ((a + m*d) + i*d)`
into the step-one homogeneous sum
`∑_{k=1}^n f (a + (m+k)*d)`.
-/
lemma apSumFrom_tail_eq_apSum_step_one (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSum (fun k => f (a + (m + k) * d)) 1 n := by
  classical
  unfold apSumFrom apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `simp` (via `add_mul_succ_norm`) prefers the endpoint normal form `a + (i+1) * d`.
  have hmul : m * d + (i + 1) * d = (m + (i + 1)) * d := by
    simpa using (Nat.add_mul m (i + 1) d).symm
  -- `simp` also reduces `((i+1) * 1)`.
  simp [Nat.add_assoc, hmul]

/-- Tail version of `apSumFrom_eq_apSum_step_one`, but expressed as an `apSumOffset` with
`m = 0`.

This is convenient when your downstream normal form wants to uniformly work with tails
(`apSumOffset`) even after switching to step-one (`d = 1`).
-/
lemma apSumFrom_tail_eq_apSumOffset_step_one_zero_m (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n =
      apSumOffset (fun k => f (a + (m + k) * d)) 1 0 n := by
  calc
    apSumFrom f (a + m * d) d n = apSum (fun k => f (a + (m + k) * d)) 1 n := by
      simpa using apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (a + (m + k) * d)) 1 0 n := by
      simpa using
        (apSumOffset_zero_start (f := fun k => f (a + (m + k) * d)) (d := 1) (n := n)).symm

/-- Translation-friendly variant of `apSumFrom_tail_eq_apSum_step_one`.

This keeps the step-one homogeneous sum normal form, but writes the summand as
`k * d + (a + m * d)` rather than `a + (m + k) * d`.

This can be convenient when other rewrite lemmas (or `simp` normal forms) prefer `k*d + const`.
-/
lemma apSumFrom_tail_eq_apSum_step_one_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
  classical
  -- First normalize to the canonical tail step-one form.
  have h := apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)
  -- Then rewrite the summand into the `k*d + const` presentation.
  -- (Here `k` ranges over `1..n` inside `apSum _ 1 n`.)
  refine h.trans ?_
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Inside `apSum _ 1 n`, the summand is evaluated at `k = (i+1)`.
  -- We normalize `a + (m + (i+1)) * d` into `(i+1) * d + (a + m*d)`.
  have hadd : a + (m + (i + 1)) * d = (i + 1) * d + (a + m * d) := by
    calc
      a + (m + (i + 1)) * d = a + (m * d + (i + 1) * d) := by
        simpa using congrArg (fun t => a + t) (Nat.add_mul m (i + 1) d)
      _ = (i + 1) * d + (a + m * d) := by
        simp [Nat.add_assoc, Nat.add_comm]
  simp [hadd, Nat.add_assoc, Nat.add_comm]


/-- Translation-friendly variant of `apSumFrom_tail_eq_apSumOffset_step_one_zero_m`.

This is the `apSumFrom` analogue of `apSumOffset_eq_apSumOffset_step_one_zero_m_add_left`: it
pushes both the tail parameter `m` and the step size `d` into the summand *and* writes the summand
in the `k*d + const` normal form.
-/
lemma apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n =
      apSumOffset (fun k => f (k * d + (a + m * d))) 1 0 n := by
  calc
    apSumFrom f (a + m * d) d n = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
      simpa using
        apSumFrom_tail_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k * d + (a + m * d))) 1 0 n := by
      simpa using
        (apSumOffset_zero_start (f := fun k => f (k * d + (a + m * d))) (d := 1) (n := n)).symm

/-- Tail step-one normal form that *keeps* the tail parameter `m` in the offset nucleus API.

This is often the most convenient bridge when you want to work uniformly with `apSumOffset` tails
(and still package the step size `d` into the summand), without first forcing `m = 0`.

It presents the affine tail
`apSumFrom f (a + m*d) d n`
as the offset sum
`apSumOffset (fun k => f (k*d + a)) 1 m n`.
-/
lemma apSumFrom_tail_eq_apSumOffset_step_one_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k * d + a)) 1 m n := by
  classical
  unfold apSumFrom apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Compare the `i`th term on each side.
  -- LHS term: `f ((a + m*d) + (i+1)*d)`.
  -- RHS term: `f (((m+i+1)*1)*d + a)`.
  have hmul : m * d + (i + 1) * d = (m + (i + 1)) * d := by
    -- `Nat.add_mul` gives `(m + (i+1)) * d = m*d + (i+1)*d`.
    simpa using (Nat.add_mul m (i + 1) d).symm
  -- Now just normalize associativity/commutativity of `+` and `*`.
  calc
    f ((a + m * d) + (i + 1) * d)
        = f (a + (m * d + (i + 1) * d)) := by
            simp [Nat.add_assoc]
    _ = f (a + (m + (i + 1)) * d) := by
            simp [hmul]
    _ = f ((m + i + 1) * d + a) := by
            simp [Nat.add_assoc, Nat.add_comm]
    _ = f (((m + i + 1) * 1) * d + a) := by
            simp

/-- Convenience wrapper around `apSumFrom_tail_eq_apSumOffset_step_one_add_left` when the affine
start is written as `m*d + a`.

This avoids a manual commutativity rewrite at the call site.
-/
lemma apSumFrom_tail_eq_apSumOffset_step_one_add_left_start_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k * d + a)) 1 m n := by
  -- Commute the affine start into the `a + m*d` form and reuse the existing lemma.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumFrom_tail_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

/-- Tail step-one normal form that keeps the tail parameter `m` in the offset nucleus API,
with the summand written in the `a + k*d` form.

It presents the affine tail
`apSumFrom f (a + m*d) d n`
as the offset sum
`apSumOffset (fun k => f (a + k*d)) 1 m n`.

This is the `a + k*d` analogue of `apSumFrom_tail_eq_apSumOffset_step_one_add_left`.
-/
lemma apSumFrom_tail_eq_apSumOffset_step_one (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k * d)) 1 m n := by
  have h :=
    apSumFrom_tail_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)
  have hs : (fun k => f (k * d + a)) = (fun k => f (a + k * d)) := by
    funext k
    simpa using congrArg f (Nat.add_comm (k * d) a)
  simpa [hs] using h


/-- Two-way bridge between the affine nucleus `apSumFrom` (starting at `m*d`) and the step-one
offset nucleus `apSumOffset`.

This rewrites
`apSumFrom f (m*d) d n`
into
`apSumOffset (fun k => f (d*k)) 1 m n`.

It is essentially `apSumFrom_tail_eq_apSumOffset_step_one` specialized to `a = 0`, plus a
multiplication-commutation normalization in the summand.
-/
lemma apSumFrom_eq_apSumOffset_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumFrom f (m * d) d n = apSumOffset (fun k => f (d * k)) 1 m n := by
  have h :=
    apSumFrom_tail_eq_apSumOffset_step_one (f := f) (a := 0) (d := d) (m := m) (n := n)
  have hs : (fun k => f (k * d)) = (fun k => f (d * k)) := by
    funext k
    simp [Nat.mul_comm]
  simpa [Nat.zero_add, hs] using h





-- (deprecated alias `apSum_step_one_eq_apSumFrom_tail` moved to `MoltResearch.Discrepancy.Deprecated`)

/-- “Cut + reassemble” normal form at the `apSumFrom`-level (affine nucleus).

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Cut + reassemble” normal form at `apSumFrom`-level.

This is the exact concatenation equality for splitting an affine AP sum of length `m+n`
into a prefix of length `m` plus the tail of length `n`.
-/
lemma apSumFrom_add_length (f : ℕ → ℤ) (a d m n : ℕ) :
  apSumFrom f a d (m + n) = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
  classical
  let g : ℕ → ℤ := fun k => f (a + k)
  have hsplit : apSum g d (m + n) = apSum g d m + apSumOffset g d m n :=
    apSum_add_length (f := g) (d := d) (m := m) (n := n)
  have hL : apSumFrom f a d (m + n) = apSum g d (m + n) := by
    simpa [g] using
      (apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := m + n))
  have hM : apSum g d m = apSumFrom f a d m := by
    simpa [g] using
      (apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := m)).symm
  have hN : apSumOffset g d m n = apSumFrom f (a + m * d) d n := by
    unfold apSumOffset apSumFrom
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hmul : (m + (i + 1)) * d = m * d + (i + 1) * d := by
      simpa using (Nat.add_mul m (i + 1) d)
    -- `simp` uses `Nat.add_assoc` to rewrite `m + i + 1` as `m + (i + 1)` first.
    simp [g, Nat.add_assoc, hmul]
  calc
    apSumFrom f a d (m + n) = apSum g d (m + n) := hL
    _ = apSum g d m + apSumOffset g d m n := hsplit
    _ = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
        simpa [hM, hN]

/-- `simp`-friendly corollary of `apSumFrom_add_length` for `m = 0`. -/
@[simp] lemma apSumFrom_add_length_zero_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d (0 + n) = apSumFrom f a d n := by
  simpa [apSumFrom_add_length] using (apSumFrom_add_length (f := f) (a := a) (d := d) (m := 0) (n := n))

/-- `simp`-friendly corollary of `apSumFrom_add_length` for `n = 0`. -/
@[simp] lemma apSumFrom_add_length_zero_right (f : ℕ → ℤ) (a d m : ℕ) :
    apSumFrom f a d (m + 0) = apSumFrom f a d m := by
  simpa [apSumFrom_add_length] using (apSumFrom_add_length (f := f) (a := a) (d := d) (m := m) (n := 0))

/-- Triangle inequality API for splitting an affine AP sum by length.

Checklist item: Problems/erdos_discrepancy.md (Track B) — immediate corollary of
`apSumFrom_add_length`.
-/
lemma natAbs_apSumFrom_add_length_le (f : ℕ → ℤ) (a d n₁ n₂ : ℕ) :
    Int.natAbs (apSumFrom f a d (n₁ + n₂)) ≤
      Int.natAbs (apSumFrom f a d n₁) + Int.natAbs (apSumFrom f (a + n₁ * d) d n₂) := by
  simpa [apSumFrom_add_length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Int.natAbs_add_le (apSumFrom f a d n₁) (apSumFrom f (a + n₁ * d) d n₂))

lemma apSumFrom_succ_length (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d (n + 1) = f (a + d) + apSumFrom f (a + d) d n := by
  have h := apSumFrom_add_length (f := f) (a := a) (d := d) (m := 1) (n := n)
  simpa [Nat.add_comm, Nat.one_mul, apSumFrom_one] using h

lemma apSumFrom_tail_eq_sub (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumFrom f (a + m * d) d n = apSumFrom f a d (m + n) - apSumFrom f a d m := by
  have h := (apSumFrom_add_length (f := f) (a := a) (d := d) (m := m) (n := n)).symm
  have h' : apSumFrom f (a + m * d) d n + apSumFrom f a d m = apSumFrom f a d (m + n) := by
    simpa [add_comm] using h
  exact eq_sub_of_add_eq h'

-- (see `MoltResearch.Discrepancy.AffineTail` for `apSumFrom_sub_eq_apSumFrom_tail`)

/-- Convenience: when `m ≤ n`, rewrite the affine tail sum of length `n - m` as a difference of
affine AP partial sums.

This is a wrapper around `apSumFrom_tail_eq_sub` that avoids the intermediate endpoint
`m + (n - m)`.
-/
lemma apSumFrom_tail_eq_sub_of_le (f : ℕ → ℤ) (a d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSumFrom f (a + m * d) d (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa [Nat.add_sub_of_le hmn] using
    (apSumFrom_tail_eq_sub (f := f) (a := a) (d := d) (m := m) (n := n - m))

/-- Mul-left variant of the difference normal form: when `m ≤ n`, normalize
`apSumFrom f a d n - apSumFrom f a d m` into a step-one `apSum` whose summand is written as
`d*k + const`.

This is a small wrapper around `apSumFrom_tail_eq_sub_of_le` and
`apSumFrom_tail_eq_apSum_step_one_add_left`.
-/
lemma apSumFrom_sub_eq_apSum_step_one_mul_left_add_of_le (f : ℕ → ℤ) (a d : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m =
      apSum (fun k => f (d * k + (d * m + a))) 1 (n - m) := by
  classical
  -- Rewrite the difference as the canonical tail, then package the tail into step-one form.
  calc
    apSumFrom f a d n - apSumFrom f a d m
        = apSumFrom f (a + m * d) d (n - m) := by
            simpa using (apSumFrom_tail_eq_sub_of_le (f := f) (a := a) (d := d) (m := m) (n := n)
              hmn).symm
    _ = apSum (fun k => f (k * d + (a + m * d))) 1 (n - m) := by
            simpa using
              (apSumFrom_tail_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m)
                (n := n - m))
    _ = apSum (fun k => f (d * k + (d * m + a))) 1 (n - m) := by
            simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-! ### General `Int.natAbs` bounds for affine AP sums -/

/-- Uniform bound on `Int.natAbs` gives a length-times-bound estimate for affine AP sums.

If `|f k| ≤ B` for every term, then
`|apSumFrom f a d n| ≤ n * B`.
-/
lemma natAbs_apSumFrom_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumFrom]
  | succ n ih =>
      have hterm : Int.natAbs (f (a + (n + 1) * d)) ≤ B := hf _
      calc
        Int.natAbs (apSumFrom f a d (n + 1))
            = Int.natAbs (apSumFrom f a d n + f (a + (n + 1) * d)) := by
                simp [apSumFrom_succ]
        _ ≤ Int.natAbs (apSumFrom f a d n) + Int.natAbs (f (a + (n + 1) * d)) :=
              Int.natAbs_add_le _ _
        _ ≤ n * B + B := by
              exact Nat.add_le_add ih hterm
        _ = (n + 1) * B := by
              simpa [Nat.succ_mul, Nat.add_assoc]

/-! A sign sequence has affine AP partial sums bounded by length: `|∑_{i=1}^n f (a + i*d)| ≤ n`. -/
lemma IsSignSequence.natAbs_apSumFrom_le {f : ℕ → ℤ} (hf : IsSignSequence f) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) ≤ n := by
  induction n with
  | zero =>
      simp [apSumFrom]
  | succ n ih =>
      calc
        Int.natAbs (apSumFrom f a d (n + 1))
            = Int.natAbs (apSumFrom f a d n + f (a + (n + 1) * d)) := by
                simp [apSumFrom_succ]
        _ ≤ Int.natAbs (apSumFrom f a d n) + Int.natAbs (f (a + (n + 1) * d)) :=
              Int.natAbs_add_le _ _
        _ = Int.natAbs (apSumFrom f a d n) + 1 := by
              simp [IsSignSequence.natAbs_eq_one (hf := hf)]
        _ ≤ n + 1 := by
              simpa using Nat.add_le_add_right ih 1

/-! ### Algebraic properties of `apSumFrom` -/

@[simp] lemma apSumFrom_add (f g : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom (fun k => f k + g k) a d n = apSumFrom f a d n + apSumFrom g a d n := by
  classical
  unfold apSumFrom
  simpa [Finset.sum_add_distrib]

@[simp] lemma apSumFrom_neg (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom (fun k => - f k) a d n = - apSumFrom f a d n := by
  classical
  unfold apSumFrom
  simpa [Finset.sum_neg_distrib]

@[simp] lemma apSumFrom_sub (f g : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom (fun k => f k - g k) a d n = apSumFrom f a d n - apSumFrom g a d n := by
  classical
  unfold apSumFrom
  simpa [Finset.sum_sub_distrib]

@[simp] lemma apSumFrom_mul_left (c : ℤ) (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom (fun k => c * f k) a d n = c * apSumFrom f a d n := by
  classical
  unfold apSumFrom
  simpa [Finset.mul_sum]

@[simp] lemma apSumFrom_mul_right (f : ℕ → ℤ) (c : ℤ) (a d n : ℕ) :
  apSumFrom (fun k => f k * c) a d n = apSumFrom f a d n * c := by
  classical
  unfold apSumFrom
  simpa [Finset.sum_mul]

/-! ## Affine discrepancy -/

/-- A convenient wrapper for the absolute value of an affine arithmetic-progression sum.

It is defined as the natural absolute value of `apSumFrom f a d n`.
-/
def affineDiscrepancy (f : ℕ → ℤ) (a d n : ℕ) : ℕ :=
  Int.natAbs (apSumFrom f a d n)

/-- Definitional lemma exposing the definition. -/
lemma affineDiscrepancy_eq_natAbs_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    affineDiscrepancy f a d n = Int.natAbs (apSumFrom f a d n) :=
  rfl

/-- Alias for the definitional lemma. -/
lemma affineDiscrepancy_def (f : ℕ → ℤ) (a d n : ℕ) :
    affineDiscrepancy f a d n = Int.natAbs (apSumFrom f a d n) :=
  rfl

/-- `simp` bridge: `Int.natAbs (apSumFrom …)` simplifies to the `affineDiscrepancy` wrapper.

This direction avoids simp loops with `affineDiscrepancy_def`.
-/
@[simp] lemma natAbs_apSumFrom_eq_affineDiscrepancy (f : ℕ → ℤ) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) = affineDiscrepancy f a d n :=
  rfl

/-- The affine discrepancy of an empty progression is zero. -/
@[simp] lemma affineDiscrepancy_zero (f : ℕ → ℤ) (a d : ℕ) :
    affineDiscrepancy f a d 0 = 0 := by
  simp [affineDiscrepancy]

/-- `f` has affine discrepancy at least `C` if some affine AP partial sum exceeds `C` in absolute
value, with a positive step size `d`.

This is the natural analogue of `HasDiscrepancyAtLeast` where we also allow an offset `a`.
-/
def HasAffineDiscrepancyAtLeast (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∃ a d n : ℕ, d > 0 ∧ Int.natAbs (apSumFrom f a d n) > C

/-- Sign-flip invariance: negating the sequence does not change affine discrepancy. -/
@[simp] lemma HasAffineDiscrepancyAtLeast_neg_iff (f : ℕ → ℤ) (C : ℕ) :
    HasAffineDiscrepancyAtLeast (fun k => -f k) C ↔ HasAffineDiscrepancyAtLeast f C := by
  constructor
  · rintro ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    have hnatAbs :
        Int.natAbs (apSumFrom (fun k => -f k) a d n) = Int.natAbs (apSumFrom f a d n) := by
      unfold apSumFrom
      simp
    simpa [hnatAbs] using hgt
  · rintro ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    have hnatAbs :
        Int.natAbs (apSumFrom (fun k => -f k) a d n) = Int.natAbs (apSumFrom f a d n) := by
      unfold apSumFrom
      simp
    simpa [hnatAbs] using hgt

/-- Restate `HasAffineDiscrepancyAtLeast` using the `affineDiscrepancy` wrapper. -/
lemma HasAffineDiscrepancyAtLeast_iff_exists_affineDiscrepancy (f : ℕ → ℤ) (C : ℕ) :
    HasAffineDiscrepancyAtLeast f C ↔ ∃ a d n, d > 0 ∧ affineDiscrepancy f a d n > C := by
  unfold HasAffineDiscrepancyAtLeast affineDiscrepancy
  constructor <;> rintro ⟨a, d, n, hd, hgt⟩ <;> exact ⟨a, d, n, hd, hgt⟩

/-- Variant with the step-size side condition written as `d ≥ 1`. -/
lemma HasAffineDiscrepancyAtLeast_iff_exists_affineDiscrepancy_ge_one (f : ℕ → ℤ) (C : ℕ) :
    HasAffineDiscrepancyAtLeast f C ↔ ∃ a d n, d ≥ 1 ∧ affineDiscrepancy f a d n > C := by
  constructor
  · rintro ⟨a, d, n, hd, hgt⟩
    exact ⟨a, d, n, Nat.succ_le_of_lt hd, by simpa using hgt⟩
  · rintro ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, (Nat.succ_le_iff).1 hd, ?_⟩
    simpa using hgt

/-- Normal form: rewrite `HasAffineDiscrepancyAtLeast f C` into an offset-sum witness on the
shifted sequence `k ↦ f (k + a)`.

This is the `m = 0` case of the general “tail/offset” normal form, expressed using only lemmas
available in this file.
-/
lemma HasAffineDiscrepancyAtLeast_iff_exists_apSumOffset_shift_add_zero {f : ℕ → ℤ} {C : ℕ} :
    HasAffineDiscrepancyAtLeast f C ↔
      ∃ a d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset (fun k => f (k + a)) d 0 n) > C := by
  classical
  constructor
  · rintro ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    -- `apSumFrom f a d n` is definitionally the same as an offset sum of the shifted sequence
    -- `k ↦ f (k + a)` with `m = 0`.
    simpa [HasAffineDiscrepancyAtLeast, apSumFrom, apSumOffset, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hgt
  · rintro ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    simpa [HasAffineDiscrepancyAtLeast, apSumFrom, apSumOffset, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hgt

/-- Witness-level translation: a discrepancy witness for the shifted sequence `k ↦ f (k + a)` is
equivalently an affine AP witness for `f` with offset `a`.

This is the direct bridge between the “homogeneous discrepancy” nucleus predicate and the affine
nucleus object `apSumFrom`.
-/
lemma HasDiscrepancyAtLeast_shift_add_iff_exists_apSumFrom {f : ℕ → ℤ} (a : ℕ) {C : ℕ} :
    HasDiscrepancyAtLeast (fun k => f (k + a)) C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumFrom f a d n) > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    -- Rewrite the homogeneous sum on the shifted sequence as an affine sum on `f`.
    simpa using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa using hgt

/-- Packaging lemma: a discrepancy witness for the shifted sequence gives an affine discrepancy
witness for the original sequence.
-/
lemma HasDiscrepancyAtLeast_shift_add_to_HasAffineDiscrepancyAtLeast {f : ℕ → ℤ} (a : ℕ) {C : ℕ} :
    HasDiscrepancyAtLeast (fun k => f (k + a)) C → HasAffineDiscrepancyAtLeast f C := by
  intro h
  rcases (HasDiscrepancyAtLeast_shift_add_iff_exists_apSumFrom (f := f) a (C := C)).1 h with
    ⟨d, n, hd, hgt⟩
  exact ⟨a, d, n, hd, hgt⟩

/-- Monotonicity of `HasAffineDiscrepancyAtLeast` in the bound. -/
lemma HasAffineDiscrepancyAtLeast.mono {f : ℕ → ℤ} {C₁ C₂ : ℕ}
    (h : HasAffineDiscrepancyAtLeast f C₂) (hC : C₁ ≤ C₂) :
    HasAffineDiscrepancyAtLeast f C₁ := by
  rcases h with ⟨a, d, n, hd, hgt⟩
  exact ⟨a, d, n, hd, lt_of_le_of_lt hC hgt⟩

/-- Decrease the bound by one. -/
lemma HasAffineDiscrepancyAtLeast.of_succ {f : ℕ → ℤ} {C : ℕ}
    (h : HasAffineDiscrepancyAtLeast f (C + 1)) : HasAffineDiscrepancyAtLeast f C := by
  exact
    HasAffineDiscrepancyAtLeast.mono (f := f) (C₁ := C) (C₂ := C + 1) h (Nat.le_succ C)

/-- Extract a witness with positive `n`. -/
lemma HasAffineDiscrepancyAtLeast.exists_witness_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSumFrom f a d n) > C := by
  rcases h with ⟨a, d, n, hd, hgt⟩
  cases n with
  | zero =>
      exfalso
      have : (C : ℕ) < 0 := by
        simpa [apSumFrom_zero] using hgt
      exact Nat.not_lt_zero C this
  | succ n' =>
      refine ⟨a, d, Nat.succ n', hd, ?_, ?_⟩
      · exact Nat.succ_pos _
      · simpa using hgt

/-- Extract a witness with `d ≥ 1`. -/
lemma HasAffineDiscrepancyAtLeast.exists_witness_d_ge_one {f : ℕ → ℤ} {C : ℕ}
    (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n, d ≥ 1 ∧ Int.natAbs (apSumFrom f a d n) > C := by
  rcases h with ⟨a, d, n, hd, hgt⟩
  refine ⟨a, d, n, ?_, hgt⟩
  exact Nat.succ_le_of_lt hd

/-!
### Step-positivity witness normal forms (`d = Nat.succ d'`)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/

/-- From an affine discrepancy witness obtain a witness whose step is written as `Nat.succ d`. -/
lemma HasAffineDiscrepancyAtLeast.exists_witness_succ {f : ℕ → ℤ} {C : ℕ}
    (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n : ℕ, Int.natAbs (apSumFrom f a (Nat.succ d) n) > C := by
  rcases HasAffineDiscrepancyAtLeast.exists_witness_d_ge_one (h := h) with ⟨a, d, n, hd, hgt⟩
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  rcases Nat.exists_eq_succ_of_ne_zero hd0 with ⟨d', rfl⟩
  exact ⟨a, d', n, hgt⟩

/-- Variant of `HasAffineDiscrepancyAtLeast.exists_witness_succ` also recording `n > 0`. -/
lemma HasAffineDiscrepancyAtLeast.exists_witness_succ_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f a (Nat.succ d) n) > C := by
  rcases h.exists_witness_pos with ⟨a, d, n, hd, hn, hgt⟩
  have hd' : d ≥ 1 := Nat.succ_le_of_lt hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd'
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  rcases Nat.exists_eq_succ_of_ne_zero hd0 with ⟨d', rfl⟩
  exact ⟨a, d', n, hn, hgt⟩

/-- Normal form: `HasAffineDiscrepancyAtLeast f C` has a witness with `d ≥ 1` and `n > 0`.

The `n > 0` side condition is automatic from `Int.natAbs (apSumFrom …) > C`, but it is often
useful to keep it explicit in “surface” statements.
-/
lemma HasAffineDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasAffineDiscrepancyAtLeast f C ↔
      ∃ a d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSumFrom f a d n) > C := by
  constructor
  · intro h
    rcases h.exists_witness_pos with ⟨a, d, n, hd, hn, hgt⟩
    exact ⟨a, d, n, Nat.succ_le_of_lt hd, hn, hgt⟩
  · rintro ⟨a, d, n, hd, _hn, hgt⟩
    refine ⟨a, d, n, ?_, hgt⟩
    exact (Nat.succ_le_iff).1 hd

/-- Surface form of affine unbounded discrepancy, matching the usual notation
`∑_{i=1}^n f (a + i*d)`.

This is a thin wrapper around the nucleus predicate `HasAffineDiscrepancyAtLeast`, via
`apSumFrom_eq_sum_Icc`.
-/
theorem forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos
    (f : ℕ → ℤ) :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ, d ≥ 1 ∧ n > 0 ∧
          Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  constructor
  · intro h C
    rcases (HasAffineDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos (f := f) (C := C)).1 (h C)
        with ⟨a, d, n, hd, hn, hgt⟩
    refine ⟨a, d, n, hd, hn, ?_⟩
    simpa [apSumFrom_eq_sum_Icc] using hgt
  · intro h C
    rcases h C with ⟨a, d, n, hd, hn, hgt⟩
    have hgt' : Int.natAbs (apSumFrom f a d n) > C := by
      simpa [← apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)] using hgt
    exact (HasAffineDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos (f := f) (C := C)).2
      ⟨a, d, n, hd, hn, hgt'⟩

/-- Surface form of affine unbounded discrepancy, with the step-size side condition written as
`d > 0`.

This is often the most natural surface form when connecting to statements phrased with a strict
positivity hypothesis.

It is a convenience wrapper around
`forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`, using the
equivalence `d > 0 ↔ d ≥ 1` for natural numbers.
-/
theorem forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ, d > 0 ∧ n > 0 ∧
          Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  constructor
  · intro h C
    rcases
        (forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos
              (f := f)).1 h C with
      ⟨a, d, n, hd, hn, hgt⟩
    refine ⟨a, d, n, ?_, hn, hgt⟩
    -- `d ≥ 1` implies `d > 0`.
    exact (Nat.succ_le_iff).1 hd
  · intro h
    -- Convert the strict-positivity side condition to `d ≥ 1` and reuse the `d ≥ 1` normal form.
    refine
      (forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos
            (f := f)).2 ?_
    intro C
    rcases h C with ⟨a, d, n, hd, hn, hgt⟩
    exact ⟨a, d, n, Nat.succ_le_of_lt hd, hn, hgt⟩

/-- Negating the function does not change affine discrepancy. -/
lemma HasAffineDiscrepancyAtLeast.neg_iff {f : ℕ → ℤ} {C : ℕ} :
    HasAffineDiscrepancyAtLeast (fun n => - f n) C ↔ HasAffineDiscrepancyAtLeast f C := by
  constructor
  · intro h
    rcases h with ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    simpa [apSumFrom_neg] using hgt
  · intro h
    rcases h with ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    simpa [apSumFrom_neg] using hgt

/-- A sign sequence has affine discrepancy at least zero. -/
lemma IsSignSequence.hasAffineDiscrepancyAtLeast_zero {f : ℕ → ℤ}
    (hf : IsSignSequence f) :
    HasAffineDiscrepancyAtLeast f 0 := by
  refine ⟨0, 1, 1, ?_, ?_⟩
  · exact Nat.succ_pos 0
  · simpa [apSumFrom_one, IsSignSequence.natAbs_eq_one (hf := hf)] using Nat.succ_pos 0

/-- Homogeneous discrepancy implies affine discrepancy (take offset `a = 0`). -/
lemma HasDiscrepancyAtLeast.to_affine {f : ℕ → ℤ} {C : ℕ} (h : HasDiscrepancyAtLeast f C) :
    HasAffineDiscrepancyAtLeast f C := by
  rcases h with ⟨d, n, hd, hgt⟩
  refine ⟨0, d, n, hd, ?_⟩
  simpa using hgt

/-- Relate affine discrepancy to shifted homogeneous discrepancy. -/
lemma HasAffineDiscrepancyAtLeast_iff_exists_shift (f : ℕ → ℤ) (C : ℕ) :
  HasAffineDiscrepancyAtLeast f C ↔ ∃ a, HasDiscrepancyAtLeast (fun k => f (a + k)) C := by
  constructor
  · intro h
    rcases h with ⟨a, d, n, hd, hgt⟩
    refine ⟨a, ?_⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSumFrom_eq_apSum_shift_add_left] using hgt
  · rintro ⟨a, h⟩
    rcases h with ⟨d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    simpa [apSumFrom_eq_apSum_shift_add_left] using hgt

/-- Normal form for “affine unbounded discrepancy”: for each `C`, some shift of `f` has
homogeneous discrepancy at least `C`.

This is just `HasAffineDiscrepancyAtLeast_iff_exists_shift` with the quantifier `∀ C` moved
outside.
-/
theorem forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift (f : ℕ → ℤ) :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ a : ℕ, HasDiscrepancyAtLeast (fun k => f (a + k)) C) := by
  constructor
  · intro h C
    exact (HasAffineDiscrepancyAtLeast_iff_exists_shift (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasAffineDiscrepancyAtLeast_iff_exists_shift (f := f) (C := C)).2 (h C)

/-- Extract a witness with `d ≥ 1` and length `n > C`. -/
lemma IsSignSequence.exists_affine_witness_d_ge_one_and_length_gt {f : ℕ → ℤ}
    (hf : IsSignSequence f) {C : ℕ} (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n, d ≥ 1 ∧ n > C ∧ Int.natAbs (apSumFrom f a d n) > C := by
  rcases h with ⟨a, d, n, hd, hgt⟩
  have hd1 : d ≥ 1 := Nat.succ_le_of_lt hd
  have hlen : n > C := by
    have hle : Int.natAbs (apSumFrom f a d n) ≤ n :=
      IsSignSequence.natAbs_apSumFrom_le (hf := hf) a d n
    exact lt_of_lt_of_le hgt hle
  exact ⟨a, d, n, hd1, hlen, hgt⟩

end MoltResearch
