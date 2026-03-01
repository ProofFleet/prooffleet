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

/-- Multiplication-on-the-left paper notation: rewrite `apSumFrom` as
`∑ i ∈ Icc 1 n, f (a + d*i)`.

This variant avoids commuting multiplication under binders in downstream proofs.
-/
lemma apSumFrom_eq_sum_Icc_mul_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + d * i)) := by
  classical
  refine (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (a + d*i)` back to
`apSumFrom`.

This is the inverse orientation of `apSumFrom_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSumFrom_mul_left (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (a + d * i)) = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_sum_Icc_mul_left (f := f) (a := a) (d := d) (n := n)).symm

/-- Multiplication-on-the-left + translation-friendly paper notation: rewrite `apSumFrom` as
`∑ i ∈ Icc 1 n, f (d*i + a)`.

This combines `apSumFrom_eq_sum_Icc_mul_left` with commuting addition outside the binder.
-/
lemma apSumFrom_eq_sum_Icc_mul_left_add (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (d * i + a)) := by
  classical
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (apSumFrom_eq_sum_Icc_mul_left (f := f) (a := a) (d := d) (n := n))

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (d*i + a)` back to
`apSumFrom`.

This is the inverse orientation of `apSumFrom_eq_sum_Icc_mul_left_add`.
-/
lemma sum_Icc_eq_apSumFrom_mul_left_add (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (d * i + a)) = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (n := n)).symm

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

/-- Normal form: an affine AP sum starting at `a = 0` is just a homogeneous AP sum.

This is the inverse orientation of `apSum_eq_apSumFrom`.
-/
lemma apSumFrom_zero_a (f : ℕ → ℤ) (d n : ℕ) :
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

/-- Mul-left variant of `apSumFrom_mul_eq_apSumOffset`.

This is a tiny normal-form helper when your affine start is already written as `d * m`, so you can
rewrite to an `apSumOffset` without first commuting multiplication.
-/
lemma apSumFrom_mul_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumFrom f (d * m) d n = apSumOffset f d m n := by
  -- Reuse the `m * d` lemma, but keep the statement in the `d * m` orientation.
  simpa [Nat.mul_comm] using (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Convenience wrapper: if the affine start `a` is *definitionally* a multiple of `d`, rewrite
`apSumFrom f a d n` to an offset sum.

This is a small normal-form helper when your context already contains a fact `a = m * d`.
-/
lemma apSumFrom_eq_apSumOffset_of_eq_mul (f : ℕ → ℤ) {a d m n : ℕ} (ha : a = m * d) :
    apSumFrom f a d n = apSumOffset f d m n := by
  simpa [ha] using (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Mul-left variant of `apSumFrom_eq_apSumOffset_of_eq_mul`.

This is a small normal-form helper when your context already contains a fact `a = d * m`.
-/
lemma apSumFrom_eq_apSumOffset_of_eq_mul_left (f : ℕ → ℤ) {a d m n : ℕ} (ha : a = d * m) :
    apSumFrom f a d n = apSumOffset f d m n := by
  simpa [ha] using (apSumFrom_mul_left_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

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
    simpa [hdiv] using
      (apSumFrom_mul_left_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

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
lemma apSumFrom_eq_apSumOffset_step_one_zero_m (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  -- `apSumOffset g 1 0 n` simp-normalizes to `apSum g 1 n`.
  simpa [apSumFrom_eq_apSum_step_one] using
    (apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n))

/-- Normal form (“step-one”, offset-sum view): express an affine AP sum as an `apSumOffset` with
step size `1`.

This name is aligned with the existing `…_step_one` family (cf. `apSumOffset_eq_apSumOffset_step_one`).

Implementation note: this is just a wrapper around `apSumFrom_eq_apSumOffset_step_one_zero_m`.
-/
lemma apSumFrom_eq_apSumOffset_step_one (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  simpa using (apSumFrom_eq_apSumOffset_step_one_zero_m (f := f) (a := a) (d := d) (n := n))

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

/-- Translation-friendly variant of `apSumFrom_eq_apSumOffset_step_one_zero_m`.

This packages the summand as `k * d + a` rather than `a + k * d`.
-/
lemma apSumFrom_eq_apSumOffset_step_one_zero_m_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa [Nat.add_comm] using
    (apSumFrom_eq_apSumOffset_step_one_zero_m (f := f) (a := a) (d := d) (n := n))

/-- Translation-friendly variant of `apSumFrom_eq_apSumOffset_step_one`.

This name is aligned with the existing `…_step_one` family.

Implementation note: this is just a wrapper around `apSumFrom_eq_apSumOffset_step_one_zero_m_add_left`.
-/
lemma apSumFrom_eq_apSumOffset_step_one_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    (apSumFrom_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (n := n))

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

/-- Inverse orientation of `apSumFrom_eq_apSum_step_one`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSum_step_one_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSum (fun k => f (a + k * d)) 1 n = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n)).symm

/-- Normal form (“step-one”, `apSumFrom`-native): express an affine AP sum as an `apSumFrom`
with step size `1` by bundling the original step size `d` into the summand.

This is the affine analogue of `apSumOffset_eq_apSumOffset_step_one`.

The right-hand side is often convenient when you want to stay in the `apSumFrom` API
(e.g. to use `apSumFrom_add_length`) while normalizing away an explicit step size.
-/
lemma apSumFrom_eq_apSumFrom_step_one (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumFrom (fun k => f (a + k * d)) 0 1 n := by
  unfold apSumFrom
  simp

/-- Translation-friendly variant of `apSumFrom_eq_apSumFrom_step_one`.

This packages the summand as `k * d + a` rather than `a + k * d`.
-/
lemma apSumFrom_eq_apSumFrom_step_one_add_left (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n = apSumFrom (fun k => f (k * d + a)) 0 1 n := by
  simpa [Nat.add_comm] using
    (apSumFrom_eq_apSumFrom_step_one (f := f) (a := a) (d := d) (n := n))

/-- Inverse orientation of `apSumFrom_eq_apSumFrom_step_one`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSumFrom_step_one_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom (fun k => f (a + k * d)) 0 1 n = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_apSumFrom_step_one (f := f) (a := a) (d := d) (n := n)).symm

/-- Inverse orientation of `apSumFrom_eq_apSumFrom_step_one_add_left`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSumFrom_step_one_add_left_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom (fun k => f (k * d + a)) 0 1 n = apSumFrom f a d n := by
  simpa using
    (apSumFrom_eq_apSumFrom_step_one_add_left (f := f) (a := a) (d := d) (n := n)).symm

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
        (apSumOffset_zero_m (f := fun k => f (a + (m + k) * d)) (d := 1) (n := n)).symm

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
        (apSumOffset_zero_m (f := fun k => f (k * d + (a + m * d))) (d := 1) (n := n)).symm

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

/-- Inverse orientation of `apSumFrom_tail_eq_apSumOffset_step_one`.

We do *not* mark this as `[simp]`: our normal forms usually prefer to *introduce* the step-one
`apSumOffset … 1 m n` shape, not eliminate it.
-/
lemma apSumOffset_step_one_eq_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (a + k * d)) 1 m n = apSumFrom f (a + m * d) d n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (m := m) (n := n)).symm

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

/-- Inverse orientation of `apSumFrom_eq_apSumOffset_mul_left`.

We do *not* mark this as `[simp]`: our normal forms usually prefer to *introduce* the
`apSumOffset … 1 m n` shape.
-/
lemma apSumOffset_eq_apSumFrom_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (d * k)) 1 m n = apSumFrom f (m * d) d n := by
  simpa using (apSumFrom_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumFrom_tail_eq_apSumOffset_step_one_add_left`.

We do *not* mark this as `[simp]`: our normal forms prefer the `apSumOffset … 1 m n` presentation
once we have decided to work in the step-one world.
-/
lemma apSumOffset_step_one_add_left_eq_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (k * d + a)) 1 m n = apSumFrom f (a + m * d) d n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumFrom_tail_eq_apSum_step_one_add_left`.

We do *not* mark this as `[simp]`: our normal forms prefer the `k*d + const` presentation when
using the `_add_left` lemmas.
-/
lemma apSum_step_one_add_left_eq_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    apSum (fun k => f (k * d + (a + m * d))) 1 n = apSumFrom f (a + m * d) d n := by
  simpa using
    (apSumFrom_tail_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left`.

This is a convenience lemma for returning from the translation-friendly `apSumOffset … 1 0 n`
step-one normal form back to the affine nucleus API.
-/
lemma apSumOffset_step_one_zero_m_add_left_eq_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (k * d + (a + m * d))) 1 0 n = apSumFrom f (a + m * d) d n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)).symm

/-- Inverse orientation of `apSumFrom_eq_apSumOffset_step_one_zero_m_add_left`.

This is the `m = 0` case of `apSumOffset_step_one_zero_m_add_left_eq_apSumFrom_tail`.
-/
lemma apSumOffset_step_one_zero_m_add_left_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    apSumOffset (fun k => f (k * d + a)) 1 0 n = apSumFrom f a d n := by
  simpa using
    (apSumOffset_step_one_zero_m_add_left_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := 0)
      (n := n))

/-- Inverse orientation of `apSumFrom_tail_eq_apSum_step_one`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSum_step_one_eq_apSumFrom_tail (f : ℕ → ℤ) (a d m n : ℕ) :
    apSum (fun k => f (a + (m + k) * d)) 1 n = apSumFrom f (a + m * d) d n := by
  simpa using (apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)).symm

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

/-- Triangle inequality API for splitting an affine AP sum by length. -/
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

@[simp] lemma apSumFrom_mul_right (c : ℤ) (f : ℕ → ℤ) (a d n : ℕ) :
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

/-- Simplification lemma exposing the definition. -/
@[simp] lemma affineDiscrepancy_eq_natAbs_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    affineDiscrepancy f a d n = Int.natAbs (apSumFrom f a d n) :=
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
    exact ⟨a, d, n, Nat.succ_le_of_lt hd, by simpa [affineDiscrepancy] using hgt⟩
  · rintro ⟨a, d, n, hd, hgt⟩
    refine ⟨a, d, n, (Nat.succ_le_iff).1 hd, ?_⟩
    simpa [affineDiscrepancy] using hgt

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
  simpa [apSum_eq_apSumFrom] using hgt

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
