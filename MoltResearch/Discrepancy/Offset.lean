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

/-- Rewrite `apSumOffset` as the familiar interval sum `∑ i ∈ Icc (m+1) (m+n), f (i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumOffset`, and
rewrite to this form only when matching paper notation.
-/
lemma apSumOffset_eq_sum_Icc (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  classical
  unfold apSumOffset
  have h :=
    (Finset.sum_Ico_eq_sum_range (f := fun i => f (i * d)) (m := m + 1) (n := m + (n + 1)))
  have hlen : (m + (n + 1)) - (m + 1) = n := by
    -- `(m+1+n) - (m+1) = n`, and `m+1+n = m+(n+1)`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.add_sub_cancel_left (m + 1) n)
  calc
    (Finset.range n).sum (fun i => f ((m + i + 1) * d))
        = (Finset.range n).sum (fun i => f ((m + (i + 1)) * d)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- `m + i + 1 = m + (i + 1)`
            simp [Nat.add_assoc]
    _ = (Finset.Ico (m + 1) (m + (n + 1))).sum (fun i => f (i * d)) := by
            -- `h` is oriented from `Ico` to `range`; we use it backwards.
            simpa [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm
    _ = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
            -- Convert the upper endpoint to the canonical `(m+n)+1` form.
            have hend : m + (n + 1) = (m + n) + 1 := by
              simp [Nat.add_assoc]
            have hsum :
                (Finset.Ico (m + 1) ((m + n) + 1)).sum (fun i => f (i * d)) =
                  (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
              simpa using
                congrArg (fun s : Finset ℕ => s.sum (fun i => f (i * d)))
                  (Finset.Ico_add_one_right_eq_Icc (a := m + 1) (b := m + n))
            simpa [hend] using hsum

/-- Special case: step size `d = 1` turns `apSumOffset` into the plain interval sum
`∑ i ∈ Icc (m+1) (m+n), f i`.

This is a small convenience wrapper around `apSumOffset_eq_sum_Icc`.
-/
lemma apSumOffset_one_d (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 1 m n = (Finset.Icc (m + 1) (m + n)).sum f := by
  simpa using (apSumOffset_eq_sum_Icc (f := f) (d := 1) (m := m) (n := n))

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc (m+1) (m+n), f (i*d)` back
to `apSumOffset`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).symm

/-- Translation-friendly variant of `apSumOffset_eq_sum_Icc` using `d * i` (step size on the left).

This is occasionally convenient when you want to share a summand shape with affine sums, which are
commonly written as `i * d + a`.
-/
lemma apSumOffset_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  classical
  refine (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc (m+1) (m+n), f (d*i)` back to
`apSumOffset`.

This is the inverse orientation of `apSumOffset_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSumOffset_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Split the “paper notation” interval sum
`∑ i ∈ Icc (m+1) (m+(n₁+n₂)), f (i*d)` into the first `n₁` terms and the next `n₂` terms.

This is the interval-sum counterpart of the nucleus normal form `apSumOffset_add_length`.
-/
lemma sum_Icc_add_length (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  classical
  -- Normalize to offset sums, split by length, then rewrite back to interval sums.
  calc
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))
        = apSumOffset f d m (n₁ + n₂) := by
            simpa using
              (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n₁ + n₂))
    _ = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
    _ = (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
            simp [apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Translation-friendly variant of `sum_Icc_add_length` using `d * i` (step size on the left).

This is occasionally convenient when you want to avoid commuting multiplication under binders.
-/
lemma sum_Icc_add_length_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  classical
  -- Reduce to the `i * d` statement via commutativity.
  simpa [Nat.mul_comm] using
    (sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Normal form: when `m ≤ n`, rewrite the “paper notation” interval sum
`∑ i ∈ Icc (m+1) n, f (i*d)` back to `apSumOffset f d m (n - m)`.

This is a convenience wrapper around `sum_Icc_eq_apSumOffset` that normalizes the upper endpoint
into the canonical `(m + (n - m))` form.
-/
lemma sum_Icc_eq_apSumOffset_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa [Nat.add_sub_of_le hmn] using
    (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n - m))

/-- Surface form: when `m ≤ n`, rewrite the offset sum `apSumOffset f d m (n - m)` as the
interval sum `∑ i ∈ Icc (m+1) n, f (i*d)`.

This is the inverse orientation of `sum_Icc_eq_apSumOffset_of_le`.
-/
lemma apSumOffset_eq_sum_Icc_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- Difference of two homogeneous AP partial sums as an offset AP sum when `m ≤ n`. -/
lemma apSum_sub_apSum_eq_apSumOffset (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  -- use apSumOffset_eq_sub with length (n-m)
  have h := (apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n - m)).symm
  have hmn' : m + (n - m) = n := Nat.add_sub_of_le hmn
  simpa [hmn'] using h

/-- Convenience: when `m ≤ n`, rewrite an offset sum of length `n - m` as a difference of
homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_apSum_eq_apSumOffset`. It avoids the intermediate
endpoint `m + (n - m)` that appears when expanding `apSumOffset` via `apSumOffset_eq_sub`.
-/
lemma apSumOffset_eq_apSum_sub_apSum_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = apSum f d n - apSum f d m := by
  simpa [Nat.add_sub_of_le hmn] using
    (apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n - m))

/-- Convenience: when `m ≤ n`, split `apSum f d n` into its first `m` terms and the remaining
`n - m` terms as an `apSumOffset`.

This is a small wrapper around `apSum_add_length` that normalizes the upper endpoint into the
canonical `m + (n - m)` form.
-/
lemma apSum_eq_add_apSumOffset_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n = apSum f d m + apSumOffset f d m (n - m) := by
  -- Normalize `n` as `m + (n - m)` and apply the length-splitting lemma.
  simpa [Nat.add_sub_of_le hmn] using (apSum_add_length (f := f) (d := d) (m := m) (n := n - m))

/-- Difference of a longer homogeneous AP partial sum and its initial segment, in the `(m + n) - m`
normal form.

This lemma is a convenience wrapper around `apSumOffset_eq_sub`, oriented so that rewriting
turns a subtraction into an explicit offset sum.
-/
lemma apSum_sub_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)).symm

/-- Rewrite the normal-form difference `apSum f d (m+n) - apSum f d m` as an interval sum
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumOffset` and use
this lemma only when matching paper notation.
-/
lemma apSum_sub_eq_sum_Icc (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  -- Rewrite subtraction to an offset sum, then to an interval sum.
  simp [apSum_sub_eq_apSumOffset, apSumOffset_eq_sum_Icc]

/-- Translation-friendly variant of `apSum_sub_eq_sum_Icc` using `d * i` (step size on the left). -/
lemma apSum_sub_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  classical
  refine (apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Translation-friendly variant of `apSum_sub_apSum_eq_sum_Icc` using `d * i` (step size on the
left).

This is occasionally convenient when you want to share a summand shape with affine sums.
-/
lemma apSum_sub_apSum_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
  classical
  calc
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
        simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn
    _ = (Finset.Icc (m + 1) (m + (n - m))).sum (fun i => f (d * i)) := by
        simpa using
          (apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n - m))
    _ = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
        simp [Nat.add_sub_of_le hmn]

/-- Normal form (paper → nucleus, difference): rewrite the interval sum
`∑ i ∈ Icc (m+1) (m+n), f (d*i)` as the difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSum_sub_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form (paper → nucleus, difference): when `m ≤ n`, rewrite
`∑ i ∈ Icc (m+1) n, f (d*i)` as a difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_apSum_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSum_sub_apSum_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSum f d n - apSum f d m := by
  simpa using (apSum_sub_apSum_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- When `m ≤ n`, rewrite `apSum f d n - apSum f d m` as an interval sum
`∑ i ∈ Icc (m+1) n, f (i*d)`.

This is the “paper notation” counterpart of `apSum_sub_apSum_eq_apSumOffset`.
-/
lemma apSum_sub_apSum_eq_sum_Icc (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  have h := apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (hmn := hmn)
  -- Rewrite the offset tail to an interval sum and simplify the endpoint `m + (n - m) = n`.
  simpa [apSumOffset_eq_sum_Icc, Nat.add_sub_of_le hmn] using h

/-- Normal form (paper → nucleus, difference): rewrite the interval sum
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` as the difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_eq_sum_Icc`.
-/
lemma sum_Icc_eq_apSum_sub (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form (paper → nucleus, difference): when `m ≤ n`, rewrite
`∑ i ∈ Icc (m+1) n, f (i*d)` as a difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_apSum_eq_sum_Icc`.
-/
lemma sum_Icc_eq_apSum_sub_apSum_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum f d n - apSum f d m := by
  simpa using (apSum_sub_apSum_eq_sum_Icc (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- Normal form (“step-one”): express an offset AP sum as an `apSumOffset` with step size `1`
by bundling the step size `d` into the summand.

This is the offset-sum analogue of `apSum_eq_apSum_step_one`.
-/
lemma apSumOffset_eq_apSumOffset_step_one (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
  unfold apSumOffset
  simp

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_step_one`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSumOffset_step_one_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (k * d)) 1 m n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n)).symm

/-- Express `apSumOffset` as an `apSum` with step `1`. -/
lemma apSumOffset_eq_apSum_step_one (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
  unfold apSumOffset apSum
  -- `simp` reduces `((i+1)*1)` and normalizes `(m + (i+1))`.
  simp [Nat.add_assoc]

/-- Translation-friendly variant of `apSumOffset_eq_apSum_step_one`.

This rewrites the summand index from `((m + k) * d)` into the “constant on the right” form
`k * d + m * d` using `Nat.add_mul`.

This normal form is occasionally more convenient when you plan to apply translation lemmas that
expect an explicit `x + const` structure.
-/
lemma apSumOffset_eq_apSum_step_one_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  -- Start from the canonical step-one form and rewrite the AP index.
  simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n))

/-- Inverse orientation of `apSumOffset_eq_apSum_step_one`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSum_step_one_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f ((m + k) * d)) 1 n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSum_step_one_add_left`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSum_step_one_add_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k * d + m * d)) 1 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form: rewrite an offset AP sum to a step-one offset sum with zero offset by bundling the
offset `m` and step size `d` into the summand.

This is occasionally convenient when you want to reuse lemmas about `apSumOffset` while avoiding
both the explicit offset and the explicit step size.
-/
lemma apSumOffset_eq_apSumOffset_step_one_zero_m (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
  calc
    apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
      simpa using apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
      simpa using
        (apSumOffset_zero_m (f := fun k => f ((m + k) * d)) (d := 1) (n := n)).symm

/-- Variant of `apSumOffset_eq_apSumOffset_step_one_zero_m` written in the translation-friendly
`k * d + m * d` form.

This eliminates both the offset parameter and the AP step size as explicit arguments of
`apSumOffset`, at the cost of moving them into the summand.
-/
lemma apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  calc
    apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
      simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
      simpa using
        (apSumOffset_zero_m (f := fun k => f (k * d + m * d)) (d := 1) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_step_one_zero_m`. -/
lemma apSumOffset_step_one_zero_m_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f ((m + k) * d)) 1 0 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSumOffset_step_one_zero_m (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_step_one_zero_m_add_left`. -/
lemma apSumOffset_step_one_zero_m_add_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (k * d + m * d)) 1 0 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Express `apSumOffset` as an `apSum` with the same step on a shifted function. -/
lemma apSumOffset_eq_apSum_shift (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (m * d + k)) d n := by
  unfold apSumOffset apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmul : (m + i + 1) * d = m * d + (i + 1) * d := by
    simpa [Nat.add_assoc] using (Nat.add_mul m (i + 1) d)
  -- rewrite the AP index in the summand
  simp [hmul]

/-- Variant of `apSumOffset_eq_apSum_shift` written in the translation-friendly `k + const` form.

This can be convenient when composing with lemmas that are oriented as `x ↦ x + k`.
-/
lemma apSumOffset_eq_apSum_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  have h := apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)
  have hswap :
      apSum (fun k => f (m * d + k)) d n = apSum (fun k => f (k + m * d)) d n := by
    unfold apSum
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [Nat.add_comm]
  exact h.trans hswap

/-- Inverse orientation of `apSumOffset_eq_apSum_shift`. -/
lemma apSum_shift_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (m * d + k)) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSum_shift_add`.

We do *not* mark this as `[simp]`: our normal forms generally prefer to *introduce* the
translation-friendly shifted-sequence view.
-/
lemma apSum_shift_add_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Commute a translation in the shifted-sequence view of `apSumOffset`.

This is a convenience lemma: the two shifted sequences `k ↦ f (a + k)` and `k ↦ f (k + a)` are
definitionally different, and without this lemma you often need a `funext` + `Nat.add_comm` rewrite
to swap between them.

We do *not* mark this as `[simp]`: it is meant as an explicit normal-form rewrite when you want to
standardize on the translation-friendly `k + a` presentation.
-/
lemma apSumOffset_shift_comm (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f (k + a)) d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Normalize an offset AP sum by shifting the underlying sequence and resetting the offset `m = 0`.

This can be a convenient normal form when you want to treat offset sums as homogeneous sums on a
shifted sequence, so that subsequent rewriting/simp lemmas only have to handle the `m = 0` case.

We provide both an `m*d + k` variant (constant on the left) and a translation-friendly `k + m*d`
variant (constant on the right).
-/
lemma apSumOffset_eq_apSumOffset_shift (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (m * d + k)) d 0 n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Both sides simplify to the same shifted index `m*d + (i+1)*d`.
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul]

/-- Translation-friendly variant of `apSumOffset_eq_apSumOffset_shift` written in the `k + const` form.

This can be convenient when composing with lemmas that are oriented as `x ↦ x + k`.
-/
lemma apSumOffset_eq_apSumOffset_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  -- Start from the `m*d + k` form and commute the addition in the summand.
  have h := apSumOffset_eq_apSumOffset_shift (f := f) (d := d) (m := m) (n := n)
  -- Rewrite `m*d + k` to `k + m*d` pointwise.
  unfold apSumOffset at h ⊢
  -- `simp` can now do the pointwise arithmetic normalization.
  simpa [Nat.add_comm] using h

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_shift`. -/
lemma apSumOffset_shift_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (m * d + k)) d 0 n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumOffset_shift (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_shift_add`.

We do *not* mark this as `[simp]`: our normal forms usually prefer to *introduce* the explicit
shifted-sequence view and eliminate the offset parameter `m`.
-/
lemma apSumOffset_shift_add_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (k + m * d)) d 0 n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form: push an offset parameter into a translation of the underlying sequence.

Concretely, an offset sum on the shifted sequence `k ↦ f (k + a)` can be rewritten as an offset sum
with `m = 0` by absorbing the offset into the translation constant:

`apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m*d))) d 0 n`.

This is useful when you want to eliminate the explicit offset parameter `m` but keep the
translation-friendly `k + const` presentation.
-/
lemma apSumOffset_shift_add_eq_apSumOffset_shift_add (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  -- First eliminate the offset parameter using the generic shifted-sequence normal form.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumOffset_eq_apSumOffset_shift_add (f := fun k => f (k + a)) (d := d) (m := m) (n := n))

/-- Inverse orientation of `apSumOffset_shift_add_eq_apSumOffset_shift_add`. -/
lemma apSumOffset_shift_add_shift_add_eq_apSumOffset_shift_add (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (k + (a + m * d))) d 0 n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using (apSumOffset_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m)
    (n := n)).symm

/-- Normal form (add-left variant): push an offset parameter into a translation constant.

This is the `a + k` analogue of `apSumOffset_shift_add_eq_apSumOffset_shift_add`.

Concretely:
`apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f ((a + m*d) + k)) d 0 n`.

We keep both `… + k` and `k + …` flavors available since `simp` often behaves better when we avoid
commuting addition under binders.
-/
lemma apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f ((a + m * d) + k)) d 0 n := by
  -- Eliminate the offset parameter using the generic `m*d + k` shifted-sequence view.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumOffset_eq_apSumOffset_shift (f := fun k => f (a + k)) (d := d) (m := m) (n := n))

/-- Inverse orientation of `apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left`. -/
lemma apSumOffset_shift_add_left_shift_add_left_eq_apSumOffset_shift_add_left (f : ℕ → ℤ)
    (a d m n : ℕ) :
    apSumOffset (fun k => f ((a + m * d) + k)) d 0 n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)).symm

-- (lemma `apSumOffset_add_length` moved to `MoltResearch/Discrepancy/Basic.lean`)

/-- Split an offset AP sum at an intermediate length `n₁` when `n₁ ≤ n₂`.

This is the offset-sum analogue of `apSumFrom_eq_add_apSumFrom_tail`.
-/
lemma apSumOffset_eq_add_apSumOffset_tail (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) (n₂ - n₁) := by
  -- Rewrite `n₂` as `n₁ + (n₂ - n₁)` and apply `apSumOffset_add_length`.
  simpa [Nat.add_sub_of_le hn] using
    (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂ - n₁))

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

/-- Tail of an offset AP sum as a difference of a longer sum and its initial segment. -/
lemma apSumOffset_tail_eq_sub (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d (m + n₁) n₂ = apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ := by
  have h := apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
  have hsub := congrArg (fun z : ℤ => z - apSumOffset f d m n₁) h
  have : apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
    simpa [add_sub_cancel_left] using hsub
  simpa using this.symm

/-- Rewrite the normal-form difference `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁`
 as the tail `apSumOffset f d (m+n₁) n₂`.

This is the offset-sum analogue of `apSum_sub_eq_apSumOffset` / `apSumFrom_sub_eq_apSumFrom_tail`.
-/
lemma apSumOffset_sub_eq_apSumOffset_tail (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using (apSumOffset_tail_eq_sub (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)).symm

/-- Rewrite the normal-form difference `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁`
as the “paper notation” interval sum `∑ i ∈ Icc (m+n₁+1) (m+n₁+n₂), f (i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumOffset` and use
this lemma only when matching paper notation.
-/
lemma apSumOffset_sub_eq_sum_Icc (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  -- First rewrite the subtraction to a tail sum, then rewrite that tail to an interval sum.
  calc
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁
        = apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁)
                (n₂ := n₂))
    _ = (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
            simpa [Nat.add_assoc] using
              (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m + n₁) (n := n₂))

/-- Difference of two offset sums over the same start `m` as a tail sum when `n₁ ≤ n₂`. -/
lemma apSumOffset_sub_apSumOffset_eq_apSumOffset (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) := by
  have h :=
    apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂ - n₁)
  simpa [Nat.add_sub_of_le hn] using h

/-- When `n₁ ≤ n₂`, rewrite the difference of two offset sums as the “paper notation” interval sum
`∑ i ∈ Icc (m+n₁+1) (m+n₂), f (i*d)`.

This is the “paper notation” counterpart of `apSumOffset_sub_apSumOffset_eq_apSumOffset`.
-/
lemma apSumOffset_sub_apSumOffset_eq_sum_Icc (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (i * d)) := by
  have hEq :=
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)
  -- Rewrite the tail to an interval sum and simplify `m + n₁ + (n₂ - n₁) = m + n₂`.
  simpa [apSumOffset_eq_sum_Icc, Nat.add_sub_of_le hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq

/-- Sign-sequence bound on the difference of two offset sums when `n₁ ≤ n₂`. -/
lemma IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    Int.natAbs (apSumOffset f d m n₂ - apSumOffset f d m n₁) ≤ n₂ - n₁ := by
  have hEq :=
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)
  have hf' : IsSignSequence (fun k => f ((m + n₁) * d + k)) := by
    intro k
    exact hf (((m + n₁) * d) + k)
  have hle :
      Int.natAbs (apSum (fun k => f ((m + n₁) * d + k)) d (n₂ - n₁)) ≤ n₂ - n₁ :=
    IsSignSequence.natAbs_apSum_le (hf := hf') (d := d) (n := n₂ - n₁)
  have hShift := apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m + n₁) (n := n₂ - n₁)
  have htail : Int.natAbs (apSumOffset f d (m + n₁) (n₂ - n₁)) ≤ n₂ - n₁ := by
    simpa [hShift] using hle
  simpa [hEq] using htail

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
  have hf' : IsSignSequence (fun k => f (m * d + k)) := by
    intro k
    exact hf (m * d + k)
  have h_eq := apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)
  have h_le := (IsSignSequence.natAbs_apSum_le (hf := hf') (d := d) (n := n))
  simpa [h_eq] using h_le

lemma IsSignSequence.natAbs_apSum_sub_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n := by
  have h := hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)] using h

lemma IsSignSequence.natAbs_apSum_sub_apSum_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    Int.natAbs (apSum f d n - apSum f d m) ≤ n - m := by
  have h := hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n - m)
  simpa [apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (hmn := hmn)] using h

end MoltResearch
