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

/-- Sum of `f` over the next `n` terms of the arithmetic progression after skipping `m` terms.

It is defined as `∑ i in range n, f ((m + i + 1) * d)`. -/
def apSumOffset (f : ℕ → ℤ) (d m n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f ((m + i + 1) * d))

/-- `f` has discrepancy at least `C` if some AP partial sum exceeds `C` in absolute value,
with a **positive** step size `d ≥ 1`.

We compare via `Int.natAbs` so `C : ℕ` stays natural.
-/
def HasDiscrepancyAtLeast (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSum f d n) > C

/-- Monotonicity of `HasDiscrepancyAtLeast` in the bound. -/
lemma HasDiscrepancyAtLeast.mono {f : ℕ → ℤ} {C₁ C₂ : ℕ}
    (h : HasDiscrepancyAtLeast f C₂) (hC : C₁ ≤ C₂) : HasDiscrepancyAtLeast f C₁ := by
  rcases h with ⟨d, n, hd, hn⟩
  exact ⟨d, n, hd, lt_of_le_of_lt hC hn⟩

/-- Decrease the bound by one. -/
lemma HasDiscrepancyAtLeast.of_succ {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f (C + 1)) : HasDiscrepancyAtLeast f C := by
  exact
    HasDiscrepancyAtLeast.mono (f := f) (C₁ := C) (C₂ := C + 1) h (Nat.le_succ C)

/-- Unpack the defining property. -/
lemma IsSignSequence.eq_one_or_eq_neg_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    f n = 1 ∨ f n = -1 :=
  hf n

lemma IsSignSequence.natAbs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    Int.natAbs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

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

@[simp] lemma apSum_zero (f : ℕ → ℤ) (d : ℕ) : apSum f d 0 = 0 := by
  simp [apSum]

@[simp] lemma apSum_one (f : ℕ → ℤ) (d : ℕ) : apSum f d 1 = f d := by
  simp [apSum]

@[simp] lemma apSumOffset_zero (f : ℕ → ℤ) (d m : ℕ) : apSumOffset f d m 0 = 0 := by
  simp [apSumOffset]

@[simp] lemma apSumOffset_one (f : ℕ → ℤ) (d m : ℕ) : apSumOffset f d m 1 = f ((m + 1) * d) := by
  simp [apSumOffset]

lemma apSumOffset_succ (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  classical
  -- expand definition and use `Finset.range_add_one`
  unfold apSumOffset
  simp [Finset.range_add_one, Finset.sum_insert, add_comm, add_assoc]

lemma apSum_eq_apSumOffset (f : ℕ → ℤ) (d n : ℕ) : apSum f d n = apSumOffset f d 0 n := by
  unfold apSum apSumOffset
  simp

lemma apSum_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  classical
  -- `Finset.range (n+1)` is `insert n (range n)`
  simp [apSum, Finset.range_add_one, Finset.sum_insert]
  -- remaining goal is just commutativity
  simp [add_comm]

@[simp] lemma apSum_two (f : ℕ → ℤ) (d : ℕ) : apSum f d 2 = f d + f (2 * d) := by
  simpa [apSum_one] using (apSum_succ (f := f) (d := d) (n := 1))

/-- Split `apSum` over a sum of lengths: `apSum f d (m + n)` equals the sum over the first `m` terms plus the sum over the next `n` terms. -/
lemma apSum_add_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) = apSum f d m + apSumOffset f d m n := by
  induction n with
  | zero =>
      simp [apSumOffset, apSum]
  | succ n ih =>
      have hsucc := (apSum_succ (f := f) (d := d) (n := m + n))
      calc
        apSum f d (m + n + 1)
            = apSum f d (m + n) + f ((m + n + 1) * d) := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsucc
        _ = (apSum f d m + apSumOffset f d m n) + f ((m + n + 1) * d) := by
              simp [ih]
        _ = apSum f d m + (apSumOffset f d m n + f ((m + n + 1) * d)) := by
              simp [add_assoc]
        _ = apSum f d m + apSumOffset f d m (n + 1) := by
              simp [apSumOffset_succ (f := f) (d := d) (m := m) (n := n)]

-- Algebraic properties of `apSum`
lemma apSum_add (f g : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f k + g k) d n = apSum f d n + apSum g d n := by
  classical
  unfold apSum
  simp [Finset.sum_add_distrib]

lemma apSum_neg (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => - f k) d n = - apSum f d n := by
  classical
  unfold apSum
  simp [Finset.sum_neg_distrib]

lemma apSum_sub (f g : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f k - g k) d n = apSum f d n - apSum g d n := by
  classical
  unfold apSum
  simp [Finset.sum_sub_distrib]

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

lemma apSum_zero_d (f : ℕ → ℤ) (n : ℕ) : apSum f 0 n = n • f 0 := by
  classical
  -- along step size 0, the AP is constant at 0
  simp [apSum]

end MoltResearch
