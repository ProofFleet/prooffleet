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

/-- From a discrepancy witness obtain `d` and `n` both positive. -/
lemma HasDiscrepancyAtLeast.exists_witness_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  cases n with
  | zero =>
      -- `apSum f d 0 = 0`, so `natAbs` cannot be strictly greater than `C`.
      exfalso
      have hgt' : (C : ℕ) < 0 := by
        simpa [apSum] using hgt
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

lemma IsSignSequence.natAbs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    Int.natAbs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

/-- Normal form: for a sign sequence, the integer absolute value satisfies `|f n| = 1`. -/
lemma IsSignSequence.abs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    abs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

/-- A sign sequence is pointwise bounded by `1` in absolute value. -/
lemma IsSignSequence.abs_le_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    abs (f n) ≤ 1 := by
  simpa [hf.abs_eq_one n]

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
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    _ = (Finset.Ico 1 (n + 1)).sum (fun i => f (i * d)) := by
            simpa [Nat.add_sub_cancel] using h.symm
    _ = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
            simpa [Finset.Ico_add_one_right_eq_Icc]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (i*d)` back to `apSum`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSum (f : ℕ → ℤ) (d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using (apSum_eq_sum_Icc (f := f) (d := d) (n := n)).symm

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

/-- Normal form (“step-one”): express a homogeneous AP sum as an `apSum` with step size `1`
by bundling the step size `d` into the summand.

This is the homogeneous analogue of `apSumOffset_eq_apSum_step_one` and
`apSumFrom_eq_apSum_step_one`.
-/
lemma apSum_eq_apSum_step_one (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  unfold apSum
  simp

/-- Inverse orientation of `apSum_eq_apSum_step_one`.

We do *not* mark this as `[simp]`: our normal forms prefer the step-one presentation.
-/
lemma apSum_step_one_eq_apSum (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f (k * d)) 1 n = apSum f d n := by
  simpa using (apSum_eq_apSum_step_one (f := f) (d := d) (n := n)).symm

/-- Normal form: an offset sum with `m = 0` is just the homogeneous sum `apSum`.

Marked `[simp]` so that normalizing away a spurious `m = 0` offset is automatic.
(We intentionally do *not* simp in the other direction.)
-/
@[simp] lemma apSumOffset_zero_m (f : ℕ → ℤ) (d n : ℕ) : apSumOffset f d 0 n = apSum f d n := by
  unfold apSumOffset apSum
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

/-- Split `apSum` over a sum of lengths: `apSum f d (m + n)` equals the sum over the first `m`
terms plus the sum over the next `n` terms. -/
lemma apSum_add_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) = apSum f d m + apSumOffset f d m n := by
  classical
  unfold apSum apSumOffset
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (fun i => f ((i + 1) * d)) m n)

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

/-- Multiplication by a fixed integer on the left commutes with `apSum`. -/
lemma apSum_mul_left (c : ℤ) (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => c * f k) d n = c * apSum f d n := by
  classical
  unfold apSum
  simp [Finset.mul_sum]

/-- Multiplication by a fixed integer on the right commutes with `apSum`. -/
lemma apSum_mul_right (f : ℕ → ℤ) (c : ℤ) (d n : ℕ) :
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

lemma apSum_zero_d (f : ℕ → ℤ) (n : ℕ) : apSum f 0 n = n • f 0 := by
  classical
  -- along step size 0, the AP is constant at 0
  simp [apSum]

@[simp] lemma apSumOffset_zero_d (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 0 m n = n • f 0 := by
  classical
  unfold apSumOffset
  simp

end MoltResearch
