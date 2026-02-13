import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: affine arithmetic progression sums

(Work in progress.)
-/

namespace MoltResearch

/-- Sum of `f` along the arithmetic progression `a + d, a + 2d, …, a + nd`. -/
def apSumFrom (f : ℕ → ℤ) (a d n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f (a + (i + 1) * d))

@[simp] lemma apSumFrom_zero (f : ℕ → ℤ) (a d : ℕ) :
  apSumFrom f a d 0 = 0 := by
  unfold apSumFrom
  simp

@[simp] lemma apSumFrom_one (f : ℕ → ℤ) (a d : ℕ) :
  apSumFrom f a d 1 = f (a + d) := by
  unfold apSumFrom
  simp

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
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = (Finset.Ico 1 (n + 1)).sum (fun i => f (a + i * d)) := by
            -- `h` is oriented from `Ico` to `range`; we use it backwards.
            simpa [Nat.add_sub_cancel] using h.symm
    _ = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
            simpa [Finset.Ico_add_one_right_eq_Icc]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (a + i*d)` back to
`apSumFrom`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSumFrom (f : ℕ → ℤ) (a d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)).symm

lemma apSumFrom_succ (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d (n + 1) = apSumFrom f a d n + f (a + (n + 1) * d) := by
  unfold apSumFrom
  simpa [Finset.sum_range_succ] using
    (Finset.sum_range_succ (fun i => f (a + (i + 1) * d)) n)

lemma apSum_eq_apSumFrom (f : ℕ → ℤ) (d n : ℕ) :
  apSum f d n = apSumFrom f 0 d n := by
  unfold apSum apSumFrom
  simp [Nat.zero_add]

lemma apSumOffset_eq_apSumFrom (f : ℕ → ℤ) (d m n : ℕ) :
  apSumOffset f d m n = apSumFrom f (m * d) d n := by
  unfold apSumOffset apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  have h : (m + i + 1) * d = m * d + (i + 1) * d := by
    simpa [Nat.add_assoc] using (Nat.add_mul m (i + 1) d)
  simp [h]

/-- Shifted version of `apSumFrom`. -/
lemma apSumFrom_eq_apSum_shift (f : ℕ → ℤ) (a d n : ℕ) :
  apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  unfold apSumFrom apSum
  rfl

lemma apSumFrom_add_length (f : ℕ → ℤ) (a d m n : ℕ) :
  apSumFrom f a d (m + n) = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
  classical
  let g : ℕ → ℤ := fun k => f (a + k)
  have hsplit : apSum g d (m + n) = apSum g d m + apSumOffset g d m n :=
    apSum_add_length (f := g) (d := d) (m := m) (n := n)
  have hL : apSumFrom f a d (m + n) = apSum g d (m + n) := by
    simpa [g] using
      (apSumFrom_eq_apSum_shift (f := f) (a := a) (d := d) (n := m + n))
  have hM : apSum g d m = apSumFrom f a d m := by
    simpa [g] using
      (apSumFrom_eq_apSum_shift (f := f) (a := a) (d := d) (n := m)).symm
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

/-- `f` has affine discrepancy at least `C` if some affine AP partial sum exceeds `C` in absolute
value, with a positive step size `d`.

This is the natural analogue of `HasDiscrepancyAtLeast` where we also allow an offset `a`.
-/
def HasAffineDiscrepancyAtLeast (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∃ a d n : ℕ, d > 0 ∧ Int.natAbs (apSumFrom f a d n) > C

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
    simpa [apSumFrom_eq_apSum_shift] using hgt
  · rintro ⟨a, h⟩
    rcases h with ⟨d, n, hd, hgt⟩
    refine ⟨a, d, n, hd, ?_⟩
    simpa [apSumFrom_eq_apSum_shift] using hgt

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
