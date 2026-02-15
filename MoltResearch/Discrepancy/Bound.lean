import MoltResearch.Discrepancy.AffineTail

/-!
# Discrepancy bounds

This file provides simple triangle‑inequality bounds for the arithmetic‑progression sum
functions defined in `MoltResearch.Discrepancy.Affine`.  Given a uniform bound `B` on the
pointwise `Int.natAbs` of a function `f : ℕ → ℤ`, we show that the absolute value of the
sums is bounded by `n * B`.
-/

namespace MoltResearch

lemma natAbs_apSum_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSum]
  | succ n ih =>
      have hsum :
          Int.natAbs (apSum f d (Nat.succ n)) ≤
            Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) := by
        simpa [apSum_succ] using
          (Int.natAbs_add_le (apSum f d n) (f ((n + 1) * d)))
      have hfn : Int.natAbs (f ((n + 1) * d)) ≤ B := hB ((n + 1) * d)
      have hbound :
          Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) ≤ n * B + B :=
        Nat.add_le_add ih hfn
      have : Int.natAbs (apSum f d (Nat.succ n)) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSumOffset_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hsum :
          Int.natAbs (apSumOffset f d m (Nat.succ n)) ≤
            Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
        simpa [apSumOffset_succ] using
          (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
      have hfn : Int.natAbs (f ((m + n + 1) * d)) ≤ B := hB ((m + n + 1) * d)
      have hbound :
          Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) ≤ n * B + B :=
        Nat.add_le_add ih hfn
      have : Int.natAbs (apSumOffset f d m (Nat.succ n)) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSum_sub_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n * B := by
  have h := natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub] using h

lemma natAbs_apSumFrom_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumFrom]
  | succ n ih =>
      have hsum :
          Int.natAbs (apSumFrom f a d (Nat.succ n)) ≤
            Int.natAbs (apSumFrom f a d n) + Int.natAbs (f (a + (n + 1) * d)) := by
        simpa [apSumFrom_succ] using
          (Int.natAbs_add_le (apSumFrom f a d n) (f (a + (n + 1) * d)))
      have hfn : Int.natAbs (f (a + (n + 1) * d)) ≤ B := hB (a + (n + 1) * d)
      have hbound :
          Int.natAbs (apSumFrom f a d n) + Int.natAbs (f (a + (n + 1) * d)) ≤ n * B + B :=
        Nat.add_le_add ih hfn
      have : Int.natAbs (apSumFrom f a d (Nat.succ n)) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSumFrom_sub_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d m n : ℕ) :
    Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ n * B := by
  have h := natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB)
    (a := a + m * d) (d := d) (n := n)
  simpa [apSumFrom_tail_eq_sub] using h

/-!
## Paper-notation wrappers

The nucleus APIs are `apSum`, `apSumOffset`, and `apSumFrom`. For surface statements it is often
convenient to work with the interval-sum normal forms `(Finset.Icc …).sum (fun i => …)`.

The lemmas below are thin wrappers around the nucleus bounds.
-/

lemma natAbs_sum_Icc_mul_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d n : ℕ) :
    Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) ≤ n * B := by
  simpa [apSum_eq_sum_Icc] using
    (natAbs_apSum_le_mul (f := f) (B := B) (hB := hB) (d := d) (n := n))

lemma natAbs_sum_Icc_mul_offset_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ n * B := by
  simpa [apSumOffset_eq_sum_Icc] using
    (natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m) (n := n))

lemma natAbs_sum_Icc_add_mul_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d n : ℕ) :
    Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) ≤ n * B := by
  simpa [apSumFrom_eq_sum_Icc] using
    (natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a) (d := d) (n := n))

/-!
### Bounds with a variable upper endpoint

Many surface statements (and intermediate steps) naturally produce sums indexed by `Icc (m+1) n`
under a hypothesis `m ≤ n`. The normal forms in `Offset.lean` / `AffineTail.lean` rewrite such
interval sums to tail sums of length `n - m`; the lemmas below are bound wrappers aligned with
those normal forms.
-/

lemma natAbs_apSum_sub_apSum_of_le_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Int.natAbs (apSum f d n - apSum f d m) ≤ (n - m) * B := by
  have h :=
    natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m) (n := n - m)
  simpa [apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn] using h

lemma natAbs_sum_Icc_mul_of_le_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (i * d))) ≤ (n - m) * B := by
  have h :=
    natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m) (n := n - m)
  simpa [sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn] using h

lemma natAbs_apSumFrom_sub_apSumFrom_of_le_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Int.natAbs (apSumFrom f a d n - apSumFrom f a d m) ≤ (n - m) * B := by
  have h :=
    natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a + m * d) (d := d)
      (n := n - m)
  simpa [apSumFrom_tail_eq_sub_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

lemma natAbs_sum_Icc_add_mul_of_le_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ (n - m) * B := by
  have h :=
    natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a + m * d) (d := d)
      (n := n - m)
  simpa [sum_Icc_eq_apSumFrom_tail_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using
    h

/-- Bound a difference of two affine tail sums over the same start `a + m*d` when `n₁ ≤ n₂`.

This is aligned with the canonical tail normal form
`apSumFrom f (a + m*d) d n₂ - apSumFrom f (a + m*d) d n₁ =
  apSumFrom f (a + (m + n₁) * d) d (n₂ - n₁)`.
-/
lemma natAbs_apSumFrom_tail_sub_apSumFrom_tail_of_le_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d m : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    Int.natAbs (apSumFrom f (a + m * d) d n₂ - apSumFrom f (a + m * d) d n₁) ≤ (n₂ - n₁) * B := by
  have hn2 : n₁ + (n₂ - n₁) = n₂ := Nat.add_sub_of_le hn
  have hEq :
      apSumFrom f (a + m * d) d n₂ - apSumFrom f (a + m * d) d n₁ =
        apSumFrom f (a + (m + n₁) * d) d (n₂ - n₁) := by
    simpa [hn2] using
      (apSumFrom_tail_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n1 := n₁)
        (n2 := n₂ - n₁))
  have hTail :
      Int.natAbs (apSumFrom f (a + (m + n₁) * d) d (n₂ - n₁)) ≤ (n₂ - n₁) * B :=
    natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a + (m + n₁) * d) (d := d)
      (n := n₂ - n₁)
  simpa [hEq] using hTail

/-- Bound a difference of two offset sums over the same start `m` when `n₁ ≤ n₂`.

This is the `B`-bounded analogue of `IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le`.
It is aligned with the canonical tail normal form
`apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁)`.
-/
lemma natAbs_apSumOffset_sub_apSumOffset_of_le_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    Int.natAbs (apSumOffset f d m n₂ - apSumOffset f d m n₁) ≤ (n₂ - n₁) * B := by
  have hTail :
      Int.natAbs (apSumOffset f d (m + n₁) (n₂ - n₁)) ≤ (n₂ - n₁) * B :=
    natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m + n₁)
      (n := n₂ - n₁)
  have hEq :
      apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) :=
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)
  simpa [hEq] using hTail

lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one_and_length_mul_bound_gt {f : ℕ → ℤ} {C B : ℕ}
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n * B > C ∧ Int.natAbs (apSum f d n) > C := by
  rcases h.exists_witness_d_ge_one with ⟨d, n, hd, hgt⟩
  have hle : Int.natAbs (apSum f d n) ≤ n * B :=
    natAbs_apSum_le_mul (f := f) (B := B) (hB := hB) (d := d) (n := n)
  have hnB : n * B > C := lt_of_lt_of_le hgt hle
  exact ⟨d, n, hd, hnB, hgt⟩

lemma HasAffineDiscrepancyAtLeast.exists_witness_d_ge_one_and_length_mul_bound_gt {f : ℕ → ℤ} {C B : ℕ}
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n, d ≥ 1 ∧ n * B > C ∧ Int.natAbs (apSumFrom f a d n) > C := by
  rcases h.exists_witness_d_ge_one with ⟨a, d, n, hd, hgt⟩
  have hle : Int.natAbs (apSumFrom f a d n) ≤ n * B :=
    natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a) (d := d) (n := n)
  have hnB : n * B > C := lt_of_lt_of_le hgt hle
  exact ⟨a, d, n, hd, hnB, hgt⟩

end MoltResearch
