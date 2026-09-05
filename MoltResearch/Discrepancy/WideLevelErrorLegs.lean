import MoltResearch.Discrepancy.LevelLegs

/-!
# Wide level error legs

The replacement and repeated-prime errors are collected before applying the
mean value theorem.  Thus the frequency cost is paid at the original scale
`A`, independently of the height of the prime level.
-/

namespace MoltResearch

open Finset

/-! ## Replacement collars -/

/-- The two quotient collars created when the prime-dependent block at `p`
is replaced by the block at the cell scale `q`. -/
def replacementCollar (A B p q : ℕ) : Finset ℕ :=
  Finset.Ioc (A / p) (A / q) ∪ Finset.Ioc (B / p) (B / q)

/-- The signed incidence of a quotient integer in the lower and upper
replacement collars. -/
def replacementCollarSign (A B p q m : ℕ) : ℂ :=
  (if m ∈ Finset.Ioc (A / p) (A / q) then 1 else 0)
    - (if m ∈ Finset.Ioc (B / p) (B / q) then 1 else 0)

/-- A difference of two ordered integer windows is the lower collar minus
the upper collar. -/
theorem sum_Ioc_sub_sum_Ioc_eq_lower_sub_upper {M : Type*} [AddCommGroup M]
    (a b a' b' : ℕ) (hab : a ≤ b) (haa' : a ≤ a')
    (ha'b' : a' ≤ b') (hbb' : b ≤ b') (f : ℕ → M) :
    (∑ m ∈ Finset.Ioc a b, f m) - ∑ m ∈ Finset.Ioc a' b', f m
      = (∑ m ∈ Finset.Ioc a a', f m) - ∑ m ∈ Finset.Ioc b b', f m := by
  rcases le_total a' b with ha'b | hba'
  · rw [← Finset.sum_Ioc_consecutive f haa' ha'b,
      ← Finset.sum_Ioc_consecutive f ha'b hbb']
    abel
  · rw [← Finset.sum_Ioc_consecutive f hab hba',
      ← Finset.sum_Ioc_consecutive f hba' ha'b']
    abel

/-- The collar identity in the indicator form used to collect equal products
`n = p*m`. -/
theorem sum_replacementCollarSign
    (A B p q : ℕ) (hAB : A ≤ B) (hq : 0 < q) (hqp : q ≤ p) (f : ℕ → ℂ) :
    ∑ m ∈ replacementCollar A B p q, replacementCollarSign A B p q m * f m
      = (∑ m ∈ Finset.Ioc (A / p) (B / p), f m)
        - ∑ m ∈ Finset.Ioc (A / q) (B / q), f m := by
  classical
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have hApBp : A / p ≤ B / p := Nat.div_le_div_right hAB
  have hAqBq : A / q ≤ B / q := Nat.div_le_div_right hAB
  have hA : A / p ≤ A / q := Nat.div_le_div_left hqp hq
  have hB : B / p ≤ B / q := Nat.div_le_div_left hqp hq
  rw [sum_Ioc_sub_sum_Ioc_eq_lower_sub_upper _ _ _ _ hApBp hA hAqBq hB]
  let L := Finset.Ioc (A / p) (A / q)
  let U := Finset.Ioc (B / p) (B / q)
  let F : ℕ → ℂ := fun m => replacementCollarSign A B p q m * f m
  have hL : ∑ m ∈ L, F m = (∑ m ∈ L, f m) - ∑ m ∈ L ∩ U, f m := by
    calc
      ∑ m ∈ L, F m
          = ∑ m ∈ L, (f m - if m ∈ U then f m else 0) := by
              refine Finset.sum_congr rfl fun m hm => ?_
              change (((if m ∈ L then 1 else 0) - (if m ∈ U then 1 else 0))
                * f m) = _
              by_cases hmU : m ∈ U <;> simp [hm, hmU]
      _ = (∑ m ∈ L, f m) - ∑ m ∈ L, (if m ∈ U then f m else 0) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ m ∈ L, f m) - ∑ m ∈ L ∩ U, f m := by
              congr 1
              have hinter : L ∩ U = L.filter (fun m => m ∈ U) := by
                ext m
                simp
              rw [hinter]
              exact (Finset.sum_filter (fun m => m ∈ U) f).symm
  have hU : ∑ m ∈ U, F m = (∑ m ∈ L ∩ U, f m) - ∑ m ∈ U, f m := by
    calc
      ∑ m ∈ U, F m
          = ∑ m ∈ U, ((if m ∈ L then f m else 0) - f m) := by
              refine Finset.sum_congr rfl fun m hm => ?_
              change (((if m ∈ L then 1 else 0) - (if m ∈ U then 1 else 0))
                * f m) = _
              by_cases hmL : m ∈ L <;> simp [hm, hmL]
      _ = (∑ m ∈ U, (if m ∈ L then f m else 0)) - ∑ m ∈ U, f m := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ m ∈ L ∩ U, f m) - ∑ m ∈ U, f m := by
              congr 1
              have hinter : L ∩ U = U.filter (fun m => m ∈ L) := by
                ext m
                simp [and_comm]
              rw [hinter]
              exact (Finset.sum_filter (fun m => m ∈ L) f).symm
  have hI : ∑ m ∈ L ∩ U, F m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hmL : m ∈ L := (Finset.mem_inter.mp hm).1
    have hmU : m ∈ U := (Finset.mem_inter.mp hm).2
    change (((if m ∈ L then 1 else 0) - (if m ∈ U then 1 else 0)) * f m) = 0
    simp [hmL, hmU]
  have hunion := Finset.sum_union_inter (s₁ := L) (s₂ := U) (f := F)
  change (∑ m ∈ L ∪ U, F m) = _
  rw [hI, add_zero, hL, hU] at hunion
  change (∑ m ∈ L ∪ U, F m) = (∑ m ∈ L, f m) - ∑ m ∈ U, f m
  rw [hunion]
  abel

/-- One prime's contribution to a collected replacement coefficient. -/
noncomputable def wideReplacementPrimeCoeff (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p q n : ℕ) : ℂ :=
  if p ∣ n ∧ n / p ∈ replacementCollar A B p q then
    replacementCollarSign A B p q (n / p) * g p
      * typicalSQuotCoeff g P (typicalS 0 B rest) (n / p)
  else 0

/-- The coefficient obtained after all cell replacement collars are collected
at their product `n = p*m`. -/
noncomputable def wideReplacementCoeff (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N : ℕ) (q : ℕ → ℕ)
    (n : ℕ) : ℂ :=
  ∑ p ∈ P, wideReplacementPrimeCoeff g A B P rest p
    (q ⌊(2 * N : ℕ) * Real.log p⌋₊) n

/-- The product attached to either replacement collar stays in `(A,2B]`
once the cell representative is below the prime and the cell width is below
two. -/
theorem replacementCollar_product_mem (A B p q m : ℕ) (hAB : A ≤ B)
    (hp : 0 < p) (hq : 0 < q) (hp2q : p ≤ 2 * q)
    (hm : m ∈ replacementCollar A B p q) :
    p * m ∈ Finset.Ioc A (2 * B) := by
  simp only [replacementCollar, Finset.mem_union, Finset.mem_Ioc] at hm
  have hu : m ≤ B / q := by
    rcases hm with hm | hm
    · exact hm.2.trans (Nat.div_le_div_right hAB)
    · exact hm.2
  have hqm : q * m ≤ B := by
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hq).mp hu
  rw [Finset.mem_Ioc]
  constructor
  · rcases hm with hm | hm
    · have := (Nat.div_lt_iff_lt_mul hp).mp hm.1
      simpa [mul_comm] using this
    · have hBm := (Nat.div_lt_iff_lt_mul hp).mp hm.1
      have hBpm : B < p * m := by simpa [mul_comm] using hBm
      exact lt_of_le_of_lt hAB hBpm
  · calc
      p * m ≤ (2 * q) * m := Nat.mul_le_mul_right m hp2q
      _ = 2 * (q * m) := by ring
      _ ≤ 2 * B := Nat.mul_le_mul_left 2 hqm

/-- Two positive integers in the same cell differ by less than a factor two.
The representative need not be prime for this consequence. -/
theorem eadicCell_prime_le_two_rep {P : Finset ℕ} {N v p q : ℕ}
    (hN : 0 < N) (hp : p ∈ eadicCell P (2 * N) v)
    (hq : q ∈ eadicCell P (2 * N) v) (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) :
    p ≤ 2 * q := by
  have hratio := eadicCell_ratio_le hN hp hq hp1 hq1
  have hNstep : N + 1 ≤ 2 * N := by omega
  have hmul : N * p ≤ N * (2 * q) :=
    hratio.trans (by
      calc
        (N + 1) * q ≤ (2 * N) * q := Nat.mul_le_mul_right q hNstep
        _ = N * (2 * q) := by ring)
  exact Nat.le_of_mul_le_mul_left hmul hN

/-- The factor-two consequence only needs the arithmetic ratio bound. -/
theorem prime_le_two_rep_of_ratio {N p q : ℕ} (hN : 0 < N)
    (hratio : N * p ≤ (N + 1) * q) : p ≤ 2 * q := by
  have hNstep : N + 1 ≤ 2 * N := by omega
  have hmul : N * p ≤ N * (2 * q) :=
    hratio.trans (by
      calc
        (N + 1) * q ≤ (2 * N) * q := Nat.mul_le_mul_right q hNstep
        _ = N * (2 * q) := by ring)
  exact Nat.le_of_mul_le_mul_left hmul hN

/-- Before equal products are collected, the replacement error is the sum of
the signed collar polynomials, one for each prime of the level. -/
theorem typicalSCellReplacement_eq_prime_collar_sum
    (g : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (q : ℕ → ℕ)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (xi : ℝ) :
    typicalSCellReplacement g A B P rest N v₀ v₁ q xi
      = ∑ p ∈ P, ∑ m ∈ replacementCollar A B p
          (q ⌊(2 * N : ℕ) * Real.log p⌋₊),
        (replacementCollarSign A B p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊) m
          * g p * typicalSQuotCoeff g P (typicalS 0 B rest) m /
            ((p * m : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ) := by
  classical
  let I := Finset.Ico v₀ (v₁ + 1)
  let c := typicalSQuotCoeff g P (typicalS 0 B rest)
  let F : ℕ → ℕ → ℂ := fun v p =>
    ∑ m ∈ replacementCollar A B p (q v),
      (replacementCollarSign A B p (q v) m * g p * c m /
          ((p * m : ℕ) : ℂ))
        * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ)
  have hcell : ∀ v ∈ I, ∀ p ∈ eadicCell P (2 * N) v,
      ⌊(2 * N : ℕ) * Real.log p⌋₊ = v := by
    intro v hv p hp
    exact (mem_eadicCell.mp hp).2
  have hper : ∀ v ∈ I, ∀ p ∈ eadicCell P (2 * N) v,
      ((g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * ((∑ m ∈ Finset.Ioc (A / p) (B / p),
              (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          - ∑ m ∈ Finset.Ioc (A / q v) (B / q v),
              (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        = F v p := by
    intro v hv p hp
    have hpP := (mem_eadicCell.mp hp).1
    have hp0 := (hP p hpP).pos
    have hq0 : 0 < q v := hq1 v
    rw [← sum_replacementCollarSign A B p (q v) hAB hq0 (hqmin v hv p hp)
      (fun m => (c m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := by
      simp only [replacementCollar, Finset.mem_union, Finset.mem_Ioc] at hm
      rcases hm with hm | hm
      · exact lt_of_le_of_lt (Nat.zero_le _) hm.1
      · exact lt_of_le_of_lt (Nat.zero_le _) hm.1
    rw [char_log_mul p m hp0.ne' hm0.ne' xi]
    push_cast
    field_simp
  have hdisj : (↑I : Set ℕ).PairwiseDisjoint (eadicCell P (2 * N)) := by
    intro v hv w hw hvw
    exact eadicCell_disjoint P (2 * N) hvw
  calc
    typicalSCellReplacement g A B P rest N v₀ v₁ q xi
        = ∑ v ∈ I, ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A / p) (B / p),
                    (c m / (m : ℂ))
                      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
                - ∑ m ∈ Finset.Ioc (A / q v) (B / q v),
                    (c m / (m : ℂ))
                      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)) := by
              rfl
    _ = ∑ v ∈ I, ∑ p ∈ eadicCell P (2 * N) v, F v p := by
          refine Finset.sum_congr rfl fun v hv => ?_
          exact Finset.sum_congr rfl fun p hp => hper v hv p hp
    _ = ∑ v ∈ I, ∑ p ∈ eadicCell P (2 * N) v,
          F ⌊(2 * N : ℕ) * Real.log p⌋₊ p := by
          refine Finset.sum_congr rfl fun v hv => ?_
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hcell v hv p hp]
    _ = ∑ p ∈ I.biUnion (eadicCell P (2 * N)),
          F ⌊(2 * N : ℕ) * Real.log p⌋₊ p :=
          (Finset.sum_biUnion hdisj).symm
    _ = ∑ p ∈ P, F ⌊(2 * N : ℕ) * Real.log p⌋₊ p := by rw [hcov]
    _ = _ := by rfl

/-- A single prime collar can be reindexed from `m` to its product `n=p*m`.
The target is padded to the common support `(A,2B]`. -/
theorem sum_replacement_prime_eq_dirichlet
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p q : ℕ) (hp : 0 < p)
    (hsupp : ∀ m ∈ replacementCollar A B p q,
      p * m ∈ Finset.Ioc A (2 * B)) (xi : ℝ) :
    (∑ m ∈ replacementCollar A B p q,
        (replacementCollarSign A B p q m * g p
            * typicalSQuotCoeff g P (typicalS 0 B rest) m /
              ((p * m : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
      = ∑ n ∈ Finset.Ioc A (2 * B),
          (wideReplacementPrimeCoeff g A B P rest p q n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
  classical
  let S := Finset.Ioc A (2 * B)
  let C := replacementCollar A B p q
  let pred : ℕ → Prop := fun n => p ∣ n ∧ n / p ∈ C
  have htarget : (∑ n ∈ S,
        (wideReplacementPrimeCoeff g A B P rest p q n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ))
      = ∑ n ∈ S.filter pred,
        (replacementCollarSign A B p q (n / p) * g p
            * typicalSQuotCoeff g P (typicalS 0 B rest) (n / p) / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hpred : pred n
    · simp [wideReplacementPrimeCoeff, pred, C, hpred]
    · simp [wideReplacementPrimeCoeff, pred, C, hpred]
  rw [htarget]
  apply Finset.sum_bij (fun m _ => p * m)
  · intro m hm
    rw [Finset.mem_filter]
    have hdiv : p ∣ p * m := Nat.dvd_mul_right p m
    have hquot : (p * m) / p = m := by
      simpa [mul_comm] using Nat.mul_div_left m hp
    exact ⟨hsupp m hm, hdiv, by simpa [C, hquot] using hm⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro n hn
    rw [Finset.mem_filter] at hn
    refine ⟨n / p, hn.2.2, ?_⟩
    exact Nat.mul_div_cancel' hn.2.1
  · intro m hm
    rw [show p * m / p = m by simpa [mul_comm] using Nat.mul_div_left m hp]

open MeasureTheory Finset ExpSums in
/-- **The replacement error is one Dirichlet polynomial.**  The support is
the common interval `(A,2B]`; the coefficient is zero away from the actual
two collars of the contributing prime. -/
theorem typicalSCellReplacement_eq_dirichlet
    (g : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (q : ℕ → ℕ)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
    (xi : ℝ) :
    typicalSCellReplacement g A B P rest N v₀ v₁ q xi
      = ∑ n ∈ Finset.Ioc A (2 * B),
          (wideReplacementCoeff g A B P rest N q n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
  classical
  rw [typicalSCellReplacement_eq_prime_collar_sum g A B hAB P hP rest N
    v₀ v₁ hcov q hq1 hqmin xi]
  let I := Finset.Ico v₀ (v₁ + 1)
  have hsupp : ∀ p ∈ P, ∀ m ∈ replacementCollar A B p
      (q ⌊(2 * N : ℕ) * Real.log p⌋₊),
      p * m ∈ Finset.Ioc A (2 * B) := by
    intro p hpP m hm
    have hpU : p ∈ I.biUnion (eadicCell P (2 * N)) := by
      rw [hcov]
      exact hpP
    rw [Finset.mem_biUnion] at hpU
    obtain ⟨v, hv, hpv⟩ := hpU
    have hidx : ⌊(2 * N : ℕ) * Real.log p⌋₊ = v := (mem_eadicCell.mp hpv).2
    rw [hidx] at hm
    exact replacementCollar_product_mem A B p (q v) m hAB
      (hP p hpP).pos (hq1 v)
      (prime_le_two_rep_of_ratio hN (hqratio v hv p hpv)) hm
  calc
    (∑ p ∈ P, ∑ m ∈ replacementCollar A B p
        (q ⌊(2 * N : ℕ) * Real.log p⌋₊),
      (replacementCollarSign A B p
          (q ⌊(2 * N : ℕ) * Real.log p⌋₊) m
        * g p * typicalSQuotCoeff g P (typicalS 0 B rest) m /
          ((p * m : ℕ) : ℂ))
        * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
        = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A (2 * B),
            (wideReplacementPrimeCoeff g A B P rest p
                (q ⌊(2 * N : ℕ) * Real.log p⌋₊) n / (n : ℂ))
              * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
          refine Finset.sum_congr rfl fun p hpP => ?_
          exact sum_replacement_prime_eq_dirichlet g A B P rest p _
            (hP p hpP).pos (hsupp p hpP) xi
    _ = ∑ n ∈ Finset.Ioc A (2 * B), ∑ p ∈ P,
          (wideReplacementPrimeCoeff g A B P rest p
              (q ⌊(2 * N : ℕ) * Real.log p⌋₊) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
          rw [Finset.sum_comm]
    _ = _ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          unfold wideReplacementCoeff
          rw [Finset.sum_div, Finset.sum_mul]

/-- A signed collar incidence has norm at most one, including on an overlap
where its two incidences cancel. -/
theorem norm_replacementCollarSign_le_one (A B p q m : ℕ) :
    ‖replacementCollarSign A B p q m‖ ≤ 1 := by
  unfold replacementCollarSign
  by_cases hA : m ∈ Finset.Ioc (A / p) (A / q) <;>
    by_cases hB : m ∈ Finset.Ioc (B / p) (B / q) <;>
    simp [hA, hB]

/-- The exact Ramaré denominator bound for a quotient coefficient. -/
theorem norm_typicalSQuotCoeff_le_inv_card_add_one
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (P S : Finset ℕ) (m : ℕ) :
    ‖typicalSQuotCoeff g P S m‖
      ≤ 1 / (((P.filter (· ∣ m)).card : ℝ) + 1) := by
  classical
  unfold typicalSQuotCoeff
  split_ifs with hm
  · rw [norm_div]
    have hden : ‖((P.filter (· ∣ m)).card : ℂ) + 1‖
        = ((P.filter (· ∣ m)).card : ℝ) + 1 := by
      rw [show ((P.filter (· ∣ m)).card : ℂ) + 1 =
          (((P.filter (· ∣ m)).card + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      ring
    rw [hden]
    exact div_le_div_of_nonneg_right (hg m) (by positivity)
  · simp only [norm_zero]
    positivity

/-- Removing one prime from a product loses at most one distinct divisor from
the level. -/
theorem card_filter_dvd_mul_le_add_one (P : Finset ℕ)
    (hP : ∀ r ∈ P, r.Prime) {p : ℕ} (hpP : p ∈ P) (m : ℕ) :
    (P.filter (· ∣ p * m)).card ≤ (P.filter (· ∣ m)).card + 1 := by
  classical
  have hsub : P.filter (· ∣ p * m) ⊆ insert p (P.filter (· ∣ m)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_insert]
    rcases (hP r hr.1).dvd_mul.mp hr.2 with hrp | hrm
    · have hor := (Nat.dvd_prime (hP p hpP)).mp hrp
      rcases hor with hr1 | hrp
      · exact False.elim ((hP r hr.1).ne_one hr1)
      · exact Or.inl hrp
    · exact Or.inr (Finset.mem_filter.mpr ⟨hr.1, hrm⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- **Ramaré collection does not enlarge a replacement coefficient.**  Each
of the `ω_P(n)` possible contributing primes has weight at most
`1/ω_P(n)`. -/
theorem norm_wideReplacementCoeff_le_one
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (A B : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N : ℕ) (q : ℕ → ℕ) (n : ℕ) :
    ‖wideReplacementCoeff g A B P rest N q n‖ ≤ 1 := by
  classical
  let d := (P.filter (· ∣ n)).card
  by_cases hd : d = 0
  · have hnone : ∀ p ∈ P, ¬p ∣ n := by
      intro p hpP hpn
      have : p ∈ P.filter (· ∣ n) := Finset.mem_filter.mpr ⟨hpP, hpn⟩
      rw [Finset.card_eq_zero.mp hd] at this
      exact (by simpa using this)
    unfold wideReplacementCoeff
    have hsum : (∑ p ∈ P, wideReplacementPrimeCoeff g A B P rest p
        (q ⌊(2 * N : ℕ) * Real.log p⌋₊) n) = 0 := by
      apply Finset.sum_eq_zero
      intro p hpP
      simp [wideReplacementPrimeCoeff, hnone p hpP]
    rw [hsum, norm_zero]
    norm_num
  · have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hterm : ∀ p ∈ P,
        ‖wideReplacementPrimeCoeff g A B P rest p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊) n‖
          ≤ if p ∣ n then 1 / (d : ℝ) else 0 := by
      intro p hpP
      by_cases hpn : p ∣ n
      · rw [if_pos hpn]
        by_cases hcoll : n / p ∈ replacementCollar A B p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊)
        · rw [wideReplacementPrimeCoeff, if_pos ⟨hpn, hcoll⟩,
            norm_mul, norm_mul]
          have hp0 := (hP p hpP).pos
          have hprod : p * (n / p) = n := Nat.mul_div_cancel' hpn
          have hcardN : d ≤ (P.filter (· ∣ n / p)).card + 1 := by
            dsimp only [d]
            have hc := card_filter_dvd_mul_le_add_one P hP hpP (n / p)
            simpa only [hprod] using hc
          have hcardR : (d : ℝ) ≤ ((P.filter (· ∣ n / p)).card : ℝ) + 1 := by
            exact_mod_cast hcardN
          have hinv : 1 / (((P.filter (· ∣ n / p)).card : ℝ) + 1)
              ≤ 1 / (d : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hd0]
            simpa only [one_mul] using hcardR
          calc
            ‖replacementCollarSign A B p
                  (q ⌊(2 * N : ℕ) * Real.log p⌋₊) (n / p)‖
                * ‖g p‖ * ‖typicalSQuotCoeff g P (typicalS 0 B rest) (n / p)‖
                ≤ 1 * 1 *
                    (1 / (((P.filter (· ∣ n / p)).card : ℝ) + 1)) := by
                      gcongr
                      · exact norm_replacementCollarSign_le_one A B p _ _
                      · exact hg p
                      · exact norm_typicalSQuotCoeff_le_inv_card_add_one
                          g hg P (typicalS 0 B rest) (n / p)
            _ ≤ 1 / (d : ℝ) := by simpa using hinv
        · rw [wideReplacementPrimeCoeff, if_neg]
          · simp
          · exact fun h => hcoll h.2
      · rw [if_neg hpn, wideReplacementPrimeCoeff, if_neg]
        · simp
        · exact fun h => hpn h.1
    calc
      ‖wideReplacementCoeff g A B P rest N q n‖
          ≤ ∑ p ∈ P, ‖wideReplacementPrimeCoeff g A B P rest p
              (q ⌊(2 * N : ℕ) * Real.log p⌋₊) n‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ p ∈ P, if p ∣ n then 1 / (d : ℝ) else 0 :=
            Finset.sum_le_sum hterm
      _ = (d : ℝ) * (1 / (d : ℝ)) := by
            rw [← Finset.sum_filter]
            simp [d]
      _ = 1 := by field_simp

/-- The coefficient norm is also bounded by the number of collar incidences;
this form is convenient for summing its mass. -/
theorem norm_wideReplacementCoeff_le_count
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N : ℕ) (q : ℕ → ℕ)
    (n : ℕ) :
    ‖wideReplacementCoeff g A B P rest N q n‖
      ≤ ∑ p ∈ P, if p ∣ n ∧ n / p ∈ replacementCollar A B p
          (q ⌊(2 * N : ℕ) * Real.log p⌋₊) then (1 : ℝ) else 0 := by
  classical
  unfold wideReplacementCoeff
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro p hpP
  by_cases h : p ∣ n ∧ n / p ∈ replacementCollar A B p
      (q ⌊(2 * N : ℕ) * Real.log p⌋₊)
  · rw [if_pos h, wideReplacementPrimeCoeff, if_pos h, norm_mul, norm_mul]
    have hsign := norm_replacementCollarSign_le_one A B p
      (q ⌊(2 * N : ℕ) * Real.log p⌋₊) (n / p)
    have hc := norm_typicalSQuotCoeff_le_one g hg P (typicalS 0 B rest) (n / p)
    calc
      ‖replacementCollarSign A B p (q ⌊(2 * N : ℕ) * Real.log p⌋₊) (n / p)‖
            * ‖g p‖ * ‖typicalSQuotCoeff g P (typicalS 0 B rest) (n / p)‖
          ≤ 1 * 1 * 1 := by gcongr; exact hg p
      _ = 1 := by norm_num
  · rw [if_neg h, wideReplacementPrimeCoeff, if_neg h, norm_zero]

/-- The multiples in the common support whose quotient lies in a fixed
collar are no more numerous than that collar. -/
theorem card_filter_replacement_incidence_le (A B p q : ℕ) (hp : 0 < p) :
    ((Finset.Ioc A (2 * B)).filter
      (fun n => p ∣ n ∧ n / p ∈ replacementCollar A B p q)).card
      ≤ (replacementCollar A B p q).card := by
  classical
  let S := (Finset.Ioc A (2 * B)).filter
    (fun n => p ∣ n ∧ n / p ∈ replacementCollar A B p q)
  have hinj : Set.InjOn (fun n => n / p) ↑S := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hd₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hn₁)).2.1
    have hd₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hn₂)).2.1
    calc
      n₁ = p * (n₁ / p) := (Nat.mul_div_cancel' hd₁).symm
      _ = p * (n₂ / p) := by
        simpa only using congrArg (fun k => p * k) heq
      _ = n₂ := Nat.mul_div_cancel' hd₂
  have himg : S.image (fun n => n / p) ⊆ replacementCollar A B p q := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    exact (Finset.mem_filter.mp hn).2.2
  calc
    S.card = (S.image (fun n => n / p)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (replacementCollar A B p q).card := Finset.card_le_card himg

/-- The squared coefficient mass is bounded by the total collar occurrence
count.  This is the exact pre-arithmetic form of `replacement_coeff_mass_le`.
-/
theorem replacement_coeff_mass_le_collars
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (A B : ℕ) (hA : 1 ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N : ℕ) (q : ℕ → ℕ) :
    ∑ n ∈ Finset.Ioc A (2 * B),
        ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ p ∈ P,
          ((replacementCollar A B p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊)).card : ℝ) / (A : ℝ) ^ 2 := by
  classical
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hpoint : ∀ n ∈ Finset.Ioc A (2 * B),
      ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ (∑ p ∈ P, if p ∣ n ∧ n / p ∈ replacementCollar A B p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊) then (1 : ℝ) else 0) /
          (n : ℝ) ^ 2 := by
    intro n hn
    have hc1 := norm_wideReplacementCoeff_le_one g hg A B P hP rest N q n
    have hcc := norm_wideReplacementCoeff_le_count g hg A B P rest N q n
    have hsq : ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2
        ≤ ‖wideReplacementCoeff g A B P rest N q n‖ := by
      nlinarith [norm_nonneg (wideReplacementCoeff g A B P rest N q n)]
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
    exact div_le_div_of_nonneg_right (hsq.trans hcc) (sq_nonneg (n : ℝ))
  calc
    ∑ n ∈ Finset.Ioc A (2 * B),
        ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ioc A (2 * B),
            (∑ p ∈ P, if p ∣ n ∧ n / p ∈ replacementCollar A B p
              (q ⌊(2 * N : ℕ) * Real.log p⌋₊) then (1 : ℝ) else 0) /
              (n : ℝ) ^ 2 := Finset.sum_le_sum hpoint
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A (2 * B),
          (if p ∣ n ∧ n / p ∈ replacementCollar A B p
              (q ⌊(2 * N : ℕ) * Real.log p⌋₊) then (1 : ℝ) else 0) /
            (n : ℝ) ^ 2 := by
          simp_rw [Finset.sum_div]
          rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ P,
          ((replacementCollar A B p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊)).card : ℝ) / (A : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun p hpP => ?_
          simp only [ite_div, zero_div]
          rw [← Finset.sum_filter]
          let C := replacementCollar A B p
            (q ⌊(2 * N : ℕ) * Real.log p⌋₊)
          let S := (Finset.Ioc A (2 * B)).filter
            (fun n => p ∣ n ∧ n / p ∈ C)
          change (∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2)
            ≤ (C.card : ℝ) / (A : ℝ) ^ 2
          calc
            (∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2)
                ≤ (S.card : ℝ) * (1 / (A : ℝ) ^ 2) := by
                  have hsum := Finset.sum_le_card_nsmul S
                    (fun n => (1 : ℝ) / (n : ℝ) ^ 2)
                    (1 / (A : ℝ) ^ 2) (by
                      intro n hn
                      have hnS := (Finset.mem_filter.mp hn).1
                      have hnA : (A : ℝ) ≤ n := by
                        exact_mod_cast (Finset.mem_Ioc.mp hnS).1.le
                      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hA0 hnA
                      rw [div_le_div_iff₀ (sq_pos_of_pos hn0) (sq_pos_of_pos hA0)]
                      nlinarith)
                  simpa [nsmul_eq_mul] using hsum
            _ ≤ (C.card : ℝ) * (1 / (A : ℝ) ^ 2) := by
                  have hcard : (S.card : ℝ) ≤ C.card := by
                    exact_mod_cast card_filter_replacement_incidence_le A B p _
                      (hP p hpP).pos
                  exact mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = _ := by ring

/-- The two collars at one prime have their expected relative width, with two
integer-endpoint errors. -/
theorem card_replacementCollar_le_of_ratio
    (A B N p q : ℕ) (hN : 0 < N) (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (hratio : N * p ≤ (N + 1) * q) :
    (replacementCollar A B p q).card
      ≤ A / (N * p) + 1 + (B / (N * p) + 1) := by
  have hAq := div_le_div_add_div_add_one A N p q hN (by omega) hqp hratio
  have hBq := div_le_div_add_div_add_one B N p q hN (by omega) hqp hratio
  have hcardA : (Finset.Ioc (A / p) (A / q)).card ≤ A / (N * p) + 1 := by
    rw [Nat.card_Ioc]
    generalize A / q = x at hAq ⊢
    generalize A / p = y at hAq ⊢
    generalize A / (N * p) = z at hAq ⊢
    omega
  have hcardB : (Finset.Ioc (B / p) (B / q)).card ≤ B / (N * p) + 1 := by
    rw [Nat.card_Ioc]
    generalize B / q = x at hBq ⊢
    generalize B / p = y at hBq ⊢
    generalize B / (N * p) = z at hBq ⊢
    omega
  unfold replacementCollar
  calc
    (Finset.Ioc (A / p) (A / q) ∪ Finset.Ioc (B / p) (B / q)).card
        ≤ (Finset.Ioc (A / p) (A / q)).card
            + (Finset.Ioc (B / p) (B / q)).card :=
              Finset.card_union_le _ _
    _ ≤ A / (N * p) + 1 + (B / (N * p) + 1) :=
          Nat.add_le_add hcardA hcardB

/-- **Replacement coefficient mass, with no logarithmic loss.**  The constant
`8` absorbs the two collars and their two integer endpoint errors. -/
theorem replacement_coeff_mass_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (q : ℕ → ℕ)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v) :
    ∑ n ∈ Finset.Ioc A (2 * B),
        ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 8 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) /
          ((N : ℝ) * (A : ℝ)) + (P.card : ℝ) / (A : ℝ) ^ 2) := by
  classical
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (replacement_coeff_mass_le_collars g hg A B hA P hP rest N q).trans ?_
  have hper : ∀ p ∈ P,
      ((replacementCollar A B p
          (q ⌊(2 * N : ℕ) * Real.log p⌋₊)).card : ℝ) / (A : ℝ) ^ 2
        ≤ 8 * (1 / ((N : ℝ) * (A : ℝ) * (p : ℝ))
          + 1 / (A : ℝ) ^ 2) := by
    intro p hpP
    have hpU : p ∈ (Finset.Ico v₀ (v₁ + 1)).biUnion
        (eadicCell P (2 * N)) := by rw [hcov]; exact hpP
    rw [Finset.mem_biUnion] at hpU
    obtain ⟨v, hv, hpv⟩ := hpU
    have hidx : ⌊(2 * N : ℕ) * Real.log p⌋₊ = v := (mem_eadicCell.mp hpv).2
    have hp1 := (hP p hpP).one_le
    have hcard := card_replacementCollar_le_of_ratio A B N p (q v) hN
      (hq1 v) (hqmin v hv p hpv) (hqratio v hv p hpv)
    rw [hidx]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
    have hNp0 : (0 : ℝ) < (N * p : ℕ) := by exact_mod_cast Nat.mul_pos hN (hP p hpP).pos
    have hcastA : ((A / (N * p) : ℕ) : ℝ) ≤ (A : ℝ) / (N * p : ℕ) :=
      Nat.cast_div_le
    have hcastB : ((B / (N * p) : ℕ) : ℝ) ≤ (B : ℝ) / (N * p : ℕ) :=
      Nat.cast_div_le
    have hBR : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hB
    have hcardR : ((replacementCollar A B p (q v)).card : ℝ)
        ≤ 3 * (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 2 := by
      have hc : ((replacementCollar A B p (q v)).card : ℝ)
          ≤ ((A / (N * p) : ℕ) : ℝ) + 1
            + (((B / (N * p) : ℕ) : ℝ) + 1) := by exact_mod_cast hcard
      push_cast at hcastA hcastB
      calc
        ((replacementCollar A B p (q v)).card : ℝ)
            ≤ ((A / (N * p) : ℕ) : ℝ) + 1
              + (((B / (N * p) : ℕ) : ℝ) + 1) := hc
        _ ≤ (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 1
              + ((B : ℝ) / ((N : ℝ) * (p : ℝ)) + 1) := by
                gcongr
        _ ≤ 3 * (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 2 := by
                have hBdiv : (B : ℝ) / ((N : ℝ) * (p : ℝ))
                    ≤ (2 * (A : ℝ)) / ((N : ℝ) * (p : ℝ)) :=
                  div_le_div_of_nonneg_right hBR (by positivity)
                calc
                  (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 1
                      + ((B : ℝ) / ((N : ℝ) * (p : ℝ)) + 1)
                      ≤ (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 1
                          + ((2 * (A : ℝ)) / ((N : ℝ) * (p : ℝ)) + 1) := by
                            gcongr
                  _ = 3 * (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 2 := by
                        field_simp
                        ring
    have hscaled : ((replacementCollar A B p (q v)).card : ℝ)
        * ((N : ℝ) * (p : ℝ))
          ≤ 3 * (A : ℝ) + 2 * ((N : ℝ) * (p : ℝ)) := by
      calc
        ((replacementCollar A B p (q v)).card : ℝ) * ((N : ℝ) * (p : ℝ))
            ≤ (3 * (A : ℝ) / ((N : ℝ) * (p : ℝ)) + 2)
                * ((N : ℝ) * (p : ℝ)) :=
              mul_le_mul_of_nonneg_right hcardR (by positivity)
        _ = 3 * (A : ℝ) + 2 * ((N : ℝ) * (p : ℝ)) := by field_simp
    rw [div_le_iff₀ (sq_pos_of_pos hA0)]
    field_simp
    nlinarith
  calc
    ∑ p ∈ P,
        ((replacementCollar A B p
          (q ⌊(2 * N : ℕ) * Real.log p⌋₊)).card : ℝ) / (A : ℝ) ^ 2
        ≤ ∑ p ∈ P, 8 * (1 / ((N : ℝ) * (A : ℝ) * (p : ℝ))
          + 1 / (A : ℝ) ^ 2) := Finset.sum_le_sum hper
    _ = 8 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) /
          ((N : ℝ) * (A : ℝ)) + (P.card : ℝ) / (A : ℝ) ^ 2) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          have hfactor : ∑ p ∈ P, 1 / ((N : ℝ) * (A : ℝ) * (p : ℝ))
              = (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) / ((N : ℝ) * (A : ℝ)) := by
            calc
              ∑ p ∈ P, 1 / ((N : ℝ) * (A : ℝ) * (p : ℝ))
                  = ∑ p ∈ P, ((1 : ℝ) / (p : ℝ)) /
                      ((N : ℝ) * (A : ℝ)) := by
                    refine Finset.sum_congr rfl fun p hpP => ?_
                    field_simp
              _ = _ := (Finset.sum_div P (fun p => (1 : ℝ) / (p : ℝ))
                ((N : ℝ) * (A : ℝ))).symm
          rw [hfactor]
          ring

/-- The harmonic coefficient mass charged by the sharp mean value theorem.
The factor `32` is an explicit conversion of the squared mass bound using the
common support `(A,4A]`; it remains absolute and carries no `log A` loss. -/
theorem replacement_harmonic_coeff_mass_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (q : ℕ → ℕ)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v) :
    ∑ n ∈ Finset.Ioc A (2 * B),
        ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ)
      ≤ 32 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) / (N : ℝ)
          + (P.card : ℝ) / (A : ℝ)) := by
  classical
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hBA : 2 * B ≤ 4 * A := by omega
  have hconvert : ∑ n ∈ Finset.Ioc A (2 * B),
      ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ)
        ≤ 4 * (A : ℝ) * ∑ n ∈ Finset.Ioc A (2 * B),
            ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
    have hn4A : (n : ℝ) ≤ 4 * (A : ℝ) := by
      exact_mod_cast (le_trans (Finset.mem_Ioc.mp hn).2 hBA)
    have hc0 : 0 ≤ ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 := sq_nonneg _
    field_simp
    nlinarith
  refine hconvert.trans ?_
  have hmass := replacement_coeff_mass_le g hg A B hA hB P hP rest N v₀ v₁
    hN hcov q hq1 hqmin hqratio
  calc
    4 * (A : ℝ) * ∑ n ∈ Finset.Ioc A (2 * B),
        ‖wideReplacementCoeff g A B P rest N q n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ 4 * (A : ℝ) *
            (8 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) /
              ((N : ℝ) * (A : ℝ)) + (P.card : ℝ) / (A : ℝ) ^ 2)) := by
          gcongr
    _ = 32 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) / (N : ℝ)
          + (P.card : ℝ) / (A : ℝ)) := by field_simp; ring

/-- Closed-form wide replacement energy. -/
noncomputable def replacementEnergyBoundWide (A : ℕ) (P : Finset ℕ)
    (N : ℕ) (T : ℝ) : ℝ :=
  Real.exp Real.pi * (T / (A : ℝ) + 8)
    * (32 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) / (N : ℝ)
      + (P.card : ℝ) / (A : ℝ)))

open MeasureTheory Finset ExpSums in
/-- **One mean value application bounds the whole replacement error.** -/
theorem intervalIntegral_norm_sq_typicalSCellReplacement_wide_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (q : ℕ → ℕ)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T,
        ‖typicalSCellReplacement g A B P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ replacementEnergyBoundWide A P N T := by
  classical
  let S := Finset.Ioc A (2 * B)
  let c := wideReplacementCoeff g A B P rest N q
  have hS : S ⊆ Finset.Ioc A (4 * A) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (by omega)⟩
  have hmvt := intervalIntegral_norm_sq_poly_le_sharp_ratio A 4 hA
    (by norm_num) S hS c T hT
  rw [intervalIntegral.integral_congr (fun xi _ =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (typicalSCellReplacement_eq_dirichlet g A B hAB P hP rest N v₀ v₁ hN
        hcov q hq1 hqmin hqratio xi))]
  refine hmvt.trans ?_
  unfold replacementEnergyBoundWide
  dsimp only [S, c]
  norm_num
  refine mul_le_mul_of_nonneg_left ?_
    (show (0 : ℝ) ≤ Real.exp Real.pi * (T / (A : ℝ) + 8) by positivity)
  simpa only [one_div] using
    (replacement_harmonic_coeff_mass_le g hg A B hA hB P hP rest N v₀ v₁
      hN hcov q hq1 hqmin hqratio)

open MeasureTheory Finset ExpSums in
/-- Set-integral form of the wide replacement estimate. -/
theorem setIntegral_norm_sq_typicalSCellReplacement_wide_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (q : ℕ → ℕ)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ xi in G,
        ‖typicalSCellReplacement g A B P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ replacementEnergyBoundWide A P N T := by
  have hmono := setIntegral_le_intervalIntegral_of_nonneg
    (fun xi => ‖typicalSCellReplacement g A B P rest N v₀ v₁ q xi‖ ^ 2)
    ((continuous_typicalSCellReplacement g A B P rest N v₀ v₁ q).norm.pow 2)
    (fun xi => sq_nonneg _) T hT.le G hGT
  exact hmono.trans
    (intervalIntegral_norm_sq_typicalSCellReplacement_wide_le g hg A B hA hAB
      hB P hP rest N v₀ v₁ hN hcov q hq1 hqmin hqratio T hT)

/-! ## Repeated-prime collisions -/

/-- One square-divisor contribution to the collision coefficient. -/
noncomputable def wideCollisionPrimeCoeff (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p n : ℕ) : ℂ :=
  if n ∈ typicalS A B rest ∧ p * p ∣ n then
    g n / ((P.filter (· ∣ n)).card : ℂ)
  else 0

/-- The collision coefficient after all repeated-prime fibres are collected
at `n`. -/
noncomputable def wideCollisionCoeff (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (n : ℕ) : ℂ :=
  ∑ p ∈ P, wideCollisionPrimeCoeff g A B P rest p n

/-- Extracting one copy of a positive divisor turns square divisibility into
divisibility of the quotient. -/
theorem mul_self_dvd_iff_dvd_div {p n : ℕ} (hp : 0 < p) :
    p * p ∣ n ↔ p ∣ n ∧ p ∣ n / p := by
  constructor
  · rintro ⟨k, rfl⟩
    constructor
    · exact ⟨p * k, by ring⟩
    · have hquot : p * p * k / p = p * k := by
        rw [show p * p * k = (p * k) * p by ring, Nat.mul_div_left (p * k) hp]
      rw [hquot]
      exact Nat.dvd_mul_right p k
  · rintro ⟨hpn, hpq⟩
    obtain ⟨k, hk⟩ := hpq
    have hn : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    refine ⟨k, ?_⟩
    calc
      n = p * (n / p) := hn
      _ = p * (p * k) := by rw [hk]
      _ = p * p * k := by ring

/-- A single repeated-prime fibre reindexes exactly to the integers in the
typical support divisible by `p²`. -/
theorem sum_collision_fibre_eq_dirichlet
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) (hp : 0 < p) (xi : ℝ) :
    (∑ m ∈ (((typicalS A B rest).filter
        (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
      ((g (p * m) / ((p * m : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
        / (((P.filter (· ∣ (p * m))).card : ℂ)))
      = ∑ n ∈ Finset.Ioc A B,
          (wideCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
  classical
  let S := typicalS A B rest
  let M := ((S.filter (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m)
  let D := (Finset.Ioc A B).filter (fun n => n ∈ S ∧ p * p ∣ n)
  have hSD : S ⊆ Finset.Ioc A B := typicalS_subset_Ioc A B rest
  have htarget : (∑ n ∈ Finset.Ioc A B,
        (wideCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ))
      = ∑ n ∈ D,
          ((g n / ((P.filter (· ∣ n)).card : ℂ)) / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases h : n ∈ S ∧ p * p ∣ n
    · change ((if n ∈ S ∧ p * p ∣ n then
          g n / ((P.filter (· ∣ n)).card : ℂ) else 0) / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)
        = if n ∈ S ∧ p * p ∣ n then
          ((g n / ((P.filter (· ∣ n)).card : ℂ)) / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) else 0
      simp [h]
    · change ((if n ∈ S ∧ p * p ∣ n then
          g n / ((P.filter (· ∣ n)).card : ℂ) else 0) / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)
        = if n ∈ S ∧ p * p ∣ n then
          ((g n / ((P.filter (· ∣ n)).card : ℂ)) / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) else 0
      simp [h]
  rw [htarget]
  change (∑ m ∈ M,
      ((g (p * m) / ((p * m : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ)) /
        (((P.filter (· ∣ (p * m))).card : ℂ))) = _
  apply Finset.sum_bij (fun m _ => p * m)
  · intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter]
    have hmimg := hm.1
    rw [Finset.mem_image] at hmimg
    obtain ⟨n, hn, hnm⟩ := hmimg
    have hpn := (Finset.mem_filter.mp hn).2
    have hnS := (Finset.mem_filter.mp hn).1
    have hnprod : p * m = n := by
      rw [← hnm]
      exact Nat.mul_div_cancel' hpn
    have hpmS : p * m ∈ S := by simpa only [hnprod] using hnS
    have hquot : (p * m) / p = m := by
      simpa [mul_comm] using Nat.mul_div_left m hp
    have hsq : p * p ∣ p * m := (mul_self_dvd_iff_dvd_div hp).2
      ⟨Nat.dvd_mul_right p m, by simpa only [hquot] using hm.2⟩
    exact ⟨hSD hpmS, hpmS, hsq⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro n hn
    rw [Finset.mem_filter] at hn
    have hsq := (mul_self_dvd_iff_dvd_div hp).1 hn.2.2
    refine ⟨n / p, ?_, Nat.mul_div_cancel' hsq.1⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hsq.2⟩
    rw [Finset.mem_image]
    exact ⟨n, Finset.mem_filter.mpr ⟨hn.2.1, hsq.1⟩, rfl⟩
  · intro m hm
    field_simp

open MeasureTheory Finset ExpSums in
/-- **The collision is one Dirichlet polynomial on `(A,B]`.** -/
theorem typicalSCollision_eq_dirichlet
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (rest : List (Finset ℕ)) (xi : ℝ) :
    typicalSCollision g A B P rest xi
      = ∑ n ∈ Finset.Ioc A B,
          (wideCollisionCoeff g A B P rest n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
  classical
  unfold typicalSCollision
  calc
    (∑ p ∈ P, ∑ m ∈ (((typicalS A B rest).filter
        (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
      ((g (p * m) / ((p * m : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ)) /
        (((P.filter (· ∣ (p * m))).card : ℂ)))
        = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A B,
            (wideCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
              * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
          refine Finset.sum_congr rfl fun p hpP => ?_
          exact sum_collision_fibre_eq_dirichlet g A B P rest p (hP p hpP).pos xi
    _ = ∑ n ∈ Finset.Ioc A B, ∑ p ∈ P,
          (wideCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
          rw [Finset.sum_comm]
    _ = _ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          unfold wideCollisionCoeff
          rw [Finset.sum_div, Finset.sum_mul]

/-- Every square-divisor prime is in particular a divisor prime. -/
theorem filter_mul_self_dvd_subset_filter_dvd (P : Finset ℕ) (n : ℕ) :
    P.filter (fun p => p * p ∣ n) ⊆ P.filter (· ∣ n) := by
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, dvd_trans (Nat.dvd_mul_right p p) hp.2⟩

/-- The collected collision coefficient is bounded by one: the number of
square-divisor primes is at most the Ramaré divisor count in its denominator.
-/
theorem norm_wideCollisionCoeff_le_one
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (n : ℕ) :
    ‖wideCollisionCoeff g A B P rest n‖ ≤ 1 := by
  classical
  let d := (P.filter (· ∣ n)).card
  by_cases hnS : n ∈ typicalS A B rest
  · by_cases hd : d = 0
    · have hnone : ∀ p ∈ P, ¬p * p ∣ n := by
        intro p hpP hsquare
        have hpd : p ∈ P.filter (· ∣ n) := Finset.mem_filter.mpr
          ⟨hpP, dvd_trans (Nat.dvd_mul_right p p) hsquare⟩
        have hempty : P.filter (· ∣ n) = ∅ := Finset.card_eq_zero.mp hd
        rw [hempty] at hpd
        simpa using hpd
      unfold wideCollisionCoeff
      have hsum : (∑ p ∈ P, wideCollisionPrimeCoeff g A B P rest p n) = 0 := by
        apply Finset.sum_eq_zero
        intro p hpP
        simp [wideCollisionPrimeCoeff, hnS, hnone p hpP]
      rw [hsum, norm_zero]
      norm_num
    · have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hterm : ∀ p ∈ P, ‖wideCollisionPrimeCoeff g A B P rest p n‖
          ≤ if p * p ∣ n then 1 / (d : ℝ) else 0 := by
        intro p hpP
        by_cases hsq : p * p ∣ n
        · rw [if_pos hsq, wideCollisionPrimeCoeff, if_pos ⟨hnS, hsq⟩,
            norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_right (hg n) (by positivity)
        · rw [if_neg hsq, wideCollisionPrimeCoeff, if_neg, norm_zero]
          exact fun h => hsq h.2
      have hcard : (P.filter (fun p => p * p ∣ n)).card ≤ d := by
        dsimp only [d]
        exact Finset.card_le_card (filter_mul_self_dvd_subset_filter_dvd P n)
      calc
        ‖wideCollisionCoeff g A B P rest n‖
            ≤ ∑ p ∈ P, ‖wideCollisionPrimeCoeff g A B P rest p n‖ :=
              norm_sum_le _ _
        _ ≤ ∑ p ∈ P, if p * p ∣ n then 1 / (d : ℝ) else 0 :=
              Finset.sum_le_sum hterm
        _ = ((P.filter (fun p => p * p ∣ n)).card : ℝ) * (1 / (d : ℝ)) := by
              rw [← Finset.sum_filter]
              simp
        _ ≤ (d : ℝ) * (1 / (d : ℝ)) := by
              gcongr
        _ = 1 := by field_simp
  · unfold wideCollisionCoeff
    have hsum : (∑ p ∈ P, wideCollisionPrimeCoeff g A B P rest p n) = 0 := by
      apply Finset.sum_eq_zero
      intro p hpP
      simp [wideCollisionPrimeCoeff, hnS]
    rw [hsum, norm_zero]
    norm_num

/-- A cruder incidence-count form used for coefficient-mass estimates. -/
theorem norm_wideCollisionCoeff_le_count
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (n : ℕ) :
    ‖wideCollisionCoeff g A B P rest n‖
      ≤ ∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0 := by
  classical
  unfold wideCollisionCoeff
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro p hpP
  by_cases hS : n ∈ typicalS A B rest ∧ p * p ∣ n
  · rw [wideCollisionPrimeCoeff, if_pos hS, if_pos hS.2, norm_div,
      Complex.norm_natCast]
    have hpdiv : p ∈ P.filter (· ∣ n) := Finset.mem_filter.mpr
      ⟨hpP, dvd_trans (Nat.dvd_mul_right p p) hS.2⟩
    have hcard : 1 ≤ (P.filter (· ∣ n)).card := Finset.card_pos.mpr ⟨p, hpdiv⟩
    rw [div_le_one (by positivity)]
    exact (hg n).trans (by exact_mod_cast hcard)
  · rw [wideCollisionPrimeCoeff, if_neg hS]
    by_cases hsq : p * p ∣ n
    · rw [if_pos hsq, norm_zero]
      norm_num
    · rw [if_neg hsq, norm_zero]

/-- Square-divisible integers in a dyadic block have the expected reciprocal
square mass. -/
theorem sum_one_div_sq_filter_mul_self_dvd_le
    (A B p : ℕ) (hA : 1 ≤ A) (hp : 0 < p) (hB : B ≤ 2 * A) :
    ∑ n ∈ (Finset.Ioc A B).filter (fun n => p * p ∣ n),
        (1 : ℝ) / (n : ℝ) ^ 2
      ≤ 2 / ((A : ℝ) * (p : ℝ) ^ 2) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  let S := (Finset.Ioc A B).filter (fun n => p * p ∣ n)
  have hsum := Finset.sum_le_card_nsmul S
    (fun n => (1 : ℝ) / (n : ℝ) ^ 2) (1 / (A : ℝ) ^ 2) (by
      intro n hn
      have hnI := (Finset.mem_filter.mp hn).1
      have hnA : (A : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hnI).1.le
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hA0 hnA
      rw [div_le_div_iff₀ (sq_pos_of_pos hn0) (sq_pos_of_pos hA0)]
      nlinarith)
  have hcard := card_filter_dvd_le_div A B (Finset.Ioc A B)
    (fun n hn => hn) (Nat.mul_pos hp hp)
  have hBR : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hB
  calc
    ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2
        ≤ (S.card : ℝ) * (1 / (A : ℝ) ^ 2) := by
          simpa [nsmul_eq_mul] using hsum
    _ ≤ ((B : ℝ) / (p * p : ℕ)) * (1 / (A : ℝ) ^ 2) := by
          gcongr
    _ ≤ ((2 * (A : ℝ)) / ((p : ℝ) ^ 2)) * (1 / (A : ℝ) ^ 2) := by
          have hden : ((p * p : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; ring
          rw [hden]
          gcongr
    _ = 2 / ((A : ℝ) * (p : ℝ) ^ 2) := by field_simp

/-- The harmonic-mass companion of
`sum_one_div_sq_filter_mul_self_dvd_le`. -/
theorem sum_one_div_filter_mul_self_dvd_le
    (A B p : ℕ) (hA : 1 ≤ A) (hp : 0 < p) (hB : B ≤ 2 * A) :
    ∑ n ∈ (Finset.Ioc A B).filter (fun n => p * p ∣ n),
        (1 : ℝ) / (n : ℝ)
      ≤ 2 / (p : ℝ) ^ 2 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  let S := (Finset.Ioc A B).filter (fun n => p * p ∣ n)
  have hsum := Finset.sum_le_card_nsmul S
    (fun n => (1 : ℝ) / (n : ℝ)) (1 / (A : ℝ)) (by
      intro n hn
      have hnI := (Finset.mem_filter.mp hn).1
      have hnA : (A : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hnI).1.le
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hA0 hnA
      exact one_div_le_one_div_of_le hA0 hnA)
  have hcard := card_filter_dvd_le_div A B (Finset.Ioc A B)
    (fun n hn => hn) (Nat.mul_pos hp hp)
  have hBR : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hB
  calc
    ∑ n ∈ S, (1 : ℝ) / (n : ℝ)
        ≤ (S.card : ℝ) * (1 / (A : ℝ)) := by
          simpa [nsmul_eq_mul] using hsum
    _ ≤ ((B : ℝ) / (p * p : ℕ)) * (1 / (A : ℝ)) := by
          gcongr
    _ ≤ ((2 * (A : ℝ)) / ((p : ℝ) ^ 2)) * (1 / (A : ℝ)) := by
          have hden : ((p * p : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; ring
          rw [hden]
          gcongr
    _ = 2 / (p : ℝ) ^ 2 := by field_simp

/-- **Collision coefficient mass.**  The only support loss is the density of
square multiples; no prime-by-prime mean value factor appears. -/
theorem collision_coeff_mass_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) :
    ∑ n ∈ Finset.Ioc A B,
        ‖wideCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ (2 / (A : ℝ)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
          + (P.card : ℝ) / (A : ℝ) ^ 2 := by
  classical
  have hpoint : ∀ n ∈ Finset.Ioc A B,
      ‖wideCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ (∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) ^ 2 := by
    intro n hn
    have hc1 := norm_wideCollisionCoeff_le_one g hg A B P rest n
    have hcc := norm_wideCollisionCoeff_le_count g hg A B P rest n
    have hsq : ‖wideCollisionCoeff g A B P rest n‖ ^ 2
        ≤ ‖wideCollisionCoeff g A B P rest n‖ := by
      nlinarith [norm_nonneg (wideCollisionCoeff g A B P rest n)]
    exact div_le_div_of_nonneg_right (hsq.trans hcc) (sq_nonneg (n : ℝ))
  calc
    ∑ n ∈ Finset.Ioc A B,
        ‖wideCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ioc A B,
            (∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) ^ 2 :=
              Finset.sum_le_sum hpoint
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A B,
          (if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) ^ 2 := by
          simp_rw [Finset.sum_div]
          rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ n ∈ (Finset.Ioc A B).filter (fun n => p * p ∣ n),
          (1 : ℝ) / (n : ℝ) ^ 2 := by
          refine Finset.sum_congr rfl fun p hpP => ?_
          simp only [ite_div, zero_div]
          exact (Finset.sum_filter (fun n => p * p ∣ n)
            (fun n => (1 : ℝ) / (n : ℝ) ^ 2)).symm
    _ ≤ ∑ p ∈ P, 2 / ((A : ℝ) * (p : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun p hpP => ?_
          exact sum_one_div_sq_filter_mul_self_dvd_le A B p hA
            (hP p hpP).pos hB
    _ = (2 / (A : ℝ)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hpP => ?_
          ring
    _ ≤ (2 / (A : ℝ)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
          + (P.card : ℝ) / (A : ℝ) ^ 2 :=
            le_add_of_nonneg_right (by positivity)

/-- Harmonic mass of the collected collision coefficient, in the form charged
by the sharp mean value theorem. -/
theorem collision_harmonic_coeff_mass_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) :
    ∑ n ∈ Finset.Ioc A B,
        ‖wideCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ)
      ≤ 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
          + (P.card : ℝ) / (A : ℝ) := by
  classical
  have hpoint : ∀ n ∈ Finset.Ioc A B,
      ‖wideCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ)
        ≤ (∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) := by
    intro n hn
    have hc1 := norm_wideCollisionCoeff_le_one g hg A B P rest n
    have hcc := norm_wideCollisionCoeff_le_count g hg A B P rest n
    have hsq : ‖wideCollisionCoeff g A B P rest n‖ ^ 2
        ≤ ‖wideCollisionCoeff g A B P rest n‖ := by
      nlinarith [norm_nonneg (wideCollisionCoeff g A B P rest n)]
    exact div_le_div_of_nonneg_right (hsq.trans hcc) (Nat.cast_nonneg n)
  calc
    ∑ n ∈ Finset.Ioc A B,
        ‖wideCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ)
        ≤ ∑ n ∈ Finset.Ioc A B,
            (∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) :=
              Finset.sum_le_sum hpoint
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A B,
          (if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) := by
          simp_rw [Finset.sum_div]
          rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ n ∈ (Finset.Ioc A B).filter (fun n => p * p ∣ n),
          (1 : ℝ) / (n : ℝ) := by
          refine Finset.sum_congr rfl fun p hpP => ?_
          simp only [ite_div, zero_div]
          exact (Finset.sum_filter (fun n => p * p ∣ n)
            (fun n => (1 : ℝ) / (n : ℝ))).symm
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun p hpP => ?_
          exact sum_one_div_filter_mul_self_dvd_le A B p hA (hP p hpP).pos hB
    _ = 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hpP => ?_
          ring
    _ ≤ 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
          + (P.card : ℝ) / (A : ℝ) := le_add_of_nonneg_right (by positivity)

/-- The closed-form one-polynomial collision envelope. -/
noncomputable def collisionEnergyBoundWide (A : ℕ) (P : Finset ℕ)
    (T : ℝ) : ℝ :=
  Real.exp Real.pi * (T / (A : ℝ) + 4)
    * (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
      + (P.card : ℝ) / (A : ℝ))

open MeasureTheory Finset ExpSums in
/-- One sharp mean value application bounds the whole collision polynomial. -/
theorem intervalIntegral_norm_sq_typicalSCollision_wide_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖typicalSCollision g A B P rest xi‖ ^ 2)
      ≤ collisionEnergyBoundWide A P T := by
  classical
  let S := Finset.Ioc A B
  let c := wideCollisionCoeff g A B P rest
  have hS : S ⊆ Finset.Ioc A (2 * A) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hB⟩
  have hmvt := intervalIntegral_norm_sq_poly_le_sharp_ratio A 2 hA
    (by norm_num) S hS c T hT
  rw [intervalIntegral.integral_congr (fun xi _ =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (typicalSCollision_eq_dirichlet g A B P hP rest xi))]
  refine hmvt.trans ?_
  unfold collisionEnergyBoundWide
  dsimp only [S, c]
  norm_num
  refine mul_le_mul_of_nonneg_left ?_
    (show (0 : ℝ) ≤ Real.exp Real.pi * (T / (A : ℝ) + 4) by positivity)
  simpa only [one_div] using
    (collision_harmonic_coeff_mass_le g hg A B hA hB P hP rest)

/-- Capstone-facing name for the single-polynomial collision estimate. -/
theorem collision_energy_single_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖typicalSCollision g A B P rest xi‖ ^ 2)
      ≤ collisionEnergyBoundWide A P T :=
  intervalIntegral_norm_sq_typicalSCollision_wide_le g hg A B hA hB
    P hP rest T hT

open MeasureTheory Finset ExpSums in
/-- Set-integral form of the one-polynomial collision bound. -/
theorem setIntegral_norm_sq_typicalSCollision_wide_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ xi in G, ‖typicalSCollision g A B P rest xi‖ ^ 2)
      ≤ collisionEnergyBoundWide A P T := by
  have hmono := setIntegral_le_intervalIntegral_of_nonneg
    (fun xi => ‖typicalSCollision g A B P rest xi‖ ^ 2)
    ((continuous_typicalSCollision g A B P rest).norm.pow 2)
    (fun xi => sq_nonneg _) T hT.le G hGT
  exact hmono.trans
    (intervalIntegral_norm_sq_typicalSCollision_wide_le g hg A B hA hB
      P hP rest T hT)

/-! ### The compensating collision family -/

/-- One prime's coefficient in the full-block compensating family. -/
noncomputable def wideAddedCollisionPrimeCoeff (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p n : ℕ) : ℂ :=
  if n ∈ typicalS A B rest ∧ p * p ∣ n then
    (g p * g (n / p)) / ((((P.filter (· ∣ (n / p))).card : ℂ) + 1))
  else 0

/-- The compensating coefficient after its repeated-prime fibres are
collected at `n`. -/
noncomputable def wideAddedCollisionCoeff (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (n : ℕ) : ℂ :=
  ∑ p ∈ P, wideAddedCollisionPrimeCoeff g A B P rest p n

/-- One compensating fibre is a polynomial on the square-divisible part of
the original support. -/
theorem sum_addedCollision_fibre_eq_dirichlet
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) (hp : 0 < p) (xi : ℝ) :
    (((g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * ∑ m ∈ (((typicalS A B rest).filter
            (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
          ((g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
            / (((P.filter (· ∣ m)).card : ℂ) + 1))
      = ∑ n ∈ Finset.Ioc A B,
          (wideAddedCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
  classical
  let S := typicalS A B rest
  let M := ((S.filter (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m)
  let D := (Finset.Ioc A B).filter (fun n => n ∈ S ∧ p * p ∣ n)
  have hSD : S ⊆ Finset.Ioc A B := typicalS_subset_Ioc A B rest
  have htarget : (∑ n ∈ Finset.Ioc A B,
        (wideAddedCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ))
      = ∑ n ∈ D,
          (((g p * g (n / p)) /
              ((((P.filter (· ∣ (n / p))).card : ℂ) + 1))) / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases h : n ∈ S ∧ p * p ∣ n
    · change ((if n ∈ S ∧ p * p ∣ n then
          (g p * g (n / p)) / ((((P.filter (· ∣ (n / p))).card : ℂ) + 1))
          else 0) / (n : ℂ)) * _ = if n ∈ S ∧ p * p ∣ n then _ else 0
      simp [h]
    · change ((if n ∈ S ∧ p * p ∣ n then
          (g p * g (n / p)) / ((((P.filter (· ∣ (n / p))).card : ℂ) + 1))
          else 0) / (n : ℂ)) * _ = if n ∈ S ∧ p * p ∣ n then _ else 0
      simp [h]
  rw [htarget]
  rw [Finset.mul_sum]
  change (∑ m ∈ M,
      ((g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * (((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)) /
              (((P.filter (· ∣ m)).card : ℂ) + 1))) = _
  apply Finset.sum_bij (fun m _ => p * m)
  · intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_filter]
    have hmimg := hm.1
    rw [Finset.mem_image] at hmimg
    obtain ⟨n, hn, hnm⟩ := hmimg
    have hpn := (Finset.mem_filter.mp hn).2
    have hnS := (Finset.mem_filter.mp hn).1
    have hnprod : p * m = n := by
      rw [← hnm]
      exact Nat.mul_div_cancel' hpn
    have hpmS : p * m ∈ S := by simpa only [hnprod] using hnS
    have hquot : (p * m) / p = m := by
      simpa [mul_comm] using Nat.mul_div_left m hp
    have hsq : p * p ∣ p * m := (mul_self_dvd_iff_dvd_div hp).2
      ⟨Nat.dvd_mul_right p m, by simpa only [hquot] using hm.2⟩
    exact ⟨hSD hpmS, hpmS, hsq⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro n hn
    rw [Finset.mem_filter] at hn
    have hsq := (mul_self_dvd_iff_dvd_div hp).1 hn.2.2
    refine ⟨n / p, ?_, Nat.mul_div_cancel' hsq.1⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hsq.2⟩
    rw [Finset.mem_image]
    exact ⟨n, Finset.mem_filter.mpr ⟨hn.2.1, hsq.1⟩, rfl⟩
  · intro m hm
    have hm0 : 0 < m := by
      rw [Finset.mem_filter] at hm
      have hmimg := hm.1
      rw [Finset.mem_image] at hmimg
      obtain ⟨n, hn, hnm⟩ := hmimg
      have hnI := typicalS_subset_Ioc A B rest (Finset.mem_filter.mp hn).1
      have hpn := (Finset.mem_filter.mp hn).2
      have hnprod : p * m = n := by rw [← hnm]; exact Nat.mul_div_cancel' hpn
      have : 0 < p * m := by simpa only [hnprod] using
        (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hnI).1)
      exact Nat.pos_of_mul_pos_left this
    rw [show (p * m) / p = m by
      simpa [mul_comm] using Nat.mul_div_left m hp,
      char_log_mul p m hp.ne' hm0.ne' xi]
    push_cast
    field_simp

open Finset in
/-- The whole compensating family is one polynomial on `(A,B]`. -/
theorem typicalSAddedTerms_eq_dirichlet
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (xi : ℝ) :
    typicalSAddedTerms g A B P rest N v₀ v₁ xi
      = ∑ n ∈ Finset.Ioc A B,
          (wideAddedCollisionCoeff g A B P rest n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
  classical
  let I := Finset.Ico v₀ (v₁ + 1)
  let F : ℕ → ℂ := fun p =>
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ∑ m ∈ (((typicalS A B rest).filter
          (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)) /
          (((P.filter (· ∣ m)).card : ℂ) + 1)
  have hdisj : (↑I : Set ℕ).PairwiseDisjoint (eadicCell P (2 * N)) := by
    intro v hv w hw hvw
    exact eadicCell_disjoint P (2 * N) hvw
  calc
    typicalSAddedTerms g A B P rest N v₀ v₁ xi
        = ∑ v ∈ I, ∑ p ∈ eadicCell P (2 * N) v, F p := by rfl
    _ = ∑ p ∈ I.biUnion (eadicCell P (2 * N)), F p :=
          (Finset.sum_biUnion hdisj).symm
    _ = ∑ p ∈ P, F p := by rw [hcov]
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A B,
          (wideAddedCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
          refine Finset.sum_congr rfl fun p hpP => ?_
          exact sum_addedCollision_fibre_eq_dirichlet g A B P rest p
            (hP p hpP).pos xi
    _ = ∑ n ∈ Finset.Ioc A B, ∑ p ∈ P,
          (wideAddedCollisionPrimeCoeff g A B P rest p n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) := by
          rw [Finset.sum_comm]
    _ = _ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          unfold wideAddedCollisionCoeff
          rw [Finset.sum_div, Finset.sum_mul]

/-- If the extracted prime already divides the quotient, multiplying by it
does not change the set of distinct level-prime divisors. -/
theorem filter_dvd_mul_eq_of_dvd (P : Finset ℕ)
    (hP : ∀ r ∈ P, r.Prime) {p m : ℕ} (hpP : p ∈ P) (hpm : p ∣ m) :
    P.filter (· ∣ p * m) = P.filter (· ∣ m) := by
  ext r
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hrP, hr⟩
    refine ⟨hrP, ?_⟩
    rcases (hP r hrP).dvd_mul.mp hr with hrp | hrm
    · rcases (Nat.dvd_prime (hP p hpP)).mp hrp with hr1 | hrp
      · exact False.elim ((hP r hrP).ne_one hr1)
      · simpa only [hrp] using hpm
    · exact hrm
  · rintro ⟨hrP, hrm⟩
    exact ⟨hrP, dvd_mul_of_dvd_right hrm p⟩

/-- The compensating coefficient retains the Ramaré normalization and is
therefore also `1`-bounded after collection. -/
theorem norm_wideAddedCollisionCoeff_le_one
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (A B : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (n : ℕ) :
    ‖wideAddedCollisionCoeff g A B P rest n‖ ≤ 1 := by
  classical
  let d := (P.filter (· ∣ n)).card
  by_cases hnS : n ∈ typicalS A B rest
  · have hterm : ∀ p ∈ P,
        ‖wideAddedCollisionPrimeCoeff g A B P rest p n‖
          ≤ if p * p ∣ n then 1 / ((d : ℝ) + 1) else 0 := by
      intro p hpP
      by_cases hsq : p * p ∣ n
      · rw [if_pos hsq, wideAddedCollisionPrimeCoeff, if_pos ⟨hnS, hsq⟩]
        have hp0 := (hP p hpP).pos
        have hsq' := (mul_self_dvd_iff_dvd_div hp0).1 hsq
        have hprod : p * (n / p) = n := Nat.mul_div_cancel' hsq'.1
        have hfilter : P.filter (· ∣ (n / p)) = P.filter (· ∣ n) := by
          have hf := (filter_dvd_mul_eq_of_dvd P hP hpP hsq'.2).symm
          simpa only [hprod] using hf
        rw [norm_div, norm_mul]
        have hden : ‖((P.filter (· ∣ (n / p))).card : ℂ) + 1‖
            = (d : ℝ) + 1 := by
          rw [hfilter]
          dsimp only [d]
          rw [show ((P.filter (· ∣ n)).card : ℂ) + 1 =
              (((P.filter (· ∣ n)).card + 1 : ℕ) : ℂ) by push_cast; ring,
            Complex.norm_natCast]
          push_cast
          ring
        rw [hden]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith [hg p, hg (n / p), norm_nonneg (g p), norm_nonneg (g (n / p))]
      · rw [if_neg hsq, wideAddedCollisionPrimeCoeff, if_neg, norm_zero]
        exact fun h => hsq h.2
    have hcard : (P.filter (fun p => p * p ∣ n)).card ≤ d := by
      dsimp only [d]
      exact Finset.card_le_card (filter_mul_self_dvd_subset_filter_dvd P n)
    calc
      ‖wideAddedCollisionCoeff g A B P rest n‖
          ≤ ∑ p ∈ P, ‖wideAddedCollisionPrimeCoeff g A B P rest p n‖ :=
            norm_sum_le _ _
      _ ≤ ∑ p ∈ P, if p * p ∣ n then 1 / ((d : ℝ) + 1) else 0 :=
            Finset.sum_le_sum hterm
      _ = ((P.filter (fun p => p * p ∣ n)).card : ℝ)
          * (1 / ((d : ℝ) + 1)) := by
            rw [← Finset.sum_filter]
            simp
      _ ≤ (d : ℝ) * (1 / ((d : ℝ) + 1)) := by
            gcongr
      _ ≤ 1 := by
            calc
              (d : ℝ) * (1 / ((d : ℝ) + 1)) = (d : ℝ) / ((d : ℝ) + 1) := by
                ring
              _ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  · unfold wideAddedCollisionCoeff
    have hsum : (∑ p ∈ P, wideAddedCollisionPrimeCoeff g A B P rest p n) = 0 := by
      apply Finset.sum_eq_zero
      intro p hpP
      simp [wideAddedCollisionPrimeCoeff, hnS]
    rw [hsum, norm_zero]
    norm_num

/-- Incidence-count bound for the compensating coefficient. -/
theorem norm_wideAddedCollisionCoeff_le_count
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (n : ℕ) :
    ‖wideAddedCollisionCoeff g A B P rest n‖
      ≤ ∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0 := by
  classical
  unfold wideAddedCollisionCoeff
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro p hpP
  by_cases hS : n ∈ typicalS A B rest ∧ p * p ∣ n
  · rw [wideAddedCollisionPrimeCoeff, if_pos hS, if_pos hS.2, norm_div, norm_mul]
    have hden : 1 ≤ ‖((P.filter (· ∣ (n / p))).card : ℂ) + 1‖ := by
      rw [show ((P.filter (· ∣ (n / p))).card : ℂ) + 1 =
          (((P.filter (· ∣ (n / p))).card + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos _
    rw [div_le_one (by positivity)]
    nlinarith [hg p, hg (n / p), norm_nonneg (g p), norm_nonneg (g (n / p))]
  · rw [wideAddedCollisionPrimeCoeff, if_neg hS]
    by_cases hsq : p * p ∣ n
    · rw [if_pos hsq, norm_zero]
      norm_num
    · rw [if_neg hsq, norm_zero]

/-- The compensating family has the same square-divisor harmonic mass as the
original collision family. -/
theorem addedCollision_harmonic_coeff_mass_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) :
    ∑ n ∈ Finset.Ioc A B,
        ‖wideAddedCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ)
      ≤ 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
          + (P.card : ℝ) / (A : ℝ) := by
  classical
  have hpoint : ∀ n ∈ Finset.Ioc A B,
      ‖wideAddedCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ)
        ≤ (∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) := by
    intro n hn
    have hc1 := norm_wideAddedCollisionCoeff_le_one g hg A B P hP rest n
    have hcc := norm_wideAddedCollisionCoeff_le_count g hg A B P rest n
    have hsq : ‖wideAddedCollisionCoeff g A B P rest n‖ ^ 2
        ≤ ‖wideAddedCollisionCoeff g A B P rest n‖ := by
      nlinarith [norm_nonneg (wideAddedCollisionCoeff g A B P rest n)]
    exact div_le_div_of_nonneg_right (hsq.trans hcc) (Nat.cast_nonneg n)
  calc
    ∑ n ∈ Finset.Ioc A B,
        ‖wideAddedCollisionCoeff g A B P rest n‖ ^ 2 / (n : ℝ)
        ≤ ∑ n ∈ Finset.Ioc A B,
            (∑ p ∈ P, if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) :=
              Finset.sum_le_sum hpoint
    _ = ∑ p ∈ P, ∑ n ∈ Finset.Ioc A B,
          (if p * p ∣ n then (1 : ℝ) else 0) / (n : ℝ) := by
          simp_rw [Finset.sum_div]
          rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ n ∈ (Finset.Ioc A B).filter (fun n => p * p ∣ n),
          (1 : ℝ) / (n : ℝ) := by
          refine Finset.sum_congr rfl fun p hpP => ?_
          simp only [ite_div, zero_div]
          exact (Finset.sum_filter (fun n => p * p ∣ n)
            (fun n => (1 : ℝ) / (n : ℝ))).symm
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun p hpP => ?_
          exact sum_one_div_filter_mul_self_dvd_le A B p hA (hP p hpP).pos hB
    _ = 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hpP => ?_
          ring
    _ ≤ 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2)
          + (P.card : ℝ) / (A : ℝ) := le_add_of_nonneg_right (by positivity)

open MeasureTheory Finset ExpSums in
/-- One sharp mean value application also bounds the full-block compensating
collision family. -/
theorem intervalIntegral_norm_sq_typicalSAddedTerms_wide_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T,
        ‖typicalSAddedTerms g A B P rest N v₀ v₁ xi‖ ^ 2)
      ≤ collisionEnergyBoundWide A P T := by
  classical
  let S := Finset.Ioc A B
  let c := wideAddedCollisionCoeff g A B P rest
  have hS : S ⊆ Finset.Ioc A (2 * A) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hB⟩
  have hmvt := intervalIntegral_norm_sq_poly_le_sharp_ratio A 2 hA
    (by norm_num) S hS c T hT
  rw [intervalIntegral.integral_congr (fun xi _ =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (typicalSAddedTerms_eq_dirichlet g A B P hP rest N v₀ v₁ hcov xi))]
  refine hmvt.trans ?_
  unfold collisionEnergyBoundWide
  dsimp only [S, c]
  norm_num
  refine mul_le_mul_of_nonneg_left ?_
    (show (0 : ℝ) ≤ Real.exp Real.pi * (T / (A : ℝ) + 4) by positivity)
  simpa only [one_div] using
    (addedCollision_harmonic_coeff_mass_le g hg A B hA hB P hP rest)

open MeasureTheory ExpSums in
/-- The adjusted collision keeps the existing factor-four triangle accounting,
but both halves now use the one-polynomial wide envelope. -/
theorem intervalIntegral_norm_sq_typicalSAdjustedCollision_wide_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A B : ℕ) (hA : 1 ≤ A) (hB : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T,
      ‖typicalSAdjustedCollision g A B P rest N v₀ v₁ xi‖ ^ 2)
      ≤ 4 * collisionEnergyBoundWide A P T := by
  let F := typicalSCollision g A B P rest
  let E := typicalSAddedTerms g A B P rest N v₀ v₁
  have hsplit := intervalIntegral_norm_add_sq_le F (fun xi => -E xi)
    (continuous_typicalSCollision g A B P rest)
    (continuous_typicalSAddedTerms g A B P rest N v₀ v₁).neg T hT.le
  have hcoll := intervalIntegral_norm_sq_typicalSCollision_wide_le g hg A B hA
    hB P hP rest T hT
  have hadd := intervalIntegral_norm_sq_typicalSAddedTerms_wide_le g hg A B hA
    hB P hP rest N v₀ v₁ hcov T hT
  change (∫ xi in (-T)..T, ‖F xi - E xi‖ ^ 2)
      ≤ 4 * collisionEnergyBoundWide A P T
  have hsplit' : (∫ xi in (-T)..T, ‖F xi - E xi‖ ^ 2)
      ≤ 2 * (∫ xi in (-T)..T, ‖F xi‖ ^ 2)
        + 2 * (∫ xi in (-T)..T, ‖E xi‖ ^ 2) := by
    simpa only [sub_eq_add_neg, norm_neg] using hsplit
  exact hsplit'.trans (by linarith)

open MeasureTheory in
/-- The wide collision fit supplies the collision share used by a level leg. -/
theorem typicalSAdjustedCollision_le_budget_wide
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hA : 1 ≤ A) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGT : G ⊆ Set.Ioc (-T) T)
    (kappa c₃ eps rho : ℝ)
    (hfit : 8 * collisionEnergyBoundWide A P T
      ≤ kappa * bandBudget c₃ eps rho) :
    2 * (∫ xi in G,
      ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  have hB : A + Delta ≤ 2 * A := by omega
  have hset := ExpSums.setIntegral_le_intervalIntegral_of_nonneg
    (fun xi => ‖typicalSAdjustedCollision
      g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
    ((continuous_typicalSAdjustedCollision
      g A (A + Delta) P rest N v₀ v₁).norm.pow 2)
    (fun xi => sq_nonneg _) T hT.le G hGT
  have hint := intervalIntegral_norm_sq_typicalSAdjustedCollision_wide_le
    g hg A (A + Delta) hA hB P hP rest N v₀ v₁ hcov T hT
  linarith

open MeasureTheory in
/-- **A level anywhere in the list, with a wide collision fit.**  This is the
wide analogue of `typicalS_level_leg_le_budget_of_collision_fit_middle`; only
the numerical collision envelope changes. -/
theorem typicalS_level_leg_le_budget_of_collision_fit_middle_wide
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 1 ≤ A) (hDeltaA : Delta ≤ A)
    (L₁ L₂ : List (Finset ℕ)) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll (L₁ ++ L₂) (p * m) ↔ HasFactorInAll (L₁ ++ L₂) m)
    (q : ℕ → ℕ)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellUniformMain g A (A + Delta) P (L₁ ++ L₂)
            N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellReplacement g A (A + Delta) P (L₁ ++ L₂)
            N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollisionFitWide : 8 * collisionEnergyBoundWide A P T
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (L₁ ++ P :: L₂),
              (g m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  rw [typicalS_middle A (A + Delta) L₁ L₂ P]
  apply typicalS_level_leg_le_budget g hcm A Delta H P hP (L₁ ++ L₂)
    N v₀ v₁ hcov hstable q K₁ K₂ T J j Pset hPset hpartT
    kappaMain kappaReplacement kappaCollision c₃ eps hc₃ hmain hreplacement
  · exact typicalSAdjustedCollision_le_budget_wide g hg A Delta hA hDeltaA
      P hP (L₁ ++ L₂) N v₀ v₁ hcov T hT
      (bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j)
      hpartT kappaCollision c₃ eps ((Delta : ℝ) / (A : ℝ)) hcollisionFitWide
  · exact hshare



end MoltResearch
