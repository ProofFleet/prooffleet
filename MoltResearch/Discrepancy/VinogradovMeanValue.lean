import Mathlib
import MoltResearch.Discrepancy.ChebyshevBlock

/-!
# Vinogradov's mean value theorem

This file gives the elementary Linnik--Karatsuba `p`-adic proof of the
classical weak Vinogradov mean value theorem.  Tuples are represented by
functions on `Fin s`; this keeps every counting set finite and makes the
coordinate symmetries explicit.

The normalization is

`J_{s,k}(P) = #{(x,y) in [1,P]^s x [1,P]^s : sum_i x_i^j = sum_i y_i^j
for 1 <= j <= k}`.

The constants below are deliberately explicit at the combinatorial stages.
The final constant is allowed to depend on `k` and on the iteration count.
-/

namespace MoltResearch

open scoped BigOperators

/-- The finite set of `s`-tuples with every coordinate in `[1, P]`. -/
def vinogradovTuples (s P : ℕ) : Finset (Fin s → ℕ) :=
  Fintype.piFinset fun _ : Fin s => Finset.Icc 1 P

/-- The `j`-th power sum of a tuple. -/
def vinogradovPowerSum {s : ℕ} (x : Fin s → ℕ) (j : ℕ) : ℕ :=
  ∑ i, x i ^ j

/-- The vector of the first `k` power sums. -/
def vinogradovMomentVector {s : ℕ} (k : ℕ) (x : Fin s → ℕ) : Fin k → ℕ :=
  fun j => vinogradovPowerSum x (j + 1)

/-- The Vinogradov system through degree `k`. -/
def IsVinogradovSolution {s : ℕ} (k : ℕ) (x y : Fin s → ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, vinogradovPowerSum x j = vinogradovPowerSum y j

instance {s k : ℕ} (x y : Fin s → ℕ) :
    Decidable (IsVinogradovSolution k x y) := by
  unfold IsVinogradovSolution
  infer_instance

/-- Vinogradov's integral in counting form. -/
def vinogradovJ (s k P : ℕ) : ℕ :=
  (((vinogradovTuples s P) ×ˢ (vinogradovTuples s P)).filter
    fun xy : (Fin s → ℕ) × (Fin s → ℕ) =>
      IsVinogradovSolution k xy.1 xy.2).card

theorem mem_vinogradovTuples {s P : ℕ} {x : Fin s → ℕ} :
    x ∈ vinogradovTuples s P ↔ ∀ i, 1 ≤ x i ∧ x i ≤ P := by
  simp [vinogradovTuples, Finset.mem_Icc]

theorem card_vinogradovTuples (s P : ℕ) :
    (vinogradovTuples s P).card = P ^ s := by
  classical
  simp [vinogradovTuples, Nat.card_Icc]

theorem isVinogradovSolution_iff_momentVector_eq {s k : ℕ}
    {x y : Fin s → ℕ} :
    IsVinogradovSolution k x y ↔
      vinogradovMomentVector k x = vinogradovMomentVector k y := by
  constructor
  · intro h
    funext j
    exact h (j + 1) (by simp [Finset.mem_Icc])
  · intro h j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
    let j' : Fin k := ⟨j - 1, by omega⟩
    simpa [vinogradovMomentVector, j', Nat.sub_add_cancel hj1] using congrFun h j'

theorem mem_vinogradovJ_filter {s k P : ℕ}
    {xy : (Fin s → ℕ) × (Fin s → ℕ)} :
    xy ∈ (((vinogradovTuples s P) ×ˢ (vinogradovTuples s P)).filter
      fun z : (Fin s → ℕ) × (Fin s → ℕ) =>
        IsVinogradovSolution k z.1 z.2) ↔
      (∀ i, 1 ≤ xy.1 i ∧ xy.1 i ≤ P) ∧
      (∀ i, 1 ≤ xy.2 i ∧ xy.2 i ≤ P) ∧
      (∀ j ∈ Finset.Icc 1 k,
        ∑ i, xy.1 i ^ j = ∑ i, xy.2 i ^ j) := by
  simp [mem_vinogradovTuples, IsVinogradovSolution, vinogradovPowerSum,
    and_assoc]

/-- Enlarging the coordinate interval cannot remove solutions. -/
theorem vinogradovJ_mono {s k P Q : ℕ} (hPQ : P ≤ Q) :
    vinogradovJ s k P ≤ vinogradovJ s k Q := by
  classical
  rw [vinogradovJ, vinogradovJ]
  apply Finset.card_le_card
  intro xy hxy
  rw [Finset.mem_filter] at hxy ⊢
  refine ⟨?_, hxy.2⟩
  rw [Finset.mem_product] at hxy ⊢
  exact ⟨Finset.mem_of_subset (fun x hx =>
    mem_vinogradovTuples.mpr fun i =>
      ⟨(mem_vinogradovTuples.mp hx i).1,
        (mem_vinogradovTuples.mp hx i).2.trans hPQ⟩) hxy.1.1,
    Finset.mem_of_subset (fun x hx =>
      mem_vinogradovTuples.mpr fun i =>
        ⟨(mem_vinogradovTuples.mp hx i).1,
          (mem_vinogradovTuples.mp hx i).2.trans hPQ⟩) hxy.1.2⟩

/-- The direct count `J_{s,k}(P) <= P^(2s)`. -/
theorem vinogradovJ_le_trivial (s k P : ℕ) :
    vinogradovJ s k P ≤ P ^ (2 * s) := by
  classical
  calc
    vinogradovJ s k P
        ≤ ((vinogradovTuples s P) ×ˢ (vinogradovTuples s P)).card :=
          by exact Finset.card_filter_le _ _
    _ = P ^ s * P ^ s := by simp [card_vinogradovTuples]
    _ = P ^ (2 * s) := by rw [← pow_add]; congr 1; omega

/-- Agreement of power sums, including the automatic degree-zero equation. -/
def VinogradovAgreeUpTo {s : ℕ} (k : ℕ) (x y : Fin s → ℕ) : Prop :=
  ∀ j ≤ k, vinogradovPowerSum x j = vinogradovPowerSum y j

theorem isVinogradovSolution_iff_agreeUpTo {s k : ℕ}
    {x y : Fin s → ℕ} :
    IsVinogradovSolution k x y ↔ VinogradovAgreeUpTo k x y := by
  constructor
  · intro h j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp [vinogradovPowerSum]
    · exact h j (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj0, hj⟩)
  · intro h j hj
    exact h j (Finset.mem_Icc.mp hj).2

/-- Binomial expansion of a translated power sum. -/
theorem vinogradovPowerSum_add {s : ℕ} (x : Fin s → ℕ) (a j : ℕ) :
    vinogradovPowerSum (fun i => x i + a) j =
      ∑ l ∈ Finset.range (j + 1),
        (j.choose l * a ^ (j - l)) * vinogradovPowerSum x l := by
  classical
  rw [vinogradovPowerSum]
  simp_rw [add_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [vinogradovPowerSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ac_rfl

private theorem agreeUpTo_add_forward {s k : ℕ} {x y : Fin s → ℕ}
    (a : ℕ) (h : VinogradovAgreeUpTo k x y) :
    VinogradovAgreeUpTo k (fun i => x i + a) (fun i => y i + a) := by
  intro j hj
  rw [vinogradovPowerSum_add, vinogradovPowerSum_add]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [h l (le_trans (by simpa using hl : l ≤ j) hj)]

private theorem agreeUpTo_of_add {s k : ℕ} {x y : Fin s → ℕ}
    (a : ℕ)
    (h : VinogradovAgreeUpTo k (fun i => x i + a) (fun i => y i + a)) :
    VinogradovAgreeUpTo k x y := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hs := h j hj
      rw [vinogradovPowerSum_add, vinogradovPowerSum_add,
        Finset.sum_range_succ, Finset.sum_range_succ] at hs
      have hlo :
          (∑ l ∈ Finset.range j,
              (j.choose l * a ^ (j - l)) * vinogradovPowerSum x l) =
            ∑ l ∈ Finset.range j,
              (j.choose l * a ^ (j - l)) * vinogradovPowerSum y l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [ih l (Finset.mem_range.mp hl) (le_trans (Nat.le_of_lt
          (Finset.mem_range.mp hl)) hj)]
      rw [hlo] at hs
      simpa using Nat.add_left_cancel hs

/-- Translation invariance of the Vinogradov system, in both directions. -/
theorem isVinogradovSolution_add_iff {s k : ℕ} (x y : Fin s → ℕ) (a : ℕ) :
    IsVinogradovSolution k (fun i => x i + a) (fun i => y i + a) ↔
      IsVinogradovSolution k x y := by
  rw [isVinogradovSolution_iff_agreeUpTo,
    isVinogradovSolution_iff_agreeUpTo]
  exact ⟨agreeUpTo_of_add a, agreeUpTo_add_forward a⟩

/-- Number of equal-moment pairs drawn from two finite tuple sets. -/
def vinogradovPairCount {s : ℕ} (k : ℕ)
    (A B : Finset (Fin s → ℕ)) : ℕ :=
  ((A ×ˢ B).filter fun xy : (Fin s → ℕ) × (Fin s → ℕ) =>
    vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2).card

/-- The representation function attached to a finite tuple set. -/
def vinogradovRepresentation {s k : ℕ} (A : Finset (Fin s → ℕ))
    (c : Fin k → ℕ) : ℕ :=
  (A.filter fun x => vinogradovMomentVector k x = c).card

theorem vinogradovPairCount_eq_sum_representation {s k : ℕ}
    (A B : Finset (Fin s → ℕ)) :
    vinogradovPairCount k A B =
      ∑ c ∈ A.image (vinogradovMomentVector k) ∪
          B.image (vinogradovMomentVector k),
        vinogradovRepresentation A c * vinogradovRepresentation B c := by
  classical
  let C := A.image (vinogradovMomentVector k) ∪
    B.image (vinogradovMomentVector k)
  rw [vinogradovPairCount]
  have hmaps : Set.MapsTo
      (fun xy : (Fin s → ℕ) × (Fin s → ℕ) => vinogradovMomentVector k xy.1)
      ↑((A ×ˢ B).filter fun xy =>
        vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2) ↑C := by
    intro xy hxy
    change xy ∈ ((A ×ˢ B).filter fun xy =>
      vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2) at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨xy.1, hxy.1.1, rfl⟩)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [vinogradovRepresentation, vinogradovRepresentation, ← Finset.card_product]
  apply congrArg Finset.card
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product]
  aesop

theorem vinogradovJ_eq_pairCount (s k P : ℕ) :
    vinogradovJ s k P =
      vinogradovPairCount k (vinogradovTuples s P) (vinogradovTuples s P) := by
  classical
  unfold vinogradovJ vinogradovPairCount
  apply congrArg Finset.card
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product]
  exact and_congr_right fun _ => isVinogradovSolution_iff_momentVector_eq

/-- Cauchy--Schwarz for a restricted first tuple, in squared counting form. -/
theorem vinogradovPairCount_sq_le {s k : ℕ}
    (A B : Finset (Fin s → ℕ)) :
    vinogradovPairCount k A B ^ 2 ≤
      vinogradovPairCount k A A * vinogradovPairCount k B B := by
  classical
  let C := A.image (vinogradovMomentVector k) ∪
    B.image (vinogradovMomentVector k)
  rw [vinogradovPairCount_eq_sum_representation,
    vinogradovPairCount_eq_sum_representation,
    vinogradovPairCount_eq_sum_representation]
  simp only [Finset.union_self]
  have hA :
      (∑ c ∈ A.image (vinogradovMomentVector k),
          vinogradovRepresentation A c ^ 2) =
        ∑ c ∈ C, vinogradovRepresentation A c ^ 2 := by
    change (∑ c ∈ A.image (vinogradovMomentVector k),
      vinogradovRepresentation A c ^ 2) =
      ∑ c ∈ A.image (vinogradovMomentVector k) ∪
        B.image (vinogradovMomentVector k), vinogradovRepresentation A c ^ 2
    apply Finset.sum_subset (Finset.subset_union_left)
    intro c hc hca
    have hz : (A.filter fun x => vinogradovMomentVector k x = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hxc
      exact hca (Finset.mem_image.mpr ⟨x, hx, hxc⟩)
    simp [vinogradovRepresentation, hz]
  have hB :
      (∑ c ∈ B.image (vinogradovMomentVector k),
          vinogradovRepresentation B c ^ 2) =
        ∑ c ∈ C, vinogradovRepresentation B c ^ 2 := by
    change (∑ c ∈ B.image (vinogradovMomentVector k),
      vinogradovRepresentation B c ^ 2) =
      ∑ c ∈ A.image (vinogradovMomentVector k) ∪
        B.image (vinogradovMomentVector k), vinogradovRepresentation B c ^ 2
    apply Finset.sum_subset (Finset.subset_union_right)
    intro c hc hcb
    have hz : (B.filter fun x => vinogradovMomentVector k x = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hxc
      exact hcb (Finset.mem_image.mpr ⟨x, hx, hxc⟩)
    simp [vinogradovRepresentation, hz]
  change (∑ c ∈ C,
      vinogradovRepresentation A c * vinogradovRepresentation B c) ^ 2 ≤
    (∑ c ∈ A.image (vinogradovMomentVector k),
      vinogradovRepresentation A c * vinogradovRepresentation A c) *
    ∑ c ∈ B.image (vinogradovMomentVector k),
      vinogradovRepresentation B c * vinogradovRepresentation B c
  simpa only [← pow_two, hA, hB] using (Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) C
    (vinogradovRepresentation A) (vinogradovRepresentation B))

/-- Sub-additivity in the first tuple set, used for case splits. -/
theorem vinogradovPairCount_union_le {s k : ℕ}
    (A₁ A₂ B : Finset (Fin s → ℕ)) :
    vinogradovPairCount k (A₁ ∪ A₂) B ≤
      vinogradovPairCount k A₁ B + vinogradovPairCount k A₂ B := by
  classical
  unfold vinogradovPairCount
  rw [show (((A₁ ∪ A₂) ×ˢ B).filter fun xy =>
      vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2) =
      ((A₁ ×ˢ B).filter fun xy =>
        vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2) ∪
      ((A₂ ×ˢ B).filter fun xy =>
        vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2) by
    ext xy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    aesop]
  exact Finset.card_union_le _ _

/-! ## Well-conditioned tuples -/

/-- The coordinates of `x` occupy distinct residue classes modulo `p`. -/
def VinogradovWellConditioned {k : ℕ} (p : ℕ) (x : Fin k → ℕ) : Prop :=
  ∀ i j, i ≠ j → x i % p ≠ x j % p

noncomputable instance {k p : ℕ} (x : Fin k → ℕ) :
    Decidable (VinogradovWellConditioned p x) := Classical.propDecidable _

/-- Indices `i < j`, represented without a redundant orientation. -/
abbrev VinogradovIndexPair (k : ℕ) := Σ j : Fin k, Fin j

private def vinogradovIndexPairFirst {k : ℕ} (q : VinogradovIndexPair k) : Fin k :=
  ⟨q.2, lt_trans q.2.isLt q.1.isLt⟩

private def vinogradovIndexPairSecond {k : ℕ} (q : VinogradovIndexPair k) : Fin k :=
  q.1

private theorem vinogradovIndexPair_ne {k : ℕ} (q : VinogradovIndexPair k) :
    vinogradovIndexPairFirst q ≠ vinogradovIndexPairSecond q := by
  intro h
  have := congrArg Fin.val h
  simp [vinogradovIndexPairFirst, vinogradovIndexPairSecond] at this
  omega

private theorem card_vinogradovIndexPair (k : ℕ) :
    Fintype.card (VinogradovIndexPair k) = k.choose 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k, Finset.sum_range_id,
    Nat.choose_two_right]

private theorem card_vinogradovTuples_filter_coord_modEq_le {n P p : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    ((vinogradovTuples n P).filter fun x => x i % p = x j % p).card
      ≤ P ^ (n - 1) * (P / p + 1) := by
  classical
  let rest : Finset ({q : Fin n // q ≠ j} → ℕ) :=
    Fintype.piFinset fun _ : {q : Fin n // q ≠ j} => Finset.Icc 1 P
  let target := rest ×ˢ Finset.range (P / p + 1)
  let encode : (Fin n → ℕ) → ({q : Fin n // q ≠ j} → ℕ) × ℕ :=
    fun x => (fun q => x q, x j / p)
  have hmaps : Set.MapsTo encode
      ↑((vinogradovTuples n P).filter fun x => x i % p = x j % p) ↑target := by
    intro x hx
    change x ∈ ((vinogradovTuples n P).filter fun x => x i % p = x j % p) at hx
    rw [Finset.mem_filter] at hx
    rw [show target = rest ×ˢ Finset.range (P / p + 1) from rfl]
    change encode x ∈ rest ×ˢ Finset.range (P / p + 1)
    rw [Finset.mem_product]
    change (fun q : {q : Fin n // q ≠ j} => x q) ∈ rest ∧
      x j / p ∈ Finset.range (P / p + 1)
    rw [Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun q => Finset.mem_Icc.mpr (mem_vinogradovTuples.mp hx.1 q), ?_⟩
    have := Nat.div_le_div_right (c := p) (mem_vinogradovTuples.mp hx.1 j).2
    omega
  have hinj : Set.InjOn encode
      ↑((vinogradovTuples n P).filter fun x => x i % p = x j % p) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    funext q
    by_cases hqj : q = j
    · subst q
      have hdiv : x j / p = y j / p := congrArg Prod.snd hxy
      have hrest : x i = y i := by
        exact congrFun (congrArg Prod.fst hxy) ⟨i, hij⟩
      have hmod : x j % p = y j % p := by rw [← hx.2, ← hy.2, hrest]
      have hmul : p * (x j / p) = p * (y j / p) := by rw [hdiv]
      have hxrepr := Nat.div_add_mod (x j) p
      have hyrepr := Nat.div_add_mod (y j) p
      omega
    · exact congrFun (congrArg Prod.fst hxy) ⟨q, hqj⟩
  have hcard := Finset.card_le_card_of_injOn encode hmaps hinj
  have hrestCard : rest.card = P ^ (n - 1) := by
    simp only [rest, Fintype.card_piFinset, Nat.card_Icc, Nat.add_sub_cancel,
      Finset.prod_const, Finset.card_univ]
    congr 1
    simpa only [Fintype.card_fin, Fintype.card_unique, Nat.sub_eq] using
      (Fintype.card_subtype_compl (fun q : Fin n => q = j))
  simpa [target, hrestCard] using hcard

/-- A single prescribed coordinate collision has the expected codimension-one
bound.  The quotient of the second coordinate and all remaining coordinates
form an injective encoding. -/
theorem card_vinogradovTuples_filter_modEq_le {k P p : ℕ}
    (q : VinogradovIndexPair k) :
    ((vinogradovTuples k P).filter fun x =>
      x (vinogradovIndexPairFirst q) % p =
        x (vinogradovIndexPairSecond q) % p).card
      ≤ P ^ (k - 1) * (P / p + 1) := by
  exact card_vinogradovTuples_filter_coord_modEq_le _ _
    (vinogradovIndexPair_ne q)

private theorem not_wellConditioned_subset_biUnion {k P p : ℕ} :
    (vinogradovTuples k P).filter (fun x => ¬ VinogradovWellConditioned p x) ⊆
      (Finset.univ : Finset (VinogradovIndexPair k)).biUnion fun q =>
        (vinogradovTuples k P).filter fun x =>
          x (vinogradovIndexPairFirst q) % p =
            x (vinogradovIndexPairSecond q) % p := by
  classical
  intro x hx
  rw [Finset.mem_filter] at hx
  simp only [VinogradovWellConditioned] at hx
  push_neg at hx
  obtain ⟨i, j, hij, hmod⟩ := hx.2
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · rw [Finset.mem_biUnion]
    let q : VinogradovIndexPair k := ⟨j, ⟨i, hijlt⟩⟩
    refine ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr ⟨hx.1, ?_⟩⟩
    simpa [q, vinogradovIndexPairFirst, vinogradovIndexPairSecond] using hmod
  · rw [Finset.mem_biUnion]
    let q : VinogradovIndexPair k := ⟨i, ⟨j, hjilt⟩⟩
    refine ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr ⟨hx.1, ?_⟩⟩
    simpa [q, vinogradovIndexPairFirst, vinogradovIndexPairSecond] using hmod.symm

/-- Ill-conditioned tuples: one of the `k choose 2` coordinate pairs
collides, and a residue class meets `[1,P]` at most `P/p+1` times. -/
theorem card_not_wellConditioned_le (k P p : ℕ) :
    ((vinogradovTuples k P).filter
      (fun x => ¬ VinogradovWellConditioned p x)).card
      ≤ k.choose 2 * P ^ (k - 1) * (P / p + 1) := by
  classical
  calc
    ((vinogradovTuples k P).filter
        (fun x => ¬ VinogradovWellConditioned p x)).card
      ≤ ((Finset.univ : Finset (VinogradovIndexPair k)).biUnion fun q =>
          (vinogradovTuples k P).filter fun x =>
            x (vinogradovIndexPairFirst q) % p =
              x (vinogradovIndexPairSecond q) % p).card :=
        Finset.card_le_card not_wellConditioned_subset_biUnion
    _ ≤ ∑ _q : VinogradovIndexPair k, P ^ (k - 1) * (P / p + 1) := by
      refine (Finset.card_biUnion_le).trans ?_
      exact Finset.sum_le_sum fun q _ => card_vinogradovTuples_filter_modEq_le q
    _ = k.choose 2 * P ^ (k - 1) * (P / p + 1) := by
      rw [Finset.sum_const, Finset.card_univ, card_vinogradovIndexPair]
      simp [mul_assoc]

private def vinogradovFirstIndex (s : ℕ) {k : ℕ} (i : Fin k) : Fin (s + k) :=
  ⟨i, lt_of_lt_of_le i.isLt (Nat.le_add_left k s)⟩

/-- Well-conditioning of the first `k` coordinates in an `(s+k)`-tuple. -/
def VinogradovFirstWellConditioned {s k : ℕ} (p : ℕ)
    (x : Fin (s + k) → ℕ) : Prop :=
  ∀ i j : Fin k, i ≠ j →
    x (vinogradovFirstIndex s i) % p ≠ x (vinogradovFirstIndex s j) % p

noncomputable instance {s k p : ℕ} (x : Fin (s + k) → ℕ) :
    Decidable (VinogradovFirstWellConditioned p x) := Classical.propDecidable _

private theorem not_firstWellConditioned_subset_biUnion {s k P p : ℕ} :
    (vinogradovTuples (s + k) P).filter
        (fun x => ¬ VinogradovFirstWellConditioned p x) ⊆
      (Finset.univ : Finset (VinogradovIndexPair k)).biUnion fun q =>
        (vinogradovTuples (s + k) P).filter fun x =>
          x (vinogradovFirstIndex s (vinogradovIndexPairFirst q)) % p =
            x (vinogradovFirstIndex s (vinogradovIndexPairSecond q)) % p := by
  classical
  intro x hx
  rw [Finset.mem_filter] at hx
  simp only [VinogradovFirstWellConditioned] at hx
  push_neg at hx
  obtain ⟨i, j, hij, hmod⟩ := hx.2
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · rw [Finset.mem_biUnion]
    let q : VinogradovIndexPair k := ⟨j, ⟨i, hijlt⟩⟩
    refine ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr ⟨hx.1, ?_⟩⟩
    simpa [q, vinogradovIndexPairFirst, vinogradovIndexPairSecond] using hmod
  · rw [Finset.mem_biUnion]
    let q : VinogradovIndexPair k := ⟨i, ⟨j, hjilt⟩⟩
    refine ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr ⟨hx.1, ?_⟩⟩
    simpa [q, vinogradovIndexPairFirst, vinogradovIndexPairSecond] using hmod.symm

/-- The ill-conditioned first block in `[1,P]^(s+k)`. -/
theorem card_not_firstWellConditioned_le (s k P p : ℕ) :
    ((vinogradovTuples (s + k) P).filter
      (fun x => ¬ VinogradovFirstWellConditioned p x)).card
      ≤ k.choose 2 * P ^ (s + k - 1) * (P / p + 1) := by
  classical
  calc
    ((vinogradovTuples (s + k) P).filter
        (fun x => ¬ VinogradovFirstWellConditioned p x)).card
      ≤ ((Finset.univ : Finset (VinogradovIndexPair k)).biUnion fun q =>
          (vinogradovTuples (s + k) P).filter fun x =>
            x (vinogradovFirstIndex s (vinogradovIndexPairFirst q)) % p =
              x (vinogradovFirstIndex s (vinogradovIndexPairSecond q)) % p).card :=
        Finset.card_le_card not_firstWellConditioned_subset_biUnion
    _ ≤ ∑ _q : VinogradovIndexPair k,
        P ^ (s + k - 1) * (P / p + 1) := by
      refine Finset.card_biUnion_le.trans ?_
      exact Finset.sum_le_sum fun q _ =>
        card_vinogradovTuples_filter_coord_modEq_le _ _ (by
          intro h
          apply vinogradovIndexPair_ne q
          apply Fin.ext
          simpa [vinogradovFirstIndex] using congrArg Fin.val h)
    _ = k.choose 2 * P ^ (s + k - 1) * (P / p + 1) := by
      rw [Finset.sum_const, Finset.card_univ, card_vinogradovIndexPair]
      simp [mul_assoc]

/-- Splitting by whether the first `k` coordinates are well-conditioned. -/
theorem vinogradovJ_le_well_add_ill (s k P p : ℕ) :
    vinogradovJ (s + k) k P ≤
      vinogradovPairCount k
        ((vinogradovTuples (s + k) P).filter
          (VinogradovFirstWellConditioned p))
        (vinogradovTuples (s + k) P) +
      vinogradovPairCount k
        ((vinogradovTuples (s + k) P).filter
          (fun x => ¬ VinogradovFirstWellConditioned p x))
        (vinogradovTuples (s + k) P) := by
  have hcover : vinogradovTuples (s + k) P =
      (vinogradovTuples (s + k) P).filter
          (VinogradovFirstWellConditioned p) ∪
      (vinogradovTuples (s + k) P).filter
        (fun x => ¬ VinogradovFirstWellConditioned p x) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  calc
    vinogradovJ (s + k) k P =
        vinogradovPairCount k (vinogradovTuples (s + k) P)
          (vinogradovTuples (s + k) P) := vinogradovJ_eq_pairCount _ _ _
    _ = vinogradovPairCount k
        ((vinogradovTuples (s + k) P).filter
            (VinogradovFirstWellConditioned p) ∪
          (vinogradovTuples (s + k) P).filter
            (fun x => ¬ VinogradovFirstWellConditioned p x))
        (vinogradovTuples (s + k) P) := by rw [← hcover]
    _ ≤ _ := vinogradovPairCount_union_le _ _ _

/-- The ill-conditioned contribution is controlled against the full mean
value by the counting Cauchy--Schwarz inequality. -/
theorem vinogradovPairCount_ill_sq_le (s k P p : ℕ) :
    vinogradovPairCount k
        ((vinogradovTuples (s + k) P).filter
          (fun x => ¬ VinogradovFirstWellConditioned p x))
        (vinogradovTuples (s + k) P) ^ 2 ≤
      vinogradovPairCount k
          ((vinogradovTuples (s + k) P).filter
            (fun x => ¬ VinogradovFirstWellConditioned p x))
          ((vinogradovTuples (s + k) P).filter
            (fun x => ¬ VinogradovFirstWellConditioned p x)) *
        vinogradovJ (s + k) k P := by
  rw [vinogradovJ_eq_pairCount]
  exact vinogradovPairCount_sq_le _ _

/-! ## Linnik's congruence lemma -/

private theorem multiset_esymm_eq_of_powerSums_eq
    {R : Type*} [CommRing R] {k : ℕ} (x y : Fin k → R)
    (hunit : ∀ m ∈ Finset.Icc 1 k, IsUnit (m : R))
    (hpow : ∀ m ∈ Finset.Icc 1 k, ∑ i, x i ^ m = ∑ i, y i ^ m) :
    ∀ m ≤ k,
      (Finset.univ.val.map x).esymm m = (Finset.univ.val.map y).esymm m := by
  intro m hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp [Multiset.esymm]
      · have hmI : m ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr hm0, hm⟩
        have hnx := congrArg (MvPolynomial.aeval x)
          (MvPolynomial.mul_esymm_eq_sum (Fin k) R m)
        have hny := congrArg (MvPolynomial.aeval y)
          (MvPolynomial.mul_esymm_eq_sum (Fin k) R m)
        simp only [map_mul, map_pow, map_neg, map_one,
          MvPolynomial.aeval_esymm_eq_multiset_esymm] at hnx hny
        have hevalx (n : ℕ) :
            MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R n) =
              (Finset.univ.val.map x).esymm n := by
          rw [← MvPolynomial.aeval_eq_eval]
          exact MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin k) R n x
        have hevaly (n : ℕ) :
            MvPolynomial.eval y (MvPolynomial.esymm (Fin k) R n) =
              (Finset.univ.val.map y).esymm n := by
          rw [← MvPolynomial.aeval_eq_eval]
          exact MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin k) R n y
        have hnx' :
            (m : R) * (Finset.univ.val.map x).esymm m =
              (-1 : R) ^ (m + 1) *
                ∑ a ∈ Finset.antidiagonal m with a.1 < m,
                  (-1 : R) ^ a.1 * (Finset.univ.val.map x).esymm a.1 *
                    ∑ i, x i ^ a.2 := by
          simpa [MvPolynomial.psum, hevalx] using hnx
        have hny' :
            (m : R) * (Finset.univ.val.map y).esymm m =
              (-1 : R) ^ (m + 1) *
                ∑ a ∈ Finset.antidiagonal m with a.1 < m,
                  (-1 : R) ^ a.1 * (Finset.univ.val.map y).esymm a.1 *
                    ∑ i, y i ^ a.2 := by
          simpa [MvPolynomial.psum, hevaly] using hny
        have hrs :
            (∑ a ∈ Finset.antidiagonal m with a.1 < m,
                (-1 : R) ^ a.1 * (Finset.univ.val.map x).esymm a.1 *
                  ∑ i, x i ^ a.2) =
              ∑ a ∈ Finset.antidiagonal m with a.1 < m,
                (-1 : R) ^ a.1 * (Finset.univ.val.map y).esymm a.1 *
                  ∑ i, y i ^ a.2 := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Finset.mem_filter] at ha
          have ha2 : a.2 ≤ m := by
            have := (Finset.mem_antidiagonal.mp ha.1).symm
            omega
          rw [ih a.1 ha.2 (le_trans (Nat.le_of_lt ha.2) hm)]
          by_cases ha20 : a.2 = 0
          · simp [ha20]
          · rw [hpow a.2 (Finset.mem_Icc.mpr
              ⟨Nat.one_le_iff_ne_zero.mpr ha20, ha2.trans hm⟩)]
        rw [hrs] at hnx'
        have hmul : (m : R) * (Finset.univ.val.map x).esymm m =
            (m : R) * (Finset.univ.val.map y).esymm m := hnx'.trans hny'.symm
        exact (hunit m hmI).mul_left_cancel hmul

private noncomputable def vinogradovTuplePolynomial {R : Type*} [CommRing R] {k : ℕ}
    (x : Fin k → R) : Polynomial R :=
  ∏ i, (Polynomial.X - Polynomial.C (x i))

private theorem vinogradovTuplePolynomial_eq_of_esymm_eq
    {R : Type*} [CommRing R] {k : ℕ} (x y : Fin k → R)
    (h : ∀ m ≤ k,
      (Finset.univ.val.map x).esymm m = (Finset.univ.val.map y).esymm m) :
    vinogradovTuplePolynomial x = vinogradovTuplePolynomial y := by
  classical
  have hxform := Multiset.prod_X_sub_X_eq_sum_esymm
    (Finset.univ.val.map x)
  have hyform := Multiset.prod_X_sub_X_eq_sum_esymm
    (Finset.univ.val.map y)
  have hxform' : vinogradovTuplePolynomial x =
      ∑ m ∈ Finset.range (k + 1),
        (-1) ^ m * (Polynomial.C ((Finset.univ.val.map x).esymm m) *
          Polynomial.X ^ (k - m)) := by
    simpa [vinogradovTuplePolynomial, Finset.prod, Multiset.map_map,
      Function.comp_def] using hxform
  have hyform' : vinogradovTuplePolynomial y =
      ∑ m ∈ Finset.range (k + 1),
        (-1) ^ m * (Polynomial.C ((Finset.univ.val.map y).esymm m) *
          Polynomial.X ^ (k - m)) := by
    simpa [vinogradovTuplePolynomial, Finset.prod, Multiset.map_map,
      Function.comp_def] using hyform
  rw [hxform', hyform']
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [h m (by simpa using hm : m ≤ k)]

/-- The full vector of power sums modulo `p^k`. -/
def vinogradovFullMoment (p k : ℕ) (x : Fin k → ℕ) : Fin k → ZMod (p ^ k) :=
  fun j => ∑ i, (x i : ZMod (p ^ k)) ^ ((j : ℕ) + 1)

private theorem zmod_primePow_natCast_isUnit {p k m : ℕ}
    (hp : p.Prime) (hm0 : 0 < m) (hmp : m < p) :
    IsUnit (m : ZMod (p ^ k)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  exact ((hp.coprime_iff_not_dvd).mpr fun hpm =>
    (not_lt_of_ge (Nat.le_of_dvd hm0 hpm)) hmp).symm

private theorem isUnit_zmod_primePow_of_cast_ne_zero {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) (z : ZMod (p ^ k))
    (hz : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) z ≠ 0) :
    IsUnit z := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  exact ((hp.coprime_iff_not_dvd).mpr fun hpv => hz (by
    calc
      ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) z =
          ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
            (z.val : ZMod (p ^ k)) := by rw [ZMod.natCast_zmod_val]
      _ = (z.val : ZMod p) := by simp
      _ = 0 := by
        obtain ⟨q, hq⟩ := hpv
        rw [hq, Nat.cast_mul, CharP.cast_eq_zero, zero_mul])).symm

private theorem fullMoment_injective_of_same_residues {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpk : k < p)
    (x y : Fin k → ℕ) (hx : VinogradovWellConditioned p x)
    (hmom : vinogradovFullMoment p k x = vinogradovFullMoment p k y)
    (hres : ∀ i, (x i : ZMod p) = (y i : ZMod p)) :
    ∀ i, (x i : ZMod (p ^ k)) = (y i : ZMod (p ^ k)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpow : ∀ m ∈ Finset.Icc 1 k,
      ∑ i, (x i : ZMod (p ^ k)) ^ m =
        ∑ i, (y i : ZMod (p ^ k)) ^ m := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmk := (Finset.mem_Icc.mp hm).2
    let m' : Fin k := ⟨m - 1, by omega⟩
    simpa [vinogradovFullMoment, m', Nat.sub_add_cancel hm1]
      using congrFun hmom m'
  have hesymm := multiset_esymm_eq_of_powerSums_eq
    (R := ZMod (p ^ k)) (fun i => (x i : ZMod (p ^ k)))
      (fun i => (y i : ZMod (p ^ k)))
      (fun m hm => zmod_primePow_natCast_isUnit hp
        (Finset.mem_Icc.mp hm).1 (lt_of_le_of_lt (Finset.mem_Icc.mp hm).2 hpk))
      hpow
  have hpoly := vinogradovTuplePolynomial_eq_of_esymm_eq
    (fun i => (x i : ZMod (p ^ k))) (fun i => (y i : ZMod (p ^ k))) hesymm
  intro i
  have hprod : ∏ r, ((y i : ZMod (p ^ k)) - (x r : ZMod (p ^ k))) = 0 := by
    have heval := congrArg (Polynomial.eval (y i : ZMod (p ^ k))) hpoly
    have hleft : Polynomial.eval (y i : ZMod (p ^ k))
        (vinogradovTuplePolynomial fun r => (x r : ZMod (p ^ k))) =
        ∏ r, ((y i : ZMod (p ^ k)) - (x r : ZMod (p ^ k))) := by
      rw [vinogradovTuplePolynomial]
      change (Polynomial.evalRingHom (y i : ZMod (p ^ k)))
        (∏ r, (Polynomial.X - Polynomial.C (x r : ZMod (p ^ k)))) = _
      rw [map_prod]
      simp only [map_sub, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.eval_C]
    have hright : Polynomial.eval (y i : ZMod (p ^ k))
        (vinogradovTuplePolynomial fun r => (y r : ZMod (p ^ k))) = 0 := by
      rw [vinogradovTuplePolynomial]
      change (Polynomial.evalRingHom (y i : ZMod (p ^ k)))
        (∏ r, (Polynomial.X - Polynomial.C (y r : ZMod (p ^ k)))) = _
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [hleft, hright] at heval
    exact heval
  have hrestUnit : IsUnit
      (∏ r ∈ (Finset.univ : Finset (Fin k)).erase i,
        ((y i : ZMod (p ^ k)) - (x r : ZMod (p ^ k)))) := by
    rw [IsUnit.prod_iff]
    intro r hr
    rw [Finset.mem_erase] at hr
    apply isUnit_zmod_primePow_of_cast_ne_zero hp hk
    simp only [map_sub, map_natCast]
    rw [sub_ne_zero]
    rw [← hres i]
    intro heq
    exact hx i r hr.1.symm (by
      have hm := (ZMod.natCast_eq_natCast_iff (x i) (x r) p).mp heq
      simpa [Nat.ModEq] using hm)
  have hfactor :
      ((y i : ZMod (p ^ k)) - (x i : ZMod (p ^ k))) *
          (∏ r ∈ (Finset.univ : Finset (Fin k)).erase i,
            ((y i : ZMod (p ^ k)) - (x r : ZMod (p ^ k)))) = 0 := by
    calc
      _ = ∏ r, ((y i : ZMod (p ^ k)) - (x r : ZMod (p ^ k))) :=
        Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      _ = 0 := hprod
  have hz : (y i : ZMod (p ^ k)) - (x i : ZMod (p ^ k)) = 0 :=
    hrestUnit.mul_right_cancel (by simpa using hfactor)
  exact (sub_eq_zero.mp hz).symm

private theorem residueLists_perm_of_fullMoment_eq {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpk : k < p) (x y : Fin k → ℕ)
    (hmom : vinogradovFullMoment p k x = vinogradovFullMoment p k y) :
    List.Perm (List.ofFn fun i => (x i : ZMod p))
      (List.ofFn fun i => (y i : ZMod p)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ m ∈ Finset.Icc 1 k,
      ∑ i, (x i : ZMod p) ^ m = ∑ i, (y i : ZMod p) ^ m := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmk := (Finset.mem_Icc.mp hm).2
    let m' : Fin k := ⟨m - 1, by omega⟩
    have hfull : ∑ i, (x i : ZMod (p ^ k)) ^ m =
        ∑ i, (y i : ZMod (p ^ k)) ^ m := by
      simpa [vinogradovFullMoment, m', Nat.sub_add_cancel hm1]
        using congrFun hmom m'
    have hcast := congrArg
      (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)) hfull
    simpa only [map_sum, map_pow, map_natCast] using hcast
  have hesymm := multiset_esymm_eq_of_powerSums_eq
    (R := ZMod p) (fun i => (x i : ZMod p)) (fun i => (y i : ZMod p))
      (fun m hm => by
        rw [ZMod.isUnit_iff_coprime]
        exact ((hp.coprime_iff_not_dvd).mpr fun hpm =>
          (not_lt_of_ge (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hpm))
            (lt_of_le_of_lt (Finset.mem_Icc.mp hm).2 hpk)).symm)
      hpow
  have hpoly := vinogradovTuplePolynomial_eq_of_esymm_eq
    (fun i => (x i : ZMod p)) (fun i => (y i : ZMod p)) hesymm
  have hpoly' :
      ((Finset.univ.val.map (fun i => (x i : ZMod p))).map fun z =>
          Polynomial.X - Polynomial.C z).prod =
        ((Finset.univ.val.map (fun i => (y i : ZMod p))).map fun z =>
          Polynomial.X - Polynomial.C z).prod := by
    simpa [vinogradovTuplePolynomial, Finset.prod, Multiset.map_map,
      Function.comp_def] using hpoly
  have hroots := congrArg Polynomial.roots hpoly'
  rw [Polynomial.roots_multiset_prod_X_sub_C,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact Multiset.coe_eq_coe.mp (by
    simpa [List.ofFn_eq_map, Finset.val_univ_fin] using hroots)

private theorem nat_eq_of_Icc_of_zmod_eq {N a b : ℕ}
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N)
    (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have hmod := (ZMod.natCast_eq_natCast_iff a b N).mp h
  rcases Finset.mem_Icc.mp ha with ⟨ha1, haN⟩
  rcases Finset.mem_Icc.mp hb with ⟨hb1, hbN⟩
  have hab : a < b + N := by omega
  have hba : b < a + N := by omega
  have habz : (a : ℤ) < (b : ℤ) + (N : ℤ) := by exact_mod_cast hab
  have hbaz : (b : ℤ) < (a : ℤ) + (N : ℤ) := by exact_mod_cast hba
  apply hmod.eq_of_abs_lt
  rw [abs_lt]
  constructor <;> omega

/-- A nonsingular fiber of the full moment map modulo `p^k` contains at
most the `k!` coordinate permutations. -/
theorem card_fullMoment_fiber_le_factorial {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpk : k < p) (c : Fin k → ZMod (p ^ k)) :
    ((vinogradovTuples k (p ^ k)).filter fun x =>
      VinogradovWellConditioned p x ∧ vinogradovFullMoment p k x = c).card
      ≤ k.factorial := by
  classical
  let S := (vinogradovTuples k (p ^ k)).filter fun x =>
    VinogradovWellConditioned p x ∧ vinogradovFullMoment p k x = c
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · change S.card ≤ k.factorial
    simp [hS]
  have hperm : ∀ x ∈ S,
      List.Perm (List.ofFn fun i => (x i : ZMod p))
        (List.ofFn fun i => (x₀ i : ZMod p)) := by
    intro x hx
    change x ∈ (vinogradovTuples k (p ^ k)).filter (fun x =>
      VinogradovWellConditioned p x ∧ vinogradovFullMoment p k x = c) at hx
    change x₀ ∈ (vinogradovTuples k (p ^ k)).filter (fun x =>
      VinogradovWellConditioned p x ∧ vinogradovFullMoment p k x = c) at hx₀
    rw [Finset.mem_filter] at hx hx₀
    exact residueLists_perm_of_fullMoment_eq hp hk hpk x x₀ (hx.2.2.trans hx₀.2.2.symm)
  have hcard : S.card ≤
      ((List.ofFn fun i => (x₀ i : ZMod p)).permutations.toFinset).card := by
    apply Finset.card_le_card_of_injOn
      (fun x => List.ofFn fun i => (x i : ZMod p))
    · intro x hx
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
      exact hperm x (Finset.mem_coe.mp hx)
    · intro x hx y hy hxy
      have hfun : (fun i => (x i : ZMod p)) = fun i => (y i : ZMod p) :=
        List.ofFn_injective hxy
      have hxS := Finset.mem_filter.mp (show x ∈ S from Finset.mem_coe.mp hx)
      have hyS := Finset.mem_filter.mp (show y ∈ S from Finset.mem_coe.mp hy)
      have hfull := fullMoment_injective_of_same_residues hp hk hpk x y hxS.2.1
        (hxS.2.2.trans hyS.2.2.symm) (fun i => congrFun hfun i)
      funext i
      exact nat_eq_of_Icc_of_zmod_eq
        ((mem_vinogradovTuples.mp hxS.1 i) |> Finset.mem_Icc.mpr)
        ((mem_vinogradovTuples.mp hyS.1 i) |> Finset.mem_Icc.mpr) (hfull i)
  calc
    S.card ≤ ((List.ofFn fun i => (x₀ i : ZMod p)).permutations.toFinset).card := hcard
    _ ≤ (List.ofFn fun i => (x₀ i : ZMod p)).permutations.length :=
      List.toFinset_card_le _
    _ = k.factorial := by rw [List.length_permutations, List.length_ofFn]

private theorem card_castHom_fiber_le {n m : ℕ} [NeZero n] (hm : 0 < m)
    (hmn : m ∣ n) (c : ZMod m) :
    ((Finset.univ : Finset (ZMod n)).filter fun z =>
      ZMod.castHom hmn (ZMod m) z = c).card ≤ n / m := by
  classical
  let encode : ZMod n → ℕ := fun z => z.val / m
  have hmaps : Set.MapsTo encode
      ↑((Finset.univ : Finset (ZMod n)).filter fun z =>
        ZMod.castHom hmn (ZMod m) z = c) ↑(Finset.range (n / m)) := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    rw [Finset.mem_coe, Finset.mem_range]
    rw [Nat.div_lt_iff_lt_mul hm]
    calc
      z.val < n := z.val_lt
      _ = n / m * m := (Nat.div_mul_cancel hmn).symm
  have hinj : Set.InjOn encode
      ↑((Finset.univ : Finset (ZMod n)).filter fun z =>
        ZMod.castHom hmn (ZMod m) z = c) := by
    intro z hz w hw hquot
    rw [Finset.mem_coe, Finset.mem_filter] at hz hw
    apply ZMod.val_injective
    have hcast : (z.val : ZMod m) = (w.val : ZMod m) := by
      calc
        (z.val : ZMod m) = ZMod.castHom hmn (ZMod m) z := by
          rw [ZMod.castHom_apply, ← ZMod.natCast_zmod_val z]
          simp
        _ = c := hz.2
        _ = ZMod.castHom hmn (ZMod m) w := hw.2.symm
        _ = (w.val : ZMod m) := by
          rw [ZMod.castHom_apply, ← ZMod.natCast_zmod_val w]
          simp
    have hmod : z.val % m = w.val % m := by
      have := (ZMod.natCast_eq_natCast_iff z.val w.val m).mp hcast
      simpa [Nat.ModEq] using this
    change z.val / m = w.val / m at hquot
    calc
      z.val = m * (z.val / m) + z.val % m := (Nat.div_add_mod z.val m).symm
      _ = m * (w.val / m) + w.val % m := by rw [hquot, hmod]
      _ = w.val := Nat.div_add_mod w.val m
  have := Finset.card_le_card_of_injOn encode hmaps hinj
  simpa using this

/-- Full moment vectors modulo `p^k` compatible with the prescribed lower
prime-power moments of `y`. -/
def vinogradovCompatibleFullMoments (p k : ℕ) (hp : 0 < p)
    (y : Fin k → ℕ) : Finset (Fin k → ZMod (p ^ k)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne'⟩
  exact Fintype.piFinset fun j =>
    (Finset.univ : Finset (ZMod (p ^ k))).filter fun z =>
      ZMod.castHom
          (pow_dvd_pow p (Nat.succ_le_iff.mpr j.isLt))
          (ZMod (p ^ ((j : ℕ) + 1))) z =
        (vinogradovPowerSum y ((j : ℕ) + 1) :
          ZMod (p ^ ((j : ℕ) + 1)))

private theorem sum_fin_sub_succ (k : ℕ) :
    Finset.univ.sum (fun j : Fin k => k - (j.val + 1)) =
      k * (k - 1) / 2 := by
  calc
    Finset.univ.sum (fun j : Fin k => k - (j.val + 1)) =
        (Finset.range k).sum (fun j => k - (j + 1)) := by
      simpa only using
        Fin.sum_univ_eq_sum_range (fun j : ℕ => k - (j + 1)) k
    _ = (Finset.range k).sum (fun j => k - 1 - j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      omega
    _ = (Finset.range k).sum (fun j => j) := by
      simpa only using Finset.sum_range_reflect (fun j => j) k
    _ = k * (k - 1) / 2 := by
      simpa only using Finset.sum_range_id k

/-- There are at most `p^(k(k-1)/2)` full moment vectors compatible
with prescribed moments modulo `p, ..., p^k`. -/
theorem card_compatibleFullMoments_le {p k : ℕ} (hp : 0 < p)
    (y : Fin k → ℕ) :
    (vinogradovCompatibleFullMoments p k hp y).card ≤
      p ^ (k * (k - 1) / 2) := by
  classical
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne'⟩
  rw [vinogradovCompatibleFullMoments, Fintype.card_piFinset]
  calc
    (∏ j : Fin k,
        ((Finset.univ : Finset (ZMod (p ^ k))).filter fun z =>
          ZMod.castHom
              (pow_dvd_pow p (Nat.succ_le_iff.mpr j.isLt))
              (ZMod (p ^ ((j : ℕ) + 1))) z =
            (vinogradovPowerSum y ((j : ℕ) + 1) :
              ZMod (p ^ ((j : ℕ) + 1)))).card) ≤
        ∏ j : Fin k, p ^ (k - ((j : ℕ) + 1)) := by
      apply Finset.prod_le_prod'
      intro j hj
      calc
        ((Finset.univ : Finset (ZMod (p ^ k))).filter fun z =>
            ZMod.castHom
                (pow_dvd_pow p (Nat.succ_le_iff.mpr j.isLt))
                (ZMod (p ^ ((j : ℕ) + 1))) z =
              (vinogradovPowerSum y ((j : ℕ) + 1) :
                ZMod (p ^ ((j : ℕ) + 1)))).card ≤
            p ^ k / p ^ ((j : ℕ) + 1) :=
          card_castHom_fiber_le (pow_pos hp ((j : ℕ) + 1))
            (pow_dvd_pow p (Nat.succ_le_iff.mpr j.isLt)) _
        _ = p ^ (k - ((j : ℕ) + 1)) := by
          rw [Nat.pow_div (Nat.succ_le_iff.mpr j.isLt) hp]
    _ = p ^ (k * (k - 1) / 2) := by
      rw [Finset.prod_pow_eq_pow_sum]
      exact congrArg (fun n : ℕ => p ^ n) (sum_fin_sub_succ k)

/-- The mixed prime-power moment congruences in Linnik's lemma. -/
def VinogradovCongruentMoments (p k : ℕ) (x y : Fin k → ℕ) : Prop :=
  ∀ j : Fin k, Nat.ModEq (p ^ ((j : ℕ) + 1))
    (vinogradovPowerSum x ((j : ℕ) + 1))
    (vinogradovPowerSum y ((j : ℕ) + 1))

theorem vinogradovCongruentMoments_iff {p k : ℕ} {x y : Fin k → ℕ} :
    VinogradovCongruentMoments p k x y ↔
      ∀ j ∈ Finset.Icc 1 k, Nat.ModEq (p ^ j)
        (vinogradovPowerSum x j) (vinogradovPowerSum y j) := by
  constructor
  · intro h j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
    let j' : Fin k := ⟨j - 1, by omega⟩
    simpa [j', Nat.sub_add_cancel hj1] using h j'
  · intro h j
    exact h ((j : ℕ) + 1) (by simp [Finset.mem_Icc])

/-- The nonsingular `x`-fiber over a fixed `y` in Linnik's lemma. -/
noncomputable def vinogradovLinnikFiber (p k : ℕ) (y : Fin k → ℕ) :
    Finset (Fin k → ℕ) :=
  by
    classical
    exact (vinogradovTuples k (p ^ k)).filter fun x =>
      VinogradovWellConditioned p x ∧ VinogradovCongruentMoments p k x y

private theorem fullMoment_mem_compatible {p k : ℕ} (hp : 0 < p)
    {x y : Fin k → ℕ} (hxy : VinogradovCongruentMoments p k x y) :
    vinogradovFullMoment p k x ∈ vinogradovCompatibleFullMoments p k hp y := by
  classical
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne'⟩
  rw [vinogradovCompatibleFullMoments, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hzmod :
      (vinogradovPowerSum x ((j : ℕ) + 1) :
          ZMod (p ^ ((j : ℕ) + 1))) =
        (vinogradovPowerSum y ((j : ℕ) + 1) :
          ZMod (p ^ ((j : ℕ) + 1))) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hxy j)
  have hfull : vinogradovFullMoment p k x j =
      (vinogradovPowerSum x ((j : ℕ) + 1) : ZMod (p ^ k)) := by
    simp [vinogradovFullMoment, vinogradovPowerSum]
  rw [hfull, map_natCast]
  exact hzmod

/-- Fixed-`y` form of Linnik's counting lemma. -/
theorem card_vinogradovLinnikFiber_le {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hpk : k < p) (y : Fin k → ℕ) :
    (vinogradovLinnikFiber p k y).card ≤
      k.factorial * p ^ (k * (k - 1) / 2) := by
  classical
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  let S := vinogradovLinnikFiber p k y
  let T := vinogradovCompatibleFullMoments p k hp.pos y
  have hmaps : ∀ x ∈ S, vinogradovFullMoment p k x ∈ T := by
    intro x hx
    dsimp [S, vinogradovLinnikFiber] at hx
    exact fullMoment_mem_compatible hp.pos (Finset.mem_filter.mp hx).2.2
  have hfiber : ∀ c ∈ T,
      ((S.filter fun x => vinogradovFullMoment p k x = c).card ≤ k.factorial) := by
    intro c hc
    apply le_trans (Finset.card_le_card ?_)
      (card_fullMoment_fiber_le_factorial hp hk hpk c)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    have hxS := hx.1
    dsimp [S, vinogradovLinnikFiber] at hxS
    rw [Finset.mem_filter] at hxS
    exact ⟨hxS.1, hxS.2.1, hx.2⟩
  calc
    S.card ≤ k.factorial * T.card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps k.factorial hfiber
    _ ≤ k.factorial * p ^ (k * (k - 1) / 2) :=
      Nat.mul_le_mul_left _ (card_compatibleFullMoments_le hp.pos y)

/-- The pairs counted by Linnik's lemma.  The `Fin k` indexing is exactly the
system with exponents `1, ..., k`. -/
noncomputable def vinogradovLinnikSolutions (p k : ℕ) :
    Finset ((Fin k → ℕ) × (Fin k → ℕ)) := by
  classical
  exact
    ((vinogradovTuples k (p ^ k)) ×ˢ (vinogradovTuples k (p ^ k))).filter fun xy =>
      VinogradovWellConditioned p xy.1 ∧
        VinogradovCongruentMoments p k xy.1 xy.2

theorem mem_vinogradovLinnikSolutions {p k : ℕ}
    {xy : (Fin k → ℕ) × (Fin k → ℕ)} :
    xy ∈ vinogradovLinnikSolutions p k ↔
      (∀ i, 1 ≤ xy.1 i ∧ xy.1 i ≤ p ^ k) ∧
      (∀ i, 1 ≤ xy.2 i ∧ xy.2 i ≤ p ^ k) ∧
      VinogradovWellConditioned p xy.1 ∧
      ∀ j ∈ Finset.Icc 1 k, Nat.ModEq (p ^ j)
        (vinogradovPowerSum xy.1 j) (vinogradovPowerSum xy.2 j) := by
  classical
  simp only [vinogradovLinnikSolutions, Finset.mem_filter, Finset.mem_product,
    mem_vinogradovTuples, vinogradovCongruentMoments_iff]
  tauto

private theorem card_vinogradovLinnikSolutions_le_aux {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpk : k < p) :
    (vinogradovLinnikSolutions p k).card ≤
      (k.factorial * p ^ (k * (k - 1) / 2)) * (p ^ k) ^ k := by
  classical
  let S := vinogradovLinnikSolutions p k
  let T := vinogradovTuples k (p ^ k)
  have hmaps : ∀ xy ∈ S, xy.2 ∈ T := by
    intro xy hxy
    dsimp [S, vinogradovLinnikSolutions] at hxy
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).2
  have hfiber : ∀ y ∈ T,
      (S.filter fun xy => xy.2 = y).card ≤
        k.factorial * p ^ (k * (k - 1) / 2) := by
    intro y hy
    calc
      (S.filter fun xy => xy.2 = y).card ≤
          (vinogradovLinnikFiber p k y).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro xy hxy
          rw [Finset.mem_coe, Finset.mem_filter] at hxy
          rw [Finset.mem_coe]
          have hxS := hxy.1
          dsimp [S, vinogradovLinnikSolutions] at hxS
          rw [Finset.mem_filter] at hxS
          rw [vinogradovLinnikFiber, Finset.mem_filter]
          have hprod := Finset.mem_product.mp hxS.1
          exact ⟨hprod.1, hxS.2.1, by simpa [hxy.2] using hxS.2.2⟩
        · intro xy hxy zw hzw hfst
          apply Prod.ext hfst
          rw [Finset.mem_coe, Finset.mem_filter] at hxy hzw
          exact hxy.2.trans hzw.2.symm
      _ ≤ k.factorial * p ^ (k * (k - 1) / 2) :=
        card_vinogradovLinnikFiber_le hp hk hpk y
  calc
    S.card ≤ (k.factorial * p ^ (k * (k - 1) / 2)) * T.card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber
    _ = (k.factorial * p ^ (k * (k - 1) / 2)) * (p ^ k) ^ k := by
      rw [card_vinogradovTuples]

private theorem linnik_exponent_identity (k : ℕ) (hk : 1 ≤ k) :
    k * (k - 1) / 2 + k * k =
      2 * k * k - k * (k + 1) / 2 := by
  let K := k * (k - 1) / 2
  have htwo : K * 2 = k * (k - 1) := by
    dsimp [K]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd
  have hksq : k ≤ k * k := by nlinarith
  have hsum : K + K + k = k * k := by
    calc
      K + K + k = K * 2 + k := by omega
      _ = k * (k - 1) + k := by rw [htwo]
      _ = (k * k - k) + k := by rw [Nat.mul_sub_left_distrib]; simp
      _ = k * k := Nat.sub_add_cancel hksq
  have htri : k * (k + 1) / 2 = K + k := by
    dsimp [K]
    simpa [Nat.mul_comm] using Nat.triangle_succ k
  rw [htri]
  dsimp [K] at hsum ⊢
  rw [mul_assoc 2 k k]
  omega

/-- Linnik's lemma: once `y` and the lower prime-power moments are fixed,
the Newton identities leave at most `k!` permutations; the remaining lifts
contribute `p^(k(k-1)/2)`.  The hypothesis `k < p` is the standard
nonsingularity condition needed to divide by `1, ..., k`. -/
theorem linnik_lemma {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (hpk : k < p) :
    (vinogradovLinnikSolutions p k).card ≤
      k.factorial * p ^ (2 * k ^ 2 - k * (k + 1) / 2) := by
  calc
    (vinogradovLinnikSolutions p k).card ≤
        (k.factorial * p ^ (k * (k - 1) / 2)) * (p ^ k) ^ k :=
      card_vinogradovLinnikSolutions_le_aux hp (by omega) hpk
    _ = k.factorial * p ^ (k * (k - 1) / 2 + k * k) := by
      rw [← pow_mul, mul_assoc, ← pow_add]
    _ = k.factorial * p ^ (2 * k ^ 2 - k * (k + 1) / 2) := by
      congr 2
      simpa [pow_two, mul_assoc] using linnik_exponent_identity k (by omega)

private theorem tupleLists_perm_of_moments_eq {k : ℕ} {x y : Fin k → ℕ}
    (hxy : vinogradovMomentVector k x = vinogradovMomentVector k y) :
    List.Perm (List.ofFn x) (List.ofFn y) := by
  have hpow : ∀ m ∈ Finset.Icc 1 k,
      ∑ i, (x i : ℚ) ^ m = ∑ i, (y i : ℚ) ^ m := by
    intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmk⟩
    let m' : Fin k := ⟨m - 1, by omega⟩
    have hmom := congrFun hxy m'
    have hmomNat : vinogradovPowerSum x m = vinogradovPowerSum y m := by
      simpa [vinogradovMomentVector, m', Nat.sub_add_cancel hm1] using hmom
    exact_mod_cast hmomNat
  have hesymm := multiset_esymm_eq_of_powerSums_eq
    (R := ℚ) (fun i => (x i : ℚ)) (fun i => (y i : ℚ))
      (fun m hm => by
        rw [isUnit_iff_ne_zero]
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)) hpow
  have hpoly := vinogradovTuplePolynomial_eq_of_esymm_eq
    (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) hesymm
  have hpoly' :
      ((Finset.univ.val.map (fun i => (x i : ℚ))).map fun z =>
          Polynomial.X - Polynomial.C z).prod =
        ((Finset.univ.val.map (fun i => (y i : ℚ))).map fun z =>
          Polynomial.X - Polynomial.C z).prod := by
    simpa [vinogradovTuplePolynomial, Finset.prod, Multiset.map_map,
      Function.comp_def] using hpoly
  have hroots := congrArg Polynomial.roots hpoly'
  rw [Polynomial.roots_multiset_prod_X_sub_C,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
  have hcast : List.Perm (List.ofFn fun i => (x i : ℚ))
      (List.ofFn fun i => (y i : ℚ)) :=
    Multiset.coe_eq_coe.mp (by
      simpa [List.ofFn_eq_map, Finset.val_univ_fin] using hroots)
  exact (List.map_perm_map_iff
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ)))).mp (by
    simpa [List.ofFn_eq_map] using hcast)

/-- The diagonal starting point of the iteration: a solution with exactly
`k` variables on each side differs only by a permutation. -/
theorem vinogradovJ_diagonal (k P : ℕ) :
    vinogradovJ k k P ≤ k.factorial * P ^ k := by
  classical
  let S := ((vinogradovTuples k P) ×ˢ (vinogradovTuples k P)).filter
    fun xy : (Fin k → ℕ) × (Fin k → ℕ) =>
      vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2
  let T := vinogradovTuples k P
  have hmaps : ∀ xy ∈ S, xy.1 ∈ T := by
    intro xy hxy
    dsimp [S, T] at hxy ⊢
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).1
  have hfiber : ∀ x ∈ T,
      (S.filter fun xy => xy.1 = x).card ≤ k.factorial := by
    intro x hx
    let U := (List.ofFn x).permutations.toFinset
    calc
      (S.filter fun xy => xy.1 = x).card ≤ U.card := by
        apply Finset.card_le_card_of_injOn (fun xy => List.ofFn xy.2)
        · intro xy hxy
          rw [Finset.mem_coe, Finset.mem_filter] at hxy
          rw [Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
          have hxyS := hxy.1
          dsimp [S] at hxyS
          rw [Finset.mem_filter] at hxyS
          exact tupleLists_perm_of_moments_eq
            (hxy.2 ▸ hxyS.2).symm
        · intro xy hxy zw hzw heq
          apply Prod.ext
          · rw [(Finset.mem_filter.mp (Finset.mem_coe.mp hxy)).2,
              (Finset.mem_filter.mp (Finset.mem_coe.mp hzw)).2]
          · exact List.ofFn_injective heq
      _ ≤ (List.ofFn x).permutations.length := List.toFinset_card_le _
      _ = k.factorial := by rw [List.length_permutations, List.length_ofFn]
  rw [vinogradovJ_eq_pairCount, vinogradovPairCount]
  change S.card ≤ k.factorial * P ^ k
  calc
    S.card ≤ k.factorial * T.card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber
    _ = k.factorial * P ^ k := by rw [card_vinogradovTuples]

/-! ## A finite Fourier form of the Hölder step -/

private noncomputable def vinogradovVectorChar (N k : ℕ) [NeZero N]
    (a z : Fin k → ZMod N) : ℂ :=
  ∏ j, ZMod.stdAddChar (a j * z j)

private theorem vinogradovVectorChar_add {N k : ℕ} [NeZero N]
    (a z w : Fin k → ZMod N) :
    vinogradovVectorChar N k a (z + w) =
      vinogradovVectorChar N k a z * vinogradovVectorChar N k a w := by
  simp only [vinogradovVectorChar, Pi.add_apply, mul_add,
    AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

private theorem vinogradovVectorChar_neg {N k : ℕ} [NeZero N]
    (a z : Fin k → ZMod N) :
    vinogradovVectorChar N k a (-z) =
      starRingEnd ℂ (vinogradovVectorChar N k a z) := by
  simp only [vinogradovVectorChar]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Pi.neg_apply, mul_neg,
    AddChar.map_neg_eq_inv]
  simpa [ZMod.stdAddChar_apply] using
    Circle.coe_inv_eq_conj (ZMod.toCircle (a j * z j))

private theorem vinogradovVectorChar_sub {N k : ℕ} [NeZero N]
    (a z w : Fin k → ZMod N) :
    vinogradovVectorChar N k a (z - w) =
      vinogradovVectorChar N k a z *
        starRingEnd ℂ (vinogradovVectorChar N k a w) := by
  rw [sub_eq_add_neg, vinogradovVectorChar_add, vinogradovVectorChar_neg]

private theorem sum_stdAddChar_mul (N : ℕ) [NeZero N] (z : ZMod N) :
    ∑ a : ZMod N, ZMod.stdAddChar (a * z) =
      if z = 0 then (N : ℂ) else 0 := by
  split_ifs with hz
  · simp [hz, ZMod.card]
  · simpa [mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N hz)

private theorem sum_vinogradovVectorChar (N k : ℕ) [NeZero N]
    (z : Fin k → ZMod N) :
    ∑ a : Fin k → ZMod N, vinogradovVectorChar N k a z =
      if z = 0 then (N : ℂ) ^ k else 0 := by
  simp only [vinogradovVectorChar]
  rw [show (∑ a : Fin k → ZMod N,
      ∏ j, ZMod.stdAddChar (a j * z j)) =
        ∏ j : Fin k, ∑ a : ZMod N, ZMod.stdAddChar (a * z j) from
      (Fintype.prod_sum fun j (a : ZMod N) => ZMod.stdAddChar (a * z j)).symm]
  simp_rw [sum_stdAddChar_mul]
  by_cases hz : z = 0
  · subst z
    simp
  · have hcoord : ∃ j : Fin k, z j ≠ 0 := by
      simpa [Function.ne_iff] using hz
    rcases hcoord with ⟨j, hj⟩
    simp only [hz, if_false]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

private noncomputable def vinogradovVectorAddChar (N k : ℕ) [NeZero N]
    (a : Fin k → ZMod N) : AddChar (Fin k → ZMod N) ℂ where
  toFun := vinogradovVectorChar N k a
  map_zero_eq_one' := by simp [vinogradovVectorChar]
  map_add_eq_mul' := vinogradovVectorChar_add a

private theorem vinogradovVectorChar_sum {N k r : ℕ} [NeZero N]
    (a : Fin k → ZMod N) (z : Fin r → Fin k → ZMod N) :
    vinogradovVectorChar N k a (∑ i, z i) =
      ∏ i, vinogradovVectorChar N k a (z i) := by
  classical
  let χ := vinogradovVectorAddChar N k a
  change χ (∑ i, z i) = ∏ i, χ (z i)
  have hgen : ∀ s : Finset (Fin r),
      χ (∑ i ∈ s, z i) = ∏ i ∈ s, χ (z i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi,
          AddChar.map_add_eq_mul, ih]
  simpa using hgen Finset.univ

private noncomputable def vinogradovResidueExpSum {N k : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N) (A : Finset α)
    (a : Fin k → ZMod N) : ℂ :=
  ∑ x ∈ A, vinogradovVectorChar N k a (φ x)

private noncomputable def vinogradovMixedEnergy {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N)
    (A B : Fin r → Finset α) : ℕ := by
  classical
  exact ((Fintype.piFinset A ×ˢ Fintype.piFinset B).filter fun xy =>
    (∑ i, φ (xy.1 i)) = ∑ i, φ (xy.2 i)).card

private theorem sum_char_tuple {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N) (A : Fin r → Finset α)
    (a : Fin k → ZMod N) :
    (∑ x ∈ Fintype.piFinset A,
        vinogradovVectorChar N k a (∑ i, φ (x i))) =
      ∏ i, vinogradovResidueExpSum φ (A i) a := by
  classical
  simp_rw [vinogradovVectorChar_sum]
  simpa only [vinogradovResidueExpSum] using
    (Finset.prod_univ_sum A
      (fun i x => vinogradovVectorChar N k a (φ x))).symm

private theorem sum_pair_char {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N)
    (A B : Fin r → Finset α) (a : Fin k → ZMod N) :
    (∑ xy ∈ Fintype.piFinset A ×ˢ Fintype.piFinset B,
        vinogradovVectorChar N k a
          ((∑ i, φ (xy.1 i)) - ∑ i, φ (xy.2 i))) =
      (∏ i, vinogradovResidueExpSum φ (A i) a) *
        starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a) := by
  classical
  calc
    (∑ xy ∈ Fintype.piFinset A ×ˢ Fintype.piFinset B,
        vinogradovVectorChar N k a
          ((∑ i, φ (xy.1 i)) - ∑ i, φ (xy.2 i))) =
        (∑ x ∈ Fintype.piFinset A,
          vinogradovVectorChar N k a (∑ i, φ (x i))) *
        (∑ y ∈ Fintype.piFinset B,
          starRingEnd ℂ (vinogradovVectorChar N k a (∑ i, φ (y i)))) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [vinogradovVectorChar_sub]
    _ = (∑ x ∈ Fintype.piFinset A,
          vinogradovVectorChar N k a (∑ i, φ (x i))) *
        starRingEnd ℂ (∑ y ∈ Fintype.piFinset B,
          vinogradovVectorChar N k a (∑ i, φ (y i))) := by
      rw [map_sum]
    _ = (∏ i, vinogradovResidueExpSum φ (A i) a) *
        starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a) := by
      rw [sum_char_tuple, sum_char_tuple]

private theorem mixedEnergy_fourier {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N)
    (A B : Fin r → Finset α) :
    ((N : ℂ) ^ k) * (vinogradovMixedEnergy φ A B : ℂ) =
      ∑ a : Fin k → ZMod N,
        (∏ i, vinogradovResidueExpSum φ (A i) a) *
          starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a) := by
  classical
  simp_rw [← sum_pair_char φ A B]
  rw [Finset.sum_comm]
  simp_rw [sum_vinogradovVectorChar]
  rw [vinogradovMixedEnergy]
  simp only [sub_eq_zero]
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem prod_le_sum_pow_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∏ i, f i) ≤ ∑ i, f i ^ Fintype.card ι := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) f Finset.univ_nonempty
  calc
    (∏ i, f i) ≤ ∏ _i : ι, f i₀ := by
      apply Finset.prod_le_prod
      · exact fun i hi => hf i
      · intro i hi
        exact hmax i (Finset.mem_univ i)
    _ = f i₀ ^ Fintype.card ι := by simp
    _ ≤ ∑ i, f i ^ Fintype.card ι := by
      exact Finset.single_le_sum (fun i _ => pow_nonneg (hf i) _)
        (Finset.mem_univ i₀)

private theorem mixed_norm_prod_le_sum {N k r : ℕ} [NeZero N]
    (hr : 0 < r) {α : Type*} (φ : α → Fin k → ZMod N)
    (A B : Fin r → Finset α) (a : Fin k → ZMod N) :
    (∏ i, ‖vinogradovResidueExpSum φ (A i) a‖) *
        (∏ i, ‖vinogradovResidueExpSum φ (B i) a‖) ≤
      (∑ i, ‖vinogradovResidueExpSum φ (A i) a‖ ^ (2 * r)) +
        ∑ i, ‖vinogradovResidueExpSum φ (B i) a‖ ^ (2 * r) := by
  let f : Fin r ⊕ Fin r → ℝ := fun i => Sum.elim
    (fun j => ‖vinogradovResidueExpSum φ (A j) a‖)
    (fun j => ‖vinogradovResidueExpSum φ (B j) a‖) i
  have hnonempty : Nonempty (Fin r ⊕ Fin r) := by
    exact ⟨Sum.inl ⟨0, hr⟩⟩
  have h := @prod_le_sum_pow_card (Fin r ⊕ Fin r) _ hnonempty f
    (fun i => by rcases i with i | i <;> simp [f])
  simpa only [f, Fintype.prod_sum_type, Fintype.sum_sum_type,
    Fintype.card_sum, Fintype.card_fin, two_mul, Sum.elim_inl, Sum.elim_inr]
    using h

private theorem diagonalEnergy_fourier_real {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N) (C : Finset α) :
    (N : ℝ) ^ k * (vinogradovMixedEnergy φ (fun _ : Fin r => C)
        (fun _ : Fin r => C) : ℝ) =
      ∑ a : Fin k → ZMod N,
        ‖vinogradovResidueExpSum φ C a‖ ^ (2 * r) := by
  have h := mixedEnergy_fourier φ (fun _ : Fin r => C) (fun _ : Fin r => C)
  have hrhs :
      (∑ a : Fin k → ZMod N,
        (∏ _i : Fin r, vinogradovResidueExpSum φ C a) *
          starRingEnd ℂ (∏ _i : Fin r, vinogradovResidueExpSum φ C a)) =
        ∑ a : Fin k → ZMod N,
          ((‖vinogradovResidueExpSum φ C a‖ ^ (2 * r) : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Complex.mul_conj', norm_pow]
    push_cast
    rw [← pow_mul]
    rw [mul_comm r 2]
  rw [hrhs] at h
  exact_mod_cast h

/-- Finite Fourier Hölder: a mixed additive energy is bounded by the sum
of the diagonal energies of its `2r` coordinate classes. -/
private theorem mixedEnergy_le_sum_diagonal {N k r : ℕ} [NeZero N]
    (hr : 0 < r) {α : Type*} (φ : α → Fin k → ZMod N)
    (A B : Fin r → Finset α) :
    vinogradovMixedEnergy φ A B ≤
      (∑ i, vinogradovMixedEnergy φ (fun _ : Fin r => A i)
        (fun _ : Fin r => A i)) +
      ∑ i, vinogradovMixedEnergy φ (fun _ : Fin r => B i)
        (fun _ : Fin r => B i) := by
  have hfourier := mixedEnergy_fourier φ A B
  have hN : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast NeZero.pos N) k
  have hdiagA :
      (∑ a : Fin k → ZMod N,
          ∑ i, ‖vinogradovResidueExpSum φ (A i) a‖ ^ (2 * r)) =
        (N : ℝ) ^ k *
          ∑ i, (vinogradovMixedEnergy φ (fun _ : Fin r => A i)
            (fun _ : Fin r => A i) : ℝ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (diagonalEnergy_fourier_real φ (A i)).symm
  have hdiagB :
      (∑ a : Fin k → ZMod N,
          ∑ i, ‖vinogradovResidueExpSum φ (B i) a‖ ^ (2 * r)) =
        (N : ℝ) ^ k *
          ∑ i, (vinogradovMixedEnergy φ (fun _ : Fin r => B i)
            (fun _ : Fin r => B i) : ℝ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (diagonalEnergy_fourier_real φ (B i)).symm
  have hbound :
      (N : ℝ) ^ k * (vinogradovMixedEnergy φ A B : ℝ) ≤
        (N : ℝ) ^ k *
          ((∑ i, vinogradovMixedEnergy φ (fun _ : Fin r => A i)
              (fun _ : Fin r => A i)) +
            ∑ i, vinogradovMixedEnergy φ (fun _ : Fin r => B i)
              (fun _ : Fin r => B i) : ℕ) := by
    calc
      (N : ℝ) ^ k * (vinogradovMixedEnergy φ A B : ℝ) =
          ‖((N : ℂ) ^ k) * (vinogradovMixedEnergy φ A B : ℂ)‖ := by
        simp [norm_pow]
      _ = ‖∑ a : Fin k → ZMod N,
          (∏ i, vinogradovResidueExpSum φ (A i) a) *
            starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a)‖ := by
        rw [hfourier]
      _ ≤ ∑ a : Fin k → ZMod N,
          ‖(∏ i, vinogradovResidueExpSum φ (A i) a) *
            starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a)‖ :=
        norm_sum_le _ _
      _ = ∑ a : Fin k → ZMod N,
          (∏ i, ‖vinogradovResidueExpSum φ (A i) a‖) *
            ∏ i, ‖vinogradovResidueExpSum φ (B i) a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [norm_prod]
      _ ≤ ∑ a : Fin k → ZMod N,
          ((∑ i, ‖vinogradovResidueExpSum φ (A i) a‖ ^ (2 * r)) +
            ∑ i, ‖vinogradovResidueExpSum φ (B i) a‖ ^ (2 * r)) := by
        exact Finset.sum_le_sum fun a ha => mixed_norm_prod_le_sum hr φ A B a
      _ = (N : ℝ) ^ k *
          ((∑ i, vinogradovMixedEnergy φ (fun _ : Fin r => A i)
              (fun _ : Fin r => A i)) +
            ∑ i, vinogradovMixedEnergy φ (fun _ : Fin r => B i)
              (fun _ : Fin r => B i) : ℕ) := by
        rw [Finset.sum_add_distrib, hdiagA, hdiagB]
        push_cast
        ring
  exact_mod_cast (le_of_mul_le_mul_left hbound hN)

/-! ## Residue classes and exact diagonal energies -/

/-- A modulus large enough that equality modulo it detects equality of every
power sum occurring for `r` variables in `[1,P]`. -/
private def vinogradovSafeModulus (r k P : ℕ) : ℕ :=
  r * (P + 1) ^ k + 1

private theorem vinogradovSafeModulus_pos (r k P : ℕ) :
    0 < vinogradovSafeModulus r k P := by
  simp [vinogradovSafeModulus]

private def vinogradovModCurve (N k : ℕ) (n : ℕ) : Fin k → ZMod N :=
  fun j => (n ^ ((j : ℕ) + 1) : ZMod N)

private theorem vinogradovPowerSum_lt_safeModulus {r k P j : ℕ}
    (hj : j ≤ k) (x : Fin r → ℕ) (hx : ∀ i, x i ≤ P) :
    vinogradovPowerSum x j < vinogradovSafeModulus r k P := by
  have hterm : ∀ i : Fin r, x i ^ j ≤ (P + 1) ^ k := by
    intro i
    calc
      x i ^ j ≤ (P + 1) ^ j :=
        Nat.pow_le_pow_left ((hx i).trans (Nat.le_succ P)) j
      _ ≤ (P + 1) ^ k := Nat.pow_le_pow_right (by omega : 0 < P + 1) hj
  calc
    vinogradovPowerSum x j ≤ ∑ _i : Fin r, (P + 1) ^ k := by
      exact Finset.sum_le_sum fun i hi => hterm i
    _ = r * (P + 1) ^ k := by simp
    _ < vinogradovSafeModulus r k P := by
      simp [vinogradovSafeModulus]

private theorem modCurve_sum_eq_iff_powerSums_eq {r k P : ℕ}
    (x y : Fin r → ℕ) (hx : ∀ i, x i ≤ P) (hy : ∀ i, y i ≤ P) :
    (∑ i, vinogradovModCurve (vinogradovSafeModulus r k P) k (x i)) =
        ∑ i, vinogradovModCurve (vinogradovSafeModulus r k P) k (y i) ↔
      vinogradovMomentVector k x = vinogradovMomentVector k y := by
  let N := vinogradovSafeModulus r k P
  have hN : 0 < N := vinogradovSafeModulus_pos r k P
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    have hcast :
        (vinogradovPowerSum x ((j : ℕ) + 1) : ZMod N) =
          (vinogradovPowerSum y ((j : ℕ) + 1) : ZMod N) := by
      simpa [vinogradovModCurve, vinogradovPowerSum] using hj
    have hmod : Nat.ModEq N (vinogradovPowerSum x ((j : ℕ) + 1))
        (vinogradovPowerSum y ((j : ℕ) + 1)) := by
      simpa [ZMod.natCast_eq_natCast_iff] using hcast
    exact Nat.ModEq.eq_of_lt_of_lt hmod
      (vinogradovPowerSum_lt_safeModulus (Nat.succ_le_of_lt j.isLt) x hx)
      (vinogradovPowerSum_lt_safeModulus (Nat.succ_le_of_lt j.isLt) y hy)
  · intro h
    funext j
    simpa [vinogradovModCurve, vinogradovMomentVector, vinogradovPowerSum]
      using congrArg (fun n : ℕ => (n : ZMod N)) (congrFun h j)

private theorem vinogradovPowerSum_mul {r : ℕ} (x : Fin r → ℕ)
    (p j : ℕ) :
    vinogradovPowerSum (fun i => p * x i) j =
      p ^ j * vinogradovPowerSum x j := by
  simp [vinogradovPowerSum, mul_pow, Finset.mul_sum]

/-- Dividing two tuples in one residue class by the common modulus preserves
all moment equations.  This is the triangular binomial argument behind the
quotient step in Linnik's method. -/
private theorem agreeUpTo_div_of_same_mod {r k p a : ℕ}
    (hp : 0 < p) (x y : Fin r → ℕ)
    (hxmod : ∀ i, x i % p = a) (hymod : ∀ i, y i % p = a)
    (hxy : VinogradovAgreeUpTo k x y) :
    VinogradovAgreeUpTo k (fun i => x i / p) (fun i => y i / p) := by
  have hxrepr : x = fun i => p * (x i / p) + a := by
    funext i
    calc
      x i = p * (x i / p) + x i % p := (Nat.div_add_mod (x i) p).symm
      _ = p * (x i / p) + a := by rw [hxmod i]
  have hyrepr : y = fun i => p * (y i / p) + a := by
    funext i
    calc
      y i = p * (y i / p) + y i % p := (Nat.div_add_mod (y i) p).symm
      _ = p * (y i / p) + a := by rw [hymod i]
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hs := hxy j hj
      rw [hxrepr, hyrepr, vinogradovPowerSum_add,
        vinogradovPowerSum_add] at hs
      simp_rw [vinogradovPowerSum_mul] at hs
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hs
      have hlo :
          (∑ l ∈ Finset.range j,
              (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => x i / p) l)) =
            ∑ l ∈ Finset.range j,
              (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => y i / p) l) := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [ih l (Finset.mem_range.mp hl)
          (le_trans (Nat.le_of_lt (Finset.mem_range.mp hl)) hj)]
      rw [hlo] at hs
      have htop :
          p ^ j * vinogradovPowerSum (fun i => x i / p) j =
            p ^ j * vinogradovPowerSum (fun i => y i / p) j := by
        simpa using Nat.add_left_cancel hs
      exact Nat.mul_left_cancel (pow_pos hp j) htop

private def vinogradovResidueClass (P p a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 P).filter fun n => n % p = a

private theorem mem_vinogradovResidueClass {P p a n : ℕ} :
    n ∈ vinogradovResidueClass P p a ↔
      1 ≤ n ∧ n ≤ P ∧ n % p = a := by
  simp [vinogradovResidueClass, Finset.mem_Icc, and_assoc]

private theorem eq_of_div_eq_of_mod_eq {p a m n : ℕ}
    (hm : m % p = a) (hn : n % p = a) (hdiv : m / p = n / p) :
    m = n := by
  calc
    m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
    _ = p * (n / p) + n % p := by rw [hdiv, hm, hn]
    _ = n := Nat.div_add_mod n p

/-- The diagonal energy of one residue class is bounded by the Vinogradov
energy at the quotient scale.  Adding `1` places the quotients back in the
normal interval `[1, P / p + 1]`. -/
private theorem diagonalResidueEnergy_le_vinogradovJ
    {r k P p a : ℕ} (hp : 0 < p) :
    let N := vinogradovSafeModulus r k P
    letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k P)⟩
    vinogradovMixedEnergy (vinogradovModCurve N k)
        (fun _ : Fin r => vinogradovResidueClass P p a)
        (fun _ : Fin r => vinogradovResidueClass P p a) ≤
      vinogradovJ r k (P / p + 1) := by
  classical
  dsimp only
  let N := vinogradovSafeModulus r k P
  letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k P)⟩
  let C := vinogradovResidueClass P p a
  let S := ((Fintype.piFinset (fun _ : Fin r => C)) ×ˢ
      Fintype.piFinset (fun _ : Fin r => C)).filter fun xy =>
        (∑ i, vinogradovModCurve N k (xy.1 i)) =
          ∑ i, vinogradovModCurve N k (xy.2 i)
  let T := ((vinogradovTuples r (P / p + 1)) ×ˢ
      vinogradovTuples r (P / p + 1)).filter fun xy =>
        IsVinogradovSolution k xy.1 xy.2
  let q : ((Fin r → ℕ) × (Fin r → ℕ)) →
      ((Fin r → ℕ) × (Fin r → ℕ)) := fun xy =>
    (fun i => xy.1 i / p + 1, fun i => xy.2 i / p + 1)
  change S.card ≤ T.card
  apply Finset.card_le_card_of_injOn q
  · intro xy hxy
    rw [Finset.mem_coe] at hxy ⊢
    dsimp [S] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    have hxC : ∀ i, xy.1 i ∈ C := by
      simpa only [Fintype.mem_piFinset] using hxy.1.1
    have hyC : ∀ i, xy.2 i ∈ C := by
      simpa only [Fintype.mem_piFinset] using hxy.1.2
    have hxdata : ∀ i, 1 ≤ xy.1 i ∧ xy.1 i ≤ P ∧ xy.1 i % p = a := by
      intro i
      exact mem_vinogradovResidueClass.mp (by simpa [C] using hxC i)
    have hydata : ∀ i, 1 ≤ xy.2 i ∧ xy.2 i ≤ P ∧ xy.2 i % p = a := by
      intro i
      exact mem_vinogradovResidueClass.mp (by simpa [C] using hyC i)
    have hmom : vinogradovMomentVector k xy.1 =
        vinogradovMomentVector k xy.2 :=
      (modCurve_sum_eq_iff_powerSums_eq xy.1 xy.2
        (fun i => (hxdata i).2.1) (fun i => (hydata i).2.1)).mp hxy.2
    have hdiv : IsVinogradovSolution k (fun i => xy.1 i / p)
        (fun i => xy.2 i / p) := by
      rw [isVinogradovSolution_iff_agreeUpTo]
      exact agreeUpTo_div_of_same_mod hp xy.1 xy.2
        (fun i => (hxdata i).2.2) (fun i => (hydata i).2.2)
        (isVinogradovSolution_iff_agreeUpTo.mp
          (isVinogradovSolution_iff_momentVector_eq.mpr hmom))
    dsimp [T, q]
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨mem_vinogradovTuples.mpr fun i => ⟨Nat.succ_pos _, ?_⟩,
      mem_vinogradovTuples.mpr fun i => ⟨Nat.succ_pos _, ?_⟩⟩, ?_⟩
    · exact Nat.add_le_add_right (Nat.div_le_div_right (hxdata i).2.1) 1
    · exact Nat.add_le_add_right (Nat.div_le_div_right (hydata i).2.1) 1
    · exact (isVinogradovSolution_add_iff
        (fun i => xy.1 i / p) (fun i => xy.2 i / p) 1).mpr hdiv
  · intro xy hxy zw hzw heq
    apply Prod.ext
    · funext i
      have hdiv : xy.1 i / p = zw.1 i / p := by
        have := congrFun (congrArg Prod.fst heq) i
        dsimp [q] at this
        omega
      have hxyS := Finset.mem_coe.mp hxy
      have hzwS := Finset.mem_coe.mp hzw
      dsimp [S] at hxyS hzwS
      rw [Finset.mem_filter, Finset.mem_product] at hxyS hzwS
      have hxC : xy.1 i ∈ C := by
        exact (Fintype.mem_piFinset.mp hxyS.1.1) i
      have hzC : zw.1 i ∈ C := by
        exact (Fintype.mem_piFinset.mp hzwS.1.1) i
      exact eq_of_div_eq_of_mod_eq
        (mem_vinogradovResidueClass.mp (by simpa [C] using hxC)).2.2
        (mem_vinogradovResidueClass.mp (by simpa [C] using hzC)).2.2 hdiv
    · funext i
      have hdiv : xy.2 i / p = zw.2 i / p := by
        have := congrFun (congrArg Prod.snd heq) i
        dsimp [q] at this
        omega
      have hxyS := Finset.mem_coe.mp hxy
      have hzwS := Finset.mem_coe.mp hzw
      dsimp [S] at hxyS hzwS
      rw [Finset.mem_filter, Finset.mem_product] at hxyS hzwS
      have hxC : xy.2 i ∈ C := by
        exact (Fintype.mem_piFinset.mp hxyS.1.2) i
      have hzC : zw.2 i ∈ C := by
        exact (Fintype.mem_piFinset.mp hzwS.1.2) i
      exact eq_of_div_eq_of_mod_eq
        (mem_vinogradovResidueClass.mp (by simpa [C] using hxC)).2.2
        (mem_vinogradovResidueClass.mp (by simpa [C] using hzC)).2.2 hdiv

/-- The residue-pattern form of the finite Hölder step.  Arbitrary residue
classes in the `2r` positions cost only their number, while every diagonal
term is the Vinogradov energy at the quotient scale. -/
private theorem residuePatternEnergy_le {r k P p : ℕ} (hp : 0 < p)
    (hr : 0 < r) (u v : Fin r → ℕ) :
    let N := vinogradovSafeModulus r k P
    letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k P)⟩
    vinogradovMixedEnergy (vinogradovModCurve N k)
        (fun i => vinogradovResidueClass P p (u i))
        (fun i => vinogradovResidueClass P p (v i)) ≤
      2 * r * vinogradovJ r k (P / p + 1) := by
  dsimp only
  let N := vinogradovSafeModulus r k P
  letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k P)⟩
  calc
    vinogradovMixedEnergy (vinogradovModCurve N k)
        (fun i => vinogradovResidueClass P p (u i))
        (fun i => vinogradovResidueClass P p (v i)) ≤
      (∑ i, vinogradovMixedEnergy (vinogradovModCurve N k)
          (fun _ : Fin r => vinogradovResidueClass P p (u i))
          (fun _ : Fin r => vinogradovResidueClass P p (u i))) +
        ∑ i, vinogradovMixedEnergy (vinogradovModCurve N k)
          (fun _ : Fin r => vinogradovResidueClass P p (v i))
          (fun _ : Fin r => vinogradovResidueClass P p (v i)) :=
      mixedEnergy_le_sum_diagonal hr _ _ _
    _ ≤ (∑ _i : Fin r, vinogradovJ r k (P / p + 1)) +
        ∑ _i : Fin r, vinogradovJ r k (P / p + 1) := by
      exact add_le_add
        (Finset.sum_le_sum fun i hi => diagonalResidueEnergy_le_vinogradovJ hp)
        (Finset.sum_le_sum fun i hi => diagonalResidueEnergy_le_vinogradovJ hp)
    _ = 2 * r * vinogradovJ r k (P / p + 1) := by
      simp [two_mul, add_mul]

/-! ## Hölder with a distinguished nonsingular block -/

private noncomputable def vinogradovBlockExpSum {N k : ℕ} [NeZero N]
    {α : Type*} (ψ : α → Fin k → ZMod N) (W : Finset α)
    (a : Fin k → ZMod N) : ℂ :=
  ∑ x ∈ W, vinogradovVectorChar N k a (ψ x)

private noncomputable def vinogradovSelectedEnergy {N k r : ℕ} [NeZero N]
    {α β : Type*} (ψ : α → Fin k → ZMod N) (W : Finset α)
    (φ : β → Fin k → ZMod N) (A B : Fin r → Finset β) : ℕ := by
  classical
  exact (((W ×ˢ W) ×ˢ
      (Fintype.piFinset A ×ˢ Fintype.piFinset B)).filter fun z =>
        ψ z.1.1 + ∑ i, φ (z.2.1 i) =
          ψ z.1.2 + ∑ i, φ (z.2.2 i)).card

private theorem sum_block_pair_char {N k : ℕ} [NeZero N]
    {α : Type*} (ψ : α → Fin k → ZMod N) (W : Finset α)
    (a : Fin k → ZMod N) :
    (∑ uv ∈ W ×ˢ W,
        vinogradovVectorChar N k a (ψ uv.1 - ψ uv.2)) =
      vinogradovBlockExpSum ψ W a *
        starRingEnd ℂ (vinogradovBlockExpSum ψ W a) := by
  classical
  rw [Finset.sum_product]
  simp_rw [vinogradovVectorChar_sub]
  simp only [vinogradovBlockExpSum]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]

private theorem selectedEnergy_fourier {N k r : ℕ} [NeZero N]
    {α β : Type*} (ψ : α → Fin k → ZMod N) (W : Finset α)
    (φ : β → Fin k → ZMod N) (A B : Fin r → Finset β) :
    ((N : ℂ) ^ k) * (vinogradovSelectedEnergy ψ W φ A B : ℂ) =
      ∑ a : Fin k → ZMod N,
        (vinogradovBlockExpSum ψ W a *
          starRingEnd ℂ (vinogradovBlockExpSum ψ W a)) *
        ((∏ i, vinogradovResidueExpSum φ (A i) a) *
          starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a)) := by
  classical
  symm
  calc
    (∑ a : Fin k → ZMod N,
        (vinogradovBlockExpSum ψ W a *
          starRingEnd ℂ (vinogradovBlockExpSum ψ W a)) *
        ((∏ i, vinogradovResidueExpSum φ (A i) a) *
          starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a))) =
      ∑ a : Fin k → ZMod N,
        (∑ uv ∈ W ×ˢ W,
          vinogradovVectorChar N k a (ψ uv.1 - ψ uv.2)) *
        (∑ xy ∈ Fintype.piFinset A ×ˢ Fintype.piFinset B,
          vinogradovVectorChar N k a
            ((∑ i, φ (xy.1 i)) - ∑ i, φ (xy.2 i))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [sum_block_pair_char, sum_pair_char]
    _ = ∑ a : Fin k → ZMod N,
        ∑ z ∈ (W ×ˢ W) ×ˢ
            (Fintype.piFinset A ×ˢ Fintype.piFinset B),
          vinogradovVectorChar N k a
            ((ψ z.1.1 + ∑ i, φ (z.2.1 i)) -
              (ψ z.1.2 + ∑ i, φ (z.2.2 i))) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.sum_product]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [← vinogradovVectorChar_add]
        congr 1
        abel
    _ = ∑ z ∈ (W ×ˢ W) ×ˢ
            (Fintype.piFinset A ×ˢ Fintype.piFinset B),
          ∑ a : Fin k → ZMod N,
            vinogradovVectorChar N k a
              ((ψ z.1.1 + ∑ i, φ (z.2.1 i)) -
                (ψ z.1.2 + ∑ i, φ (z.2.2 i))) := by
        rw [Finset.sum_comm]
    _ = ((N : ℂ) ^ k) * (vinogradovSelectedEnergy ψ W φ A B : ℂ) := by
        simp_rw [sum_vinogradovVectorChar]
        simp only [sub_eq_zero]
        rw [vinogradovSelectedEnergy, ← Finset.sum_filter]
        simp [mul_comm]

private theorem selectedEnergy_fourier_factor {N k r : ℕ} [NeZero N]
    {α β : Type*} (ψ : α → Fin k → ZMod N) (W : Finset α)
    (φ : β → Fin k → ZMod N) (A B : Fin r → Finset β) :
    ((N : ℂ) ^ k) * (vinogradovSelectedEnergy ψ W φ A B : ℂ) =
      ∑ a : Fin k → ZMod N,
        (vinogradovBlockExpSum ψ W a *
          starRingEnd ℂ (vinogradovBlockExpSum ψ W a)) *
        ((∏ i, vinogradovResidueExpSum φ (A i) a) *
          starRingEnd ℂ (∏ i, vinogradovResidueExpSum φ (B i) a)) :=
  selectedEnergy_fourier ψ W φ A B

private theorem selectedDiagonalEnergy_fourier_real {N k r : ℕ} [NeZero N]
    {α β : Type*} (ψ : α → Fin k → ZMod N) (W : Finset α)
    (φ : β → Fin k → ZMod N) (C : Finset β) :
    (N : ℝ) ^ k * (vinogradovSelectedEnergy ψ W φ
        (fun _ : Fin r => C) (fun _ : Fin r => C) : ℝ) =
      ∑ a : Fin k → ZMod N,
        ‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
          ‖vinogradovResidueExpSum φ C a‖ ^ (2 * r) := by
  have h := selectedEnergy_fourier ψ W φ
    (fun _ : Fin r => C) (fun _ : Fin r => C)
  have hrhs :
      (∑ a : Fin k → ZMod N,
        (vinogradovBlockExpSum ψ W a *
          starRingEnd ℂ (vinogradovBlockExpSum ψ W a)) *
        ((∏ _i : Fin r, vinogradovResidueExpSum φ C a) *
          starRingEnd ℂ (∏ _i : Fin r,
            vinogradovResidueExpSum φ C a))) =
        ∑ a : Fin k → ZMod N,
          ((‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
            ‖vinogradovResidueExpSum φ C a‖ ^ (2 * r) : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Complex.mul_conj', Complex.mul_conj', norm_pow]
    push_cast
    rw [← pow_mul, mul_comm r 2]
  rw [hrhs] at h
  exact_mod_cast h

/-- Hölder with the nonsingular block left untouched.  This is the precise
finite counting analogue of Vaughan's `|g(α)|² |f(α)|^{2r}` step. -/
private theorem selectedEnergy_le_sum_diagonal {N k r : ℕ} [NeZero N]
    (hr : 0 < r) {α β : Type*} (ψ : α → Fin k → ZMod N)
    (W : Finset α) (φ : β → Fin k → ZMod N)
    (A B : Fin r → Finset β) :
    vinogradovSelectedEnergy ψ W φ A B ≤
      (∑ i, vinogradovSelectedEnergy ψ W φ
        (fun _ : Fin r => A i) (fun _ : Fin r => A i)) +
      ∑ i, vinogradovSelectedEnergy ψ W φ
        (fun _ : Fin r => B i) (fun _ : Fin r => B i) := by
  have hfourier := selectedEnergy_fourier ψ W φ A B
  have hN : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast NeZero.pos N) k
  have hdiagA :
      (∑ a : Fin k → ZMod N,
          ∑ i, ‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
            ‖vinogradovResidueExpSum φ (A i) a‖ ^ (2 * r)) =
        (N : ℝ) ^ k *
          ∑ i, (vinogradovSelectedEnergy ψ W φ
            (fun _ : Fin r => A i) (fun _ : Fin r => A i) : ℝ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (selectedDiagonalEnergy_fourier_real ψ W φ (A i)).symm
  have hdiagB :
      (∑ a : Fin k → ZMod N,
          ∑ i, ‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
            ‖vinogradovResidueExpSum φ (B i) a‖ ^ (2 * r)) =
        (N : ℝ) ^ k *
          ∑ i, (vinogradovSelectedEnergy ψ W φ
            (fun _ : Fin r => B i) (fun _ : Fin r => B i) : ℝ) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (selectedDiagonalEnergy_fourier_real ψ W φ (B i)).symm
  have hbound :
      (N : ℝ) ^ k * (vinogradovSelectedEnergy ψ W φ A B : ℝ) ≤
        (N : ℝ) ^ k *
          ((∑ i, vinogradovSelectedEnergy ψ W φ
              (fun _ : Fin r => A i) (fun _ : Fin r => A i)) +
            ∑ i, vinogradovSelectedEnergy ψ W φ
              (fun _ : Fin r => B i) (fun _ : Fin r => B i) : ℕ) := by
    calc
      (N : ℝ) ^ k * (vinogradovSelectedEnergy ψ W φ A B : ℝ) =
          ‖((N : ℂ) ^ k) * (vinogradovSelectedEnergy ψ W φ A B : ℂ)‖ := by
        simp [norm_pow]
      _ = ‖∑ a : Fin k → ZMod N,
          (vinogradovBlockExpSum ψ W a *
            starRingEnd ℂ (vinogradovBlockExpSum ψ W a)) *
          ((∏ i, vinogradovResidueExpSum φ (A i) a) *
            starRingEnd ℂ (∏ i,
              vinogradovResidueExpSum φ (B i) a))‖ := by
        rw [hfourier]
      _ ≤ ∑ a : Fin k → ZMod N,
          ‖(vinogradovBlockExpSum ψ W a *
            starRingEnd ℂ (vinogradovBlockExpSum ψ W a)) *
          ((∏ i, vinogradovResidueExpSum φ (A i) a) *
            starRingEnd ℂ (∏ i,
              vinogradovResidueExpSum φ (B i) a))‖ := norm_sum_le _ _
      _ = ∑ a : Fin k → ZMod N,
          ‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
            ((∏ i, ‖vinogradovResidueExpSum φ (A i) a‖) *
              ∏ i, ‖vinogradovResidueExpSum φ (B i) a‖) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [norm_prod, pow_two]
      _ ≤ ∑ a : Fin k → ZMod N,
          ((∑ i, ‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
              ‖vinogradovResidueExpSum φ (A i) a‖ ^ (2 * r)) +
            ∑ i, ‖vinogradovBlockExpSum ψ W a‖ ^ 2 *
              ‖vinogradovResidueExpSum φ (B i) a‖ ^ (2 * r)) := by
        apply Finset.sum_le_sum
        intro a ha
        have h := mul_le_mul_of_nonneg_left
          (mixed_norm_prod_le_sum hr φ A B a)
          (sq_nonneg ‖vinogradovBlockExpSum ψ W a‖)
        simpa only [mul_add, Finset.mul_sum] using h
      _ = (N : ℝ) ^ k *
          ((∑ i, vinogradovSelectedEnergy ψ W φ
              (fun _ : Fin r => A i) (fun _ : Fin r => A i)) +
            ∑ i, vinogradovSelectedEnergy ψ W φ
              (fun _ : Fin r => B i) (fun _ : Fin r => B i) : ℕ) := by
        rw [Finset.sum_add_distrib, hdiagA, hdiagB]
        push_cast
        ring
  exact_mod_cast (le_of_mul_le_mul_left hbound hN)

/-! ## Inhomogeneous fibers -/

private noncomputable def vinogradovShiftedEnergy {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N) (C : Finset α)
    (d : Fin k → ZMod N) : ℕ := by
  classical
  exact ((Fintype.piFinset (fun _ : Fin r => C) ×ˢ
      Fintype.piFinset (fun _ : Fin r => C)).filter fun xy =>
        (∑ i, φ (xy.1 i)) = d + ∑ i, φ (xy.2 i)).card

private theorem shiftedEnergy_fourier {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N) (C : Finset α)
    (d : Fin k → ZMod N) :
    ((N : ℂ) ^ k) * (vinogradovShiftedEnergy (r := r) φ C d : ℂ) =
      ∑ a : Fin k → ZMod N,
        starRingEnd ℂ (vinogradovVectorChar N k a d) *
          (vinogradovResidueExpSum φ C a ^ r *
            starRingEnd ℂ (vinogradovResidueExpSum φ C a ^ r)) := by
  classical
  symm
  calc
    (∑ a : Fin k → ZMod N,
        starRingEnd ℂ (vinogradovVectorChar N k a d) *
          (vinogradovResidueExpSum φ C a ^ r *
            starRingEnd ℂ (vinogradovResidueExpSum φ C a ^ r))) =
      ∑ a : Fin k → ZMod N,
        ∑ xy ∈ Fintype.piFinset (fun _ : Fin r => C) ×ˢ
            Fintype.piFinset (fun _ : Fin r => C),
          vinogradovVectorChar N k a
            ((∑ i, φ (xy.1 i)) - (d + ∑ i, φ (xy.2 i))) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hpair := sum_pair_char φ
          (fun _ : Fin r => C) (fun _ : Fin r => C) a
        simp only [Finset.prod_const, Finset.card_univ,
          Fintype.card_fin] at hpair
        rw [← hpair]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro xy hxy
        rw [← vinogradovVectorChar_neg,
          ← vinogradovVectorChar_add]
        congr 1
        abel
    _ = ∑ xy ∈ Fintype.piFinset (fun _ : Fin r => C) ×ˢ
            Fintype.piFinset (fun _ : Fin r => C),
          ∑ a : Fin k → ZMod N,
            vinogradovVectorChar N k a
              ((∑ i, φ (xy.1 i)) - (d + ∑ i, φ (xy.2 i))) := by
        rw [Finset.sum_comm]
    _ = ((N : ℂ) ^ k) *
        (vinogradovShiftedEnergy (r := r) φ C d : ℂ) := by
        simp_rw [sum_vinogradovVectorChar]
        simp only [sub_eq_zero]
        rw [vinogradovShiftedEnergy, ← Finset.sum_filter]
        simp [mul_comm]

/-- No inhomogeneous moment fiber is larger than the homogeneous energy. -/
private theorem shiftedEnergy_le_diagonal {N k r : ℕ} [NeZero N]
    {α : Type*} (φ : α → Fin k → ZMod N) (C : Finset α)
    (d : Fin k → ZMod N) :
    vinogradovShiftedEnergy (r := r) φ C d ≤
      vinogradovMixedEnergy φ (fun _ : Fin r => C) (fun _ : Fin r => C) := by
  have hshift := shiftedEnergy_fourier (r := r) φ C d
  have hdiag := diagonalEnergy_fourier_real (r := r) φ C
  have hN : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast NeZero.pos N) k
  have hbound :
      (N : ℝ) ^ k * (vinogradovShiftedEnergy (r := r) φ C d : ℝ) ≤
        (N : ℝ) ^ k *
          (vinogradovMixedEnergy φ (fun _ : Fin r => C)
            (fun _ : Fin r => C) : ℝ) := by
    calc
      (N : ℝ) ^ k * (vinogradovShiftedEnergy (r := r) φ C d : ℝ) =
          ‖((N : ℂ) ^ k) *
            (vinogradovShiftedEnergy (r := r) φ C d : ℂ)‖ := by
        simp [norm_pow]
      _ = ‖∑ a : Fin k → ZMod N,
          starRingEnd ℂ (vinogradovVectorChar N k a d) *
            (vinogradovResidueExpSum φ C a ^ r *
              starRingEnd ℂ (vinogradovResidueExpSum φ C a ^ r))‖ := by
        rw [hshift]
      _ ≤ ∑ a : Fin k → ZMod N,
          ‖starRingEnd ℂ (vinogradovVectorChar N k a d) *
            (vinogradovResidueExpSum φ C a ^ r *
              starRingEnd ℂ (vinogradovResidueExpSum φ C a ^ r))‖ :=
        norm_sum_le _ _
      _ = ∑ a : Fin k → ZMod N,
          ‖vinogradovResidueExpSum φ C a‖ ^ (2 * r) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [norm_mul, Complex.norm_conj, norm_mul,
          Complex.norm_conj, norm_pow]
        have hchar : ‖vinogradovVectorChar N k a d‖ = 1 := by
          simp [vinogradovVectorChar, norm_prod]
        rw [hchar, one_mul, ← pow_add]
        congr 1
        omega
      _ = (N : ℝ) ^ k *
          (vinogradovMixedEnergy φ (fun _ : Fin r => C)
            (fun _ : Fin r => C) : ℝ) := hdiag.symm
  exact_mod_cast (le_of_mul_le_mul_left hbound hN)

/-! ## The nonsingular block after translation -/

private def zmodIccRep (N : ℕ) (z : ZMod N) : ℕ :=
  if z = 0 then N else z.val

private theorem zmodIccRep_mem_Icc {N : ℕ} (hN : 0 < N) (z : ZMod N) :
    zmodIccRep N z ∈ Finset.Icc 1 N := by
  letI : NeZero N := ⟨hN.ne'⟩
  by_cases hz : z = 0
  · rw [zmodIccRep, if_pos hz, Finset.mem_Icc]
    exact ⟨hN, le_rfl⟩
  · have hzval : 0 < z.val := Nat.pos_of_ne_zero fun h => hz (by
      apply ZMod.val_injective
      simp [h])
    rw [zmodIccRep, if_neg hz, Finset.mem_Icc]
    exact ⟨hzval, Nat.le_of_lt z.val_lt⟩

private theorem natCast_zmodIccRep {N : ℕ} (hN : 0 < N) (z : ZMod N) :
    (zmodIccRep N z : ZMod N) = z := by
  letI : NeZero N := ⟨hN.ne'⟩
  by_cases hz : z = 0
  · simp [zmodIccRep, hz]
  · rw [zmodIccRep, if_neg hz]
    exact ZMod.natCast_zmod_val z

private def vinogradovTranslatedRep (p k a : ℕ) (x : Fin k → ℕ) :
    Fin k → ℕ := fun i =>
  zmodIccRep (p ^ k) ((x i : ZMod (p ^ k)) - (a : ZMod (p ^ k)))

private theorem translatedRep_cast {p k a : ℕ} (hp : 0 < p)
    (x : Fin k → ℕ) (i : Fin k) :
    (vinogradovTranslatedRep p k a x i : ZMod (p ^ k)) =
      (x i : ZMod (p ^ k)) - (a : ZMod (p ^ k)) := by
  exact natCast_zmodIccRep (pow_pos hp k) _

private theorem translatedRep_mem_tuples {p k a : ℕ} (hp : 0 < p)
    (x : Fin k → ℕ) :
    vinogradovTranslatedRep p k a x ∈ vinogradovTuples k (p ^ k) := by
  rw [mem_vinogradovTuples]
  exact fun i => Finset.mem_Icc.mp (zmodIccRep_mem_Icc (pow_pos hp k) _)

private theorem translatedRep_wellConditioned {p k a : ℕ}
    (hp : p.Prime) (hk : 0 < k) (x : Fin k → ℕ)
    (hx : VinogradovWellConditioned p x) :
    VinogradovWellConditioned p (vinogradovTranslatedRep p k a x) := by
  intro i j hij heq
  let castDown := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
  have hrep :
      ((vinogradovTranslatedRep p k a x i : ℕ) : ZMod p) =
        (x i : ZMod p) - (a : ZMod p) := by
    have h := congrArg castDown (translatedRep_cast (a := a) hp.pos x i)
    simpa only [map_sub, map_natCast] using h
  have hrep' :
      ((vinogradovTranslatedRep p k a x j : ℕ) : ZMod p) =
        (x j : ZMod p) - (a : ZMod p) := by
    have h := congrArg castDown (translatedRep_cast (a := a) hp.pos x j)
    simpa only [map_sub, map_natCast] using h
  have hz : (x i : ZMod p) = (x j : ZMod p) := by
    apply (sub_left_injective (b := (a : ZMod p)))
    change (x i : ZMod p) - (a : ZMod p) =
      (x j : ZMod p) - (a : ZMod p)
    rw [← hrep, ← hrep']
    exact (ZMod.natCast_eq_natCast_iff _ _ p).2 (by
      simpa [Nat.ModEq] using heq)
  exact hx i j hij (by
    have := (ZMod.natCast_eq_natCast_iff (x i) (x j) p).mp hz
    simpa [Nat.ModEq] using this)

private theorem translatedRep_injective_on_Icc {p k a P : ℕ}
    (hp : 0 < p) (hP : P < p ^ k) {x y : Fin k → ℕ}
    (hx : x ∈ vinogradovTuples k P) (hy : y ∈ vinogradovTuples k P)
    (hrep : vinogradovTranslatedRep p k a x =
      vinogradovTranslatedRep p k a y) : x = y := by
  funext i
  have hcast : (x i : ZMod (p ^ k)) = (y i : ZMod (p ^ k)) := by
    have h := congrArg (fun z : ℕ => (z : ZMod (p ^ k)))
      (congrFun hrep i)
    change (vinogradovTranslatedRep p k a x i : ZMod (p ^ k)) =
      (vinogradovTranslatedRep p k a y i : ZMod (p ^ k)) at h
    rw [translatedRep_cast (a := a) hp x i,
      translatedRep_cast (a := a) hp y i] at h
    exact sub_left_injective h
  apply nat_eq_of_Icc_of_zmod_eq
    (Finset.mem_Icc.mpr ⟨(mem_vinogradovTuples.mp hx i).1,
      (mem_vinogradovTuples.mp hx i).2.trans hP.le⟩)
    (Finset.mem_Icc.mpr ⟨(mem_vinogradovTuples.mp hy i).1,
      (mem_vinogradovTuples.mp hy i).2.trans hP.le⟩) hcast

private def vinogradovRingPowerSum {R : Type*} [CommRing R]
    {n : ℕ} (x : Fin n → R) (j : ℕ) : R :=
  ∑ i, x i ^ j

private theorem cast_vinogradovPowerSum {R : Type*} [CommRing R]
    {n j : ℕ} (x : Fin n → ℕ) :
    (vinogradovPowerSum x j : R) =
      vinogradovRingPowerSum (fun i => (x i : R)) j := by
  rw [vinogradovPowerSum, vinogradovRingPowerSum,
    show (↑(∑ i, x i ^ j) : R) =
      ∑ i, (↑(x i ^ j) : R) by
        exact map_sum (Nat.castAddMonoidHom R) (fun i => x i ^ j) Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  exact Nat.cast_pow (x i) j

private theorem vinogradovRingPowerSum_add {R : Type*} [CommRing R]
    {n : ℕ} (x : Fin n → R) (c : R) (j : ℕ) :
    vinogradovRingPowerSum (fun i => x i + c) j =
      ∑ l ∈ Finset.range (j + 1),
        ((j.choose l : ℕ) : R) * c ^ (j - l) *
          vinogradovRingPowerSum x l := by
  classical
  rw [vinogradovRingPowerSum]
  simp_rw [add_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [vinogradovRingPowerSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem total_ringPowerSum_sub_eq {R : Type*} [CommRing R]
    {k r m : ℕ} (u v : Fin k → R) (x y : Fin r → R) (c : R)
    (h : ∀ l ≤ m, vinogradovRingPowerSum u l +
        vinogradovRingPowerSum x l =
      vinogradovRingPowerSum v l + vinogradovRingPowerSum y l) :
    vinogradovRingPowerSum (fun i => u i - c) m +
        vinogradovRingPowerSum (fun i => x i - c) m =
      vinogradovRingPowerSum (fun i => v i - c) m +
        vinogradovRingPowerSum (fun i => y i - c) m := by
  simp only [sub_eq_add_neg]
  rw [vinogradovRingPowerSum_add, vinogradovRingPowerSum_add,
    vinogradovRingPowerSum_add, vinogradovRingPowerSum_add,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hl
  have hlEq := h l (by omega)
  calc
    ((m.choose l : ℕ) : R) * (-c) ^ (m - l) *
          vinogradovRingPowerSum u l +
        ((m.choose l : ℕ) : R) * (-c) ^ (m - l) *
          vinogradovRingPowerSum x l =
      (((m.choose l : ℕ) : R) * (-c) ^ (m - l)) *
        (vinogradovRingPowerSum u l + vinogradovRingPowerSum x l) := by ring
    _ = (((m.choose l : ℕ) : R) * (-c) ^ (m - l)) *
        (vinogradovRingPowerSum v l + vinogradovRingPowerSum y l) := by rw [hlEq]
    _ = ((m.choose l : ℕ) : R) * (-c) ^ (m - l) *
          vinogradovRingPowerSum v l +
        ((m.choose l : ℕ) : R) * (-c) ^ (m - l) *
          vinogradovRingPowerSum y l := by ring

private theorem pow_sub_cast_eq_zero_of_mod_eq {p a n m : ℕ}
    (hn : n % p = a) :
    ((n : ZMod (p ^ m)) - (a : ZMod (p ^ m))) ^ m = 0 := by
  have hnrepr : n = p * (n / p) + a := by
    calc
      n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
      _ = p * (n / p) + a := by rw [hn]
  rw [hnrepr]
  push_cast
  rw [add_sub_cancel_right, mul_pow]
  have hpzero : (p : ZMod (p ^ m)) ^ m = 0 := by
    rw [← Nat.cast_pow, CharP.cast_eq_zero]
  rw [hpzero, zero_mul]

private theorem translatedRep_cast_powSum {p k a m : ℕ}
    (hp : 0 < p) (hm : m ≤ k) (x : Fin k → ℕ) :
    vinogradovRingPowerSum
        (fun i => (vinogradovTranslatedRep p k a x i : ZMod (p ^ m))) m =
      vinogradovRingPowerSum
        (fun i => (x i : ZMod (p ^ m)) - (a : ZMod (p ^ m))) m := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hcast := congrArg
    (ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m)))
    (translatedRep_cast (a := a) hp x i)
  simpa only [map_sub, map_natCast] using hcast

/-- Translating the whole Vinogradov system by the common free residue makes
the free variables divisible by `p`; their degree-`m` terms then vanish
modulo `p^m`, leaving Linnik's congruences on the distinguished block. -/
private theorem translatedBlock_congruent {p k r a : ℕ}
    (hp : p.Prime) (u v : Fin k → ℕ) (x y : Fin r → ℕ)
    (hxmod : ∀ i, x i % p = a) (hymod : ∀ i, y i % p = a)
    (hsol : ∀ j ≤ k,
      vinogradovPowerSum u j + vinogradovPowerSum x j =
        vinogradovPowerSum v j + vinogradovPowerSum y j) :
    VinogradovCongruentMoments p k
      (vinogradovTranslatedRep p k a u)
      (vinogradovTranslatedRep p k a v) := by
  intro j
  let m := (j : ℕ) + 1
  have hm : m ≤ k := Nat.succ_le_of_lt j.isLt
  let R := ZMod (p ^ m)
  have htotal : ∀ l ≤ m,
      vinogradovRingPowerSum (fun i => (u i : R)) l +
          vinogradovRingPowerSum (fun i => (x i : R)) l =
        vinogradovRingPowerSum (fun i => (v i : R)) l +
          vinogradovRingPowerSum (fun i => (y i : R)) l := by
    intro l hl
    calc
      vinogradovRingPowerSum (fun i => (u i : R)) l +
          vinogradovRingPowerSum (fun i => (x i : R)) l =
        ((vinogradovPowerSum u l + vinogradovPowerSum x l : ℕ) : R) := by
          rw [Nat.cast_add, cast_vinogradovPowerSum,
            cast_vinogradovPowerSum]
      _ = ((vinogradovPowerSum v l + vinogradovPowerSum y l : ℕ) : R) := by
        rw [hsol l (hl.trans hm)]
      _ = vinogradovRingPowerSum (fun i => (v i : R)) l +
          vinogradovRingPowerSum (fun i => (y i : R)) l := by
          rw [Nat.cast_add, cast_vinogradovPowerSum,
            cast_vinogradovPowerSum]
  have htrans := total_ringPowerSum_sub_eq
    (fun i => (u i : R)) (fun i => (v i : R))
    (fun i => (x i : R)) (fun i => (y i : R)) (a : R) htotal
  have hxzero : vinogradovRingPowerSum
      (fun i => (x i : R) - (a : R)) m = 0 := by
    rw [vinogradovRingPowerSum]
    apply Finset.sum_eq_zero
    intro i hi
    exact pow_sub_cast_eq_zero_of_mod_eq (hxmod i)
  have hyzero : vinogradovRingPowerSum
      (fun i => (y i : R) - (a : R)) m = 0 := by
    rw [vinogradovRingPowerSum]
    apply Finset.sum_eq_zero
    intro i hi
    exact pow_sub_cast_eq_zero_of_mod_eq (hymod i)
  rw [hxzero, hyzero, add_zero, add_zero] at htrans
  have hcast :
      (vinogradovPowerSum (vinogradovTranslatedRep p k a u) m : R) =
        (vinogradovPowerSum (vinogradovTranslatedRep p k a v) m : R) := by
    calc
      (vinogradovPowerSum (vinogradovTranslatedRep p k a u) m : R) =
          vinogradovRingPowerSum
            (fun i => (vinogradovTranslatedRep p k a u i : R)) m := by
        exact cast_vinogradovPowerSum _
      _ = vinogradovRingPowerSum (fun i => (u i : R) - (a : R)) m :=
        translatedRep_cast_powSum hp.pos hm u
      _ = vinogradovRingPowerSum (fun i => (v i : R) - (a : R)) m := htrans
      _ = vinogradovRingPowerSum
          (fun i => (vinogradovTranslatedRep p k a v i : R)) m :=
        (translatedRep_cast_powSum hp.pos hm v).symm
      _ = (vinogradovPowerSum (vinogradovTranslatedRep p k a v) m : R) := by
        exact (cast_vinogradovPowerSum _).symm
  simpa [m] using
    (ZMod.natCast_eq_natCast_iff
      (vinogradovPowerSum (vinogradovTranslatedRep p k a u) m)
      (vinogradovPowerSum (vinogradovTranslatedRep p k a v) m)
      (p ^ m)).mp hcast

private def VinogradovDifferenceAgreeUpTo {r : ℕ} (k : ℕ)
    (x y x' y' : Fin r → ℕ) : Prop :=
  ∀ j ≤ k, vinogradovPowerSum x j + vinogradovPowerSum y' j =
    vinogradovPowerSum y j + vinogradovPowerSum x' j

/-- Two solutions with the same distinguished block have the same
inhomogeneous quotient moment vector. -/
private theorem differenceAgree_div_of_same_mod {r k p a : ℕ}
    (hp : 0 < p) (x y x' y' : Fin r → ℕ)
    (hx : ∀ i, x i % p = a) (hy : ∀ i, y i % p = a)
    (hx' : ∀ i, x' i % p = a) (hy' : ∀ i, y' i % p = a)
    (h : VinogradovDifferenceAgreeUpTo k x y x' y') :
    VinogradovDifferenceAgreeUpTo k
      (fun i => x i / p) (fun i => y i / p)
      (fun i => x' i / p) (fun i => y' i / p) := by
  have repr (z : Fin r → ℕ) (hz : ∀ i, z i % p = a) :
      z = fun i => p * (z i / p) + a := by
    funext i
    calc
      z i = p * (z i / p) + z i % p := (Nat.div_add_mod (z i) p).symm
      _ = p * (z i / p) + a := by rw [hz i]
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hs := h j hj
      rw [repr x hx, repr y hy, repr x' hx', repr y' hy',
        vinogradovPowerSum_add, vinogradovPowerSum_add,
        vinogradovPowerSum_add, vinogradovPowerSum_add] at hs
      simp_rw [vinogradovPowerSum_mul] at hs
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        Finset.sum_range_succ, Finset.sum_range_succ] at hs
      have hlo :
          (∑ l ∈ Finset.range j,
            ((j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => x i / p) l) +
              (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => y' i / p) l))) =
          ∑ l ∈ Finset.range j,
            ((j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => y i / p) l) +
              (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => x' i / p) l)) := by
        apply Finset.sum_congr rfl
        intro l hl
        have hil := ih l (Finset.mem_range.mp hl)
          (le_trans (Nat.le_of_lt (Finset.mem_range.mp hl)) hj)
        calc
          (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => x i / p) l) +
              (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => y' i / p) l) =
            (j.choose l * a ^ (j - l) * p ^ l) *
              (vinogradovPowerSum (fun i => x i / p) l +
                vinogradovPowerSum (fun i => y' i / p) l) := by ring
          _ = (j.choose l * a ^ (j - l) * p ^ l) *
              (vinogradovPowerSum (fun i => y i / p) l +
                vinogradovPowerSum (fun i => x' i / p) l) := by rw [hil]
          _ = (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => y i / p) l) +
              (j.choose l * a ^ (j - l)) *
                (p ^ l * vinogradovPowerSum (fun i => x' i / p) l) := by ring
      rw [hlo] at hs
      have htop := Nat.add_left_cancel hs
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, mul_one,
        one_mul] at htop
      have hfactor : p ^ j *
          (vinogradovPowerSum (fun i => x i / p) j +
            vinogradovPowerSum (fun i => y' i / p) j) =
        p ^ j *
          (vinogradovPowerSum (fun i => y i / p) j +
            vinogradovPowerSum (fun i => x' i / p) j) := by
        simpa [mul_add] using htop
      exact Nat.mul_left_cancel (pow_pos hp j) hfactor

private def vinogradovBlockCurve (N k : ℕ) (u : Fin k → ℕ) :
    Fin k → ZMod N :=
  ∑ i, vinogradovModCurve N k (u i)

private theorem vinogradovPowerSum_le_scale {n k P j : ℕ}
    (hj : j ≤ k) (x : Fin n → ℕ) (hx : ∀ i, x i ≤ P) :
    vinogradovPowerSum x j ≤ n * (P + 1) ^ k := by
  calc
    vinogradovPowerSum x j ≤ ∑ _i : Fin n, (P + 1) ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Nat.pow_le_pow_left ((hx i).trans (Nat.le_succ P)) j).trans
        (Nat.pow_le_pow_right (by omega : 0 < P + 1) hj)
    _ = n * (P + 1) ^ k := by simp

private theorem blockCurve_eq_iff_totalPowerSums_eq {r k P : ℕ}
    (u v : Fin k → ℕ) (x y : Fin r → ℕ)
    (hu : ∀ i, u i ≤ P) (hv : ∀ i, v i ≤ P)
    (hx : ∀ i, x i ≤ P) (hy : ∀ i, y i ≤ P) :
    let N := vinogradovSafeModulus (r + k) k P
    vinogradovBlockCurve N k u + ∑ i, vinogradovModCurve N k (x i) =
        vinogradovBlockCurve N k v + ∑ i, vinogradovModCurve N k (y i) ↔
      ∀ j ≤ k, vinogradovPowerSum u j + vinogradovPowerSum x j =
        vinogradovPowerSum v j + vinogradovPowerSum y j := by
  dsimp only
  let N := vinogradovSafeModulus (r + k) k P
  have hN : 0 < N := vinogradovSafeModulus_pos (r + k) k P
  constructor
  · intro h j hj
    by_cases hj0 : j = 0
    · subst j
      simp [vinogradovPowerSum]
    · let j' : Fin k := ⟨j - 1, by omega⟩
      have hc := congrFun h j'
      have hcast :
          ((vinogradovPowerSum u j + vinogradovPowerSum x j : ℕ) : ZMod N) =
            ((vinogradovPowerSum v j + vinogradovPowerSum y j : ℕ) : ZMod N) := by
        simpa [vinogradovBlockCurve, vinogradovModCurve,
          vinogradovPowerSum, j', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
          using hc
      have hmod := (ZMod.natCast_eq_natCast_iff
        (vinogradovPowerSum u j + vinogradovPowerSum x j)
        (vinogradovPowerSum v j + vinogradovPowerSum y j) N).mp hcast
      apply Nat.ModEq.eq_of_lt_of_lt hmod
      · calc
          vinogradovPowerSum u j + vinogradovPowerSum x j ≤
              k * (P + 1) ^ k + r * (P + 1) ^ k :=
            Nat.add_le_add (vinogradovPowerSum_le_scale hj u hu)
              (vinogradovPowerSum_le_scale hj x hx)
          _ = (r + k) * (P + 1) ^ k := by ring
          _ < N := by simp [N, vinogradovSafeModulus]
      · calc
          vinogradovPowerSum v j + vinogradovPowerSum y j ≤
              k * (P + 1) ^ k + r * (P + 1) ^ k :=
            Nat.add_le_add (vinogradovPowerSum_le_scale hj v hv)
              (vinogradovPowerSum_le_scale hj y hy)
          _ = (r + k) * (P + 1) ^ k := by ring
          _ < N := by simp [N, vinogradovSafeModulus]
  · intro h
    funext j
    have hj := h ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
    simpa [vinogradovBlockCurve, vinogradovModCurve, vinogradovPowerSum]
      using congrArg (fun n : ℕ => (n : ZMod N)) hj

private theorem diagonalZeroBasedEnergy_le_vinogradovJ (r k Q : ℕ) :
    let N := vinogradovSafeModulus r k Q
    letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k Q)⟩
    vinogradovMixedEnergy (vinogradovModCurve N k)
        (fun _ : Fin r => Finset.range (Q + 1))
        (fun _ : Fin r => Finset.range (Q + 1)) ≤
      vinogradovJ r k (Q + 1) := by
  classical
  dsimp only
  let N := vinogradovSafeModulus r k Q
  letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k Q)⟩
  let C := Finset.range (Q + 1)
  let S := ((Fintype.piFinset (fun _ : Fin r => C)) ×ˢ
      Fintype.piFinset (fun _ : Fin r => C)).filter fun xy =>
        (∑ i, vinogradovModCurve N k (xy.1 i)) =
          ∑ i, vinogradovModCurve N k (xy.2 i)
  let T := ((vinogradovTuples r (Q + 1)) ×ˢ
      vinogradovTuples r (Q + 1)).filter fun xy =>
        IsVinogradovSolution k xy.1 xy.2
  let addOne : ((Fin r → ℕ) × (Fin r → ℕ)) →
      ((Fin r → ℕ) × (Fin r → ℕ)) := fun xy =>
    (fun i => xy.1 i + 1, fun i => xy.2 i + 1)
  change S.card ≤ T.card
  apply Finset.card_le_card_of_injOn addOne
  · intro xy hxy
    rw [Finset.mem_coe] at hxy ⊢
    dsimp [S] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    have hxC := Fintype.mem_piFinset.mp hxy.1.1
    have hyC := Fintype.mem_piFinset.mp hxy.1.2
    have hxle : ∀ i, xy.1 i ≤ Q := by
      intro i
      have hi : xy.1 i ∈ Finset.range (Q + 1) := by simpa [C] using hxC i
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hyle : ∀ i, xy.2 i ≤ Q := by
      intro i
      have hi : xy.2 i ∈ Finset.range (Q + 1) := by simpa [C] using hyC i
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hmom : vinogradovMomentVector k xy.1 =
        vinogradovMomentVector k xy.2 :=
      (modCurve_sum_eq_iff_powerSums_eq xy.1 xy.2
        hxle hyle).mp hxy.2
    dsimp [T, addOne]
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨mem_vinogradovTuples.mpr fun i => ⟨Nat.succ_pos _, ?_⟩,
      mem_vinogradovTuples.mpr fun i => ⟨Nat.succ_pos _, ?_⟩⟩, ?_⟩
    · exact Nat.add_le_add_right (hxle i) 1
    · exact Nat.add_le_add_right (hyle i) 1
    · exact (isVinogradovSolution_add_iff xy.1 xy.2 1).mpr
        (isVinogradovSolution_iff_momentVector_eq.mpr hmom)
  · intro xy hxy zw hzw heq
    apply Prod.ext <;> funext i
    · have := congrFun (congrArg Prod.fst heq) i
      dsimp [addOne] at this
      omega
    · have := congrFun (congrArg Prod.snd heq) i
      dsimp [addOne] at this
      omega

/-- A fixed inhomogeneous quotient moment vector costs no more than the
homogeneous Vinogradov energy. -/
private theorem shiftedZeroBasedEnergy_le_vinogradovJ
    (r k Q : ℕ) (d : Fin k → ZMod (vinogradovSafeModulus r k Q)) :
    let N := vinogradovSafeModulus r k Q
    letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k Q)⟩
    vinogradovShiftedEnergy (r := r) (vinogradovModCurve N k)
        (Finset.range (Q + 1)) d ≤ vinogradovJ r k (Q + 1) := by
  dsimp only
  let N := vinogradovSafeModulus r k Q
  letI : NeZero N := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k Q)⟩
  exact (shiftedEnergy_le_diagonal (r := r)
    (vinogradovModCurve N k) (Finset.range (Q + 1)) d).trans
      (diagonalZeroBasedEnergy_le_vinogradovJ r k Q)

/-- The diagonal term after Hölder: Linnik prices the distinguished block,
and Cauchy--Schwarz prices the remaining inhomogeneous quotient fiber. -/
private theorem selectedDiagonalEnergy_le {r k P p a : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpk : k < p) (hP : P < p ^ k) :
    let N := vinogradovSafeModulus (r + k) k P
    letI : NeZero N :=
      ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos (r + k) k P)⟩
    vinogradovSelectedEnergy (vinogradovBlockCurve N k)
        ((vinogradovTuples k P).filter (VinogradovWellConditioned p))
        (vinogradovModCurve N k)
        (fun _ : Fin r => vinogradovResidueClass P p a)
        (fun _ : Fin r => vinogradovResidueClass P p a) ≤
      P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
        vinogradovJ r k (P / p + 1) := by
  classical
  dsimp only
  let N := vinogradovSafeModulus (r + k) k P
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos (r + k) k P)⟩
  let W := (vinogradovTuples k P).filter (VinogradovWellConditioned p)
  let C := vinogradovResidueClass P p a
  let S := (((W ×ˢ W) ×ˢ
      (Fintype.piFinset (fun _ : Fin r => C) ×ˢ
        Fintype.piFinset (fun _ : Fin r => C))).filter fun z =>
      vinogradovBlockCurve N k z.1.1 +
          ∑ i, vinogradovModCurve N k (z.2.1 i) =
        vinogradovBlockCurve N k z.1.2 +
          ∑ i, vinogradovModCurve N k (z.2.2 i))
  let toV : ((Fin k → ℕ) × (Fin k → ℕ)) ×
      ((Fin r → ℕ) × (Fin r → ℕ)) → (Fin k → ℕ) := fun z => z.1.2
  change S.card ≤ _
  have hmapsV : ∀ z ∈ S, toV z ∈ vinogradovTuples k P := by
    intro z hz
    dsimp [S] at hz
    have hout := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    exact (Finset.mem_filter.mp (Finset.mem_product.mp hout.1).2).1
  have hfiberV : ∀ v ∈ vinogradovTuples k P,
      (S.filter fun z => toV z = v).card ≤
        (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1) := by
    intro v hv
    let Sv := S.filter fun z => toV z = v
    let toU : ((Fin k → ℕ) × (Fin k → ℕ)) ×
        ((Fin r → ℕ) × (Fin r → ℕ)) → (Fin k → ℕ) := fun z =>
      vinogradovTranslatedRep p k a z.1.1
    have hmapsU : ∀ z ∈ Sv,
        toU z ∈ vinogradovLinnikFiber p k
          (vinogradovTranslatedRep p k a v) := by
      intro z hz
      dsimp [Sv] at hz
      rw [Finset.mem_filter] at hz
      have hzS := hz.1
      dsimp [S] at hzS
      rw [Finset.mem_filter] at hzS
      have hout := Finset.mem_product.mp hzS.1
      have huv := Finset.mem_product.mp hout.1
      have hxy := Finset.mem_product.mp hout.2
      rcases huv with ⟨hzuW, hzvW⟩
      rcases hxy with ⟨hzxC, hzyC⟩
      have hzu := (Finset.mem_filter.mp hzuW).1
      have hzv := (Finset.mem_filter.mp hzvW).1
      have hzx := Fintype.mem_piFinset.mp hzxC
      have hzy := Fintype.mem_piFinset.mp hzyC
      have hzxdata : ∀ i, 1 ≤ z.2.1 i ∧ z.2.1 i ≤ P ∧ z.2.1 i % p = a := by
        intro i
        exact mem_vinogradovResidueClass.mp (by simpa [C] using hzx i)
      have hzydata : ∀ i, 1 ≤ z.2.2 i ∧ z.2.2 i ≤ P ∧ z.2.2 i % p = a := by
        intro i
        exact mem_vinogradovResidueClass.mp (by simpa [C] using hzy i)
      have htotal := (blockCurve_eq_iff_totalPowerSums_eq z.1.1 z.1.2
        z.2.1 z.2.2
        (fun i => (mem_vinogradovTuples.mp hzu i).2)
        (fun i => (mem_vinogradovTuples.mp hzv i).2)
        (fun i => (hzxdata i).2.1) (fun i => (hzydata i).2.1)).mp hzS.2
      dsimp [vinogradovLinnikFiber, toU]
      rw [Finset.mem_filter]
      refine ⟨translatedRep_mem_tuples hp.pos z.1.1,
        translatedRep_wellConditioned hp hk z.1.1
          (Finset.mem_filter.mp hzuW).2, ?_⟩
      rw [← hz.2]
      exact translatedBlock_congruent hp z.1.1 z.1.2 z.2.1 z.2.2
        (fun i => (hzxdata i).2.2) (fun i => (hzydata i).2.2) htotal
    have hfiberU : ∀ urep ∈ vinogradovLinnikFiber p k
          (vinogradovTranslatedRep p k a v),
        (Sv.filter fun z => toU z = urep).card ≤
          vinogradovJ r k (P / p + 1) := by
      intro urep hurep
      let Su := Sv.filter fun z => toU z = urep
      rcases Su.eq_empty_or_nonempty with hSu | ⟨z₀, hz₀⟩
      · simp [Su, hSu]
      let Q := P / p
      let Nq := vinogradovSafeModulus r k Q
      letI : NeZero Nq := ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos r k Q)⟩
      let quotPair : ((Fin k → ℕ) × (Fin k → ℕ)) ×
          ((Fin r → ℕ) × (Fin r → ℕ)) →
          ((Fin r → ℕ) × (Fin r → ℕ)) := fun z =>
        (fun i => z.2.1 i / p, fun i => z.2.2 i / p)
      let d : Fin k → ZMod Nq :=
        (∑ i, vinogradovModCurve Nq k ((quotPair z₀).1 i)) -
          ∑ i, vinogradovModCurve Nq k ((quotPair z₀).2 i)
      have hmapsQ : Set.MapsTo quotPair (↑Su)
          (↑(((Fintype.piFinset (fun _ : Fin r => Finset.range (Q + 1))) ×ˢ
            Fintype.piFinset (fun _ : Fin r => Finset.range (Q + 1))).filter
              fun xy => (∑ i, vinogradovModCurve Nq k (xy.1 i)) =
                d + ∑ i, vinogradovModCurve Nq k (xy.2 i))) := by
        intro z hz
        rw [Finset.mem_coe] at hz ⊢
        dsimp [Su] at hz
        rw [Finset.mem_filter] at hz
        have hzSv := hz.1
        dsimp [Sv] at hzSv
        rw [Finset.mem_filter] at hzSv
        have hzS := hzSv.1
        have hz₀' := Finset.mem_coe.mp hz₀
        dsimp [Su] at hz₀'
        rw [Finset.mem_filter] at hz₀'
        have hz₀Sv := hz₀'.1
        dsimp [Sv] at hz₀Sv
        rw [Finset.mem_filter] at hz₀Sv
        have hz₀S := hz₀Sv.1
        dsimp [S] at hzS hz₀S
        rw [Finset.mem_filter] at hzS hz₀S
        have hzout := Finset.mem_product.mp hzS.1
        have hzuv := Finset.mem_product.mp hzout.1
        have hzxy := Finset.mem_product.mp hzout.2
        have hz₀out := Finset.mem_product.mp hz₀S.1
        have hz₀uv := Finset.mem_product.mp hz₀out.1
        have hz₀xy := Finset.mem_product.mp hz₀out.2
        have hzx := Fintype.mem_piFinset.mp hzxy.1
        have hzy := Fintype.mem_piFinset.mp hzxy.2
        have hzx₀ := Fintype.mem_piFinset.mp hz₀xy.1
        have hzy₀ := Fintype.mem_piFinset.mp hz₀xy.2
        have data (w : Fin r → ℕ) (hw : ∀ i, w i ∈ C) :
            ∀ i, 1 ≤ w i ∧ w i ≤ P ∧ w i % p = a := by
          intro i
          exact mem_vinogradovResidueClass.mp (by simpa [C] using hw i)
        have dx := data z.2.1 hzx
        have dy := data z.2.2 hzy
        have dx₀ := data z₀.2.1 hzx₀
        have dy₀ := data z₀.2.2 hzy₀
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by
            dsimp [Q, quotPair]
            have := Nat.div_le_div_right (c := p) (dx i).2.1
            omega),
          Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by
            dsimp [Q, quotPair]
            have := Nat.div_le_div_right (c := p) (dy i).2.1
            omega)⟩, ?_⟩
        have hzuW := hzuv.1
        have hzvW := hzuv.2
        have hz₀uW := hz₀uv.1
        have hz₀vW := hz₀uv.2
        have huEq : z.1.1 = z₀.1.1 := by
          apply translatedRep_injective_on_Icc hp.pos hP
            (Finset.mem_filter.mp hzuW).1 (Finset.mem_filter.mp hz₀uW).1
          exact hz.2.trans hz₀'.2.symm
        have hvEq : z.1.2 = z₀.1.2 := hzSv.2.trans hz₀Sv.2.symm
        have htotal := (blockCurve_eq_iff_totalPowerSums_eq z.1.1 z.1.2
          z.2.1 z.2.2
          (fun i => (mem_vinogradovTuples.mp (Finset.mem_filter.mp hzuW).1 i).2)
          (fun i => (mem_vinogradovTuples.mp (Finset.mem_filter.mp hzvW).1 i).2)
          (fun i => (dx i).2.1) (fun i => (dy i).2.1)).mp hzS.2
        have htotal₀ := (blockCurve_eq_iff_totalPowerSums_eq z₀.1.1 z₀.1.2
          z₀.2.1 z₀.2.2
          (fun i => (mem_vinogradovTuples.mp (Finset.mem_filter.mp hz₀uW).1 i).2)
          (fun i => (mem_vinogradovTuples.mp (Finset.mem_filter.mp hz₀vW).1 i).2)
          (fun i => (dx₀ i).2.1) (fun i => (dy₀ i).2.1)).mp hz₀S.2
        have hdiff : VinogradovDifferenceAgreeUpTo k
            z.2.1 z.2.2 z₀.2.1 z₀.2.2 := by
          intro j hj
          have h1 := htotal j hj
          have h0 := htotal₀ j hj
          rw [huEq, hvEq] at h1
          omega
        have hqdiff := differenceAgree_div_of_same_mod hp.pos
          z.2.1 z.2.2 z₀.2.1 z₀.2.2
          (fun i => (dx i).2.2) (fun i => (dy i).2.2)
          (fun i => (dx₀ i).2.2) (fun i => (dy₀ i).2.2) hdiff
        funext j
        have heq := hqdiff ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
        change _ = d j + _
        dsimp [d, quotPair]
        simp only [Finset.sum_apply]
        apply eq_add_of_sub_eq
        exact sub_eq_sub_iff_add_eq_add.mpr (by
          simpa [vinogradovModCurve, vinogradovPowerSum, add_comm,
            add_left_comm] using
            congrArg (fun n : ℕ => (n : ZMod Nq)) heq)
      have hinjQ : Set.InjOn quotPair (↑Su) := by
        intro z hz w hw heq
        have hz' := Finset.mem_coe.mp hz
        have hw' := Finset.mem_coe.mp hw
        dsimp [Su] at hz' hw'
        rw [Finset.mem_filter] at hz' hw'
        have hzSv := hz'.1
        have hwSv := hw'.1
        dsimp [Sv] at hzSv hwSv
        rw [Finset.mem_filter] at hzSv hwSv
        have hzS := hzSv.1
        have hwS := hwSv.1
        dsimp [S] at hzS hwS
        rw [Finset.mem_filter] at hzS hwS
        have hzout := Finset.mem_product.mp hzS.1
        have hwout := Finset.mem_product.mp hwS.1
        have hzuv := Finset.mem_product.mp hzout.1
        have hwuv := Finset.mem_product.mp hwout.1
        have hzxy := Finset.mem_product.mp hzout.2
        have hwxy := Finset.mem_product.mp hwout.2
        have hzrep : vinogradovTranslatedRep p k a z.1.1 = urep := by
          simpa [toU] using hz'.2
        have hwrep : vinogradovTranslatedRep p k a w.1.1 = urep := by
          simpa [toU] using hw'.2
        apply Prod.ext
        · apply Prod.ext
          · exact translatedRep_injective_on_Icc (a := a) hp.pos hP
              (Finset.mem_filter.mp hzuv.1).1
              (Finset.mem_filter.mp hwuv.1).1 (hzrep.trans hwrep.symm)
          · exact hzSv.2.trans hwSv.2.symm
        · apply Prod.ext <;> funext i
          · exact eq_of_div_eq_of_mod_eq
              (mem_vinogradovResidueClass.mp (by
                simpa [C] using (Fintype.mem_piFinset.mp hzxy.1) i)).2.2
              (mem_vinogradovResidueClass.mp (by
                simpa [C] using (Fintype.mem_piFinset.mp hwxy.1) i)).2.2
              (congrFun (congrArg Prod.fst heq) i)
          · exact eq_of_div_eq_of_mod_eq
              (mem_vinogradovResidueClass.mp (by
                simpa [C] using (Fintype.mem_piFinset.mp hzxy.2) i)).2.2
              (mem_vinogradovResidueClass.mp (by
                simpa [C] using (Fintype.mem_piFinset.mp hwxy.2) i)).2.2
              (congrFun (congrArg Prod.snd heq) i)
      calc
        Su.card ≤ (vinogradovShiftedEnergy (r := r)
            (vinogradovModCurve Nq k) (Finset.range (Q + 1)) d) :=
          Finset.card_le_card_of_injOn quotPair hmapsQ hinjQ
        _ ≤ vinogradovJ r k (Q + 1) :=
          shiftedZeroBasedEnergy_le_vinogradovJ r k Q d
        _ = vinogradovJ r k (P / p + 1) := rfl
    calc
      (S.filter fun z => toV z = v).card = Sv.card := rfl
      _ ≤ vinogradovJ r k (P / p + 1) *
          (vinogradovLinnikFiber p k
            (vinogradovTranslatedRep p k a v)).card :=
        Finset.card_le_mul_card_image_of_maps_to hmapsU _ hfiberU
      _ ≤ vinogradovJ r k (P / p + 1) *
          (k.factorial * p ^ (k * (k - 1) / 2)) :=
        Nat.mul_le_mul_left _
          (card_vinogradovLinnikFiber_le hp hk hpk _)
      _ = (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1) := by ac_rfl
  calc
    S.card ≤ ((k.factorial * p ^ (k * (k - 1) / 2)) *
        vinogradovJ r k (P / p + 1)) *
        (vinogradovTuples k P).card :=
      Finset.card_le_mul_card_image_of_maps_to hmapsV _ hfiberV
    _ = P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
        vinogradovJ r k (P / p + 1) := by
      rw [card_vinogradovTuples]
      ring

/-! ## Splitting off the first `k` coordinates -/

private def vinogradovSplitEquiv (r k : ℕ) :
    (Fin (r + k) → ℕ) ≃ ((Fin k → ℕ) × (Fin r → ℕ)) :=
  (Equiv.arrowCongr (finCongr (Nat.add_comm r k)) (Equiv.refl ℕ)).trans
    ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl ℕ)).trans
      (Equiv.sumArrowEquivProdArrow (Fin k) (Fin r) ℕ))

private theorem splitEquiv_fst_apply (r k : ℕ) (z : Fin (r + k) → ℕ)
    (i : Fin k) :
    (vinogradovSplitEquiv r k z).1 i =
      z (((finCongr (Nat.add_comm r k)).trans finSumFinEquiv.symm).symm
        (Sum.inl i)) := by
  rfl

private theorem splitEquiv_snd_apply (r k : ℕ) (z : Fin (r + k) → ℕ)
    (i : Fin r) :
    (vinogradovSplitEquiv r k z).2 i =
      z (((finCongr (Nat.add_comm r k)).trans finSumFinEquiv.symm).symm
        (Sum.inr i)) := by
  rfl

private theorem splitEquiv_powerSum (r k j : ℕ) (z : Fin (r + k) → ℕ) :
    vinogradovPowerSum z j =
      vinogradovPowerSum (vinogradovSplitEquiv r k z).1 j +
        vinogradovPowerSum (vinogradovSplitEquiv r k z).2 j := by
  classical
  let e := (finCongr (Nat.add_comm r k)).trans finSumFinEquiv.symm
  rw [vinogradovPowerSum, vinogradovPowerSum, vinogradovPowerSum]
  calc
    (∑ i : Fin (r + k), z i ^ j) =
        ∑ q : Fin k ⊕ Fin r, z (e.symm q) ^ j := by
      exact Fintype.sum_equiv e (fun i => z i ^ j)
        (fun q => z (e.symm q) ^ j) (fun i => by simp [e])
    _ = (∑ i : Fin k, z (e.symm (Sum.inl i)) ^ j) +
        ∑ i : Fin r, z (e.symm (Sum.inr i)) ^ j := by
      rw [Fintype.sum_sum_type]
    _ = _ := by
      simp only [e, ← splitEquiv_fst_apply, ← splitEquiv_snd_apply]

private theorem splitEquiv_mem_tuples {r k P : ℕ} (z : Fin (r + k) → ℕ) :
    z ∈ vinogradovTuples (r + k) P ↔
      (vinogradovSplitEquiv r k z).1 ∈ vinogradovTuples k P ∧
        (vinogradovSplitEquiv r k z).2 ∈ vinogradovTuples r P := by
  simp only [mem_vinogradovTuples]
  constructor
  · intro h
    exact ⟨fun i => by rw [splitEquiv_fst_apply]; exact h _,
      fun i => by rw [splitEquiv_snd_apply]; exact h _⟩
  · rintro ⟨hu, hx⟩ i
    let e := (finCongr (Nat.add_comm r k)).trans finSumFinEquiv.symm
    have hu' : ∀ q : Fin k, 1 ≤ z (e.symm (Sum.inl q)) ∧
        z (e.symm (Sum.inl q)) ≤ P := by
      intro q
      simpa only [e, splitEquiv_fst_apply] using hu q
    have hx' : ∀ q : Fin r, 1 ≤ z (e.symm (Sum.inr q)) ∧
        z (e.symm (Sum.inr q)) ≤ P := by
      intro q
      simpa only [e, splitEquiv_snd_apply] using hx q
    generalize hq : e i = q
    rcases q with q | q
    · have hi : i = e.symm (Sum.inl q) := by rw [← hq]; simp
      rw [hi]
      exact hu' q
    · have hi : i = e.symm (Sum.inr q) := by rw [← hq]; simp
      rw [hi]
      exact hx' q

private theorem splitEquiv_firstWellConditioned {r k p : ℕ}
    (z : Fin (r + k) → ℕ) :
    VinogradovFirstWellConditioned p z ↔
      VinogradovWellConditioned p (vinogradovSplitEquiv r k z).1 := by
  rfl

private theorem firstWellPairCount_eq_selectedEnergy {r k P p : ℕ} :
    let N := vinogradovSafeModulus (r + k) k P
    letI : NeZero N :=
      ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos (r + k) k P)⟩
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) =
      vinogradovSelectedEnergy (vinogradovBlockCurve N k)
        ((vinogradovTuples k P).filter (VinogradovWellConditioned p))
        (vinogradovModCurve N k)
        (fun _ : Fin r => Finset.Icc 1 P)
        (fun _ : Fin r => Finset.Icc 1 P) := by
  classical
  dsimp only
  let N := vinogradovSafeModulus (r + k) k P
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos (r + k) k P)⟩
  let A := (vinogradovTuples (r + k) P).filter
    (VinogradovFirstWellConditioned p)
  let W := (vinogradovTuples k P).filter (VinogradovWellConditioned p)
  let L := ((A ×ˢ A).filter fun xy =>
    vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2)
  let R := (((W ×ˢ W) ×ˢ
      (Fintype.piFinset (fun _ : Fin r => Finset.Icc 1 P) ×ˢ
        Fintype.piFinset (fun _ : Fin r => Finset.Icc 1 P))).filter fun z =>
      vinogradovBlockCurve N k z.1.1 +
          ∑ i, vinogradovModCurve N k (z.2.1 i) =
        vinogradovBlockCurve N k z.1.2 +
          ∑ i, vinogradovModCurve N k (z.2.2 i))
  let splitPair : ((Fin (r + k) → ℕ) × (Fin (r + k) → ℕ)) →
      (((Fin k → ℕ) × (Fin k → ℕ)) ×
        ((Fin r → ℕ) × (Fin r → ℕ))) := fun xy =>
    (((vinogradovSplitEquiv r k xy.1).1,
      (vinogradovSplitEquiv r k xy.2).1),
      ((vinogradovSplitEquiv r k xy.1).2,
      (vinogradovSplitEquiv r k xy.2).2))
  change L.card = R.card
  apply Finset.card_bij (fun xy _ => splitPair xy)
  · intro xy hxy
    dsimp [L] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    have hxA := Finset.mem_filter.mp hxy.1.1
    have hyA := Finset.mem_filter.mp hxy.1.2
    have hxsplit := splitEquiv_mem_tuples xy.1 |>.mp hxA.1
    have hysplit := splitEquiv_mem_tuples xy.2 |>.mp hyA.1
    dsimp [R, splitPair]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
        ⟨hxsplit.1, (splitEquiv_firstWellConditioned xy.1).mp hxA.2⟩,
      Finset.mem_filter.mpr
        ⟨hysplit.1, (splitEquiv_firstWellConditioned xy.2).mp hyA.2⟩⟩,
      Finset.mem_product.mpr ⟨
      Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_Icc.mpr (mem_vinogradovTuples.mp hxsplit.2 i),
      Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_Icc.mpr (mem_vinogradovTuples.mp hysplit.2 i)⟩⟩, ?_⟩
    apply (blockCurve_eq_iff_totalPowerSums_eq
      (vinogradovSplitEquiv r k xy.1).1
      (vinogradovSplitEquiv r k xy.2).1
      (vinogradovSplitEquiv r k xy.1).2
      (vinogradovSplitEquiv r k xy.2).2
      (fun i => (mem_vinogradovTuples.mp hxsplit.1 i).2)
      (fun i => (mem_vinogradovTuples.mp hysplit.1 i).2)
      (fun i => (mem_vinogradovTuples.mp hxsplit.2 i).2)
      (fun i => (mem_vinogradovTuples.mp hysplit.2 i).2)).mpr
    intro j hj
    rw [← splitEquiv_powerSum, ← splitEquiv_powerSum]
    exact isVinogradovSolution_iff_agreeUpTo.mp
      (isVinogradovSolution_iff_momentVector_eq.mpr hxy.2) j hj
  · intro x hx y hy heq
    apply Prod.ext
    · apply (vinogradovSplitEquiv r k).injective
      exact Prod.ext (congrArg (fun z => z.1.1) heq)
        (congrArg (fun z => z.2.1) heq)
    · apply (vinogradovSplitEquiv r k).injective
      exact Prod.ext (congrArg (fun z => z.1.2) heq)
        (congrArg (fun z => z.2.2) heq)
  · intro z hz
    dsimp [R] at hz
    rw [Finset.mem_filter] at hz
    have hout := Finset.mem_product.mp hz.1
    have huv := Finset.mem_product.mp hout.1
    have hfree := Finset.mem_product.mp hout.2
    let x := (vinogradovSplitEquiv r k).symm (z.1.1, z.2.1)
    let y := (vinogradovSplitEquiv r k).symm (z.1.2, z.2.2)
    have hxsplit : vinogradovSplitEquiv r k x = (z.1.1, z.2.1) := by simp [x]
    have hysplit : vinogradovSplitEquiv r k y = (z.1.2, z.2.2) := by simp [y]
    have hxmem : x ∈ vinogradovTuples (r + k) P := by
      rw [splitEquiv_mem_tuples, hxsplit]
      exact ⟨(Finset.mem_filter.mp huv.1).1,
        mem_vinogradovTuples.mpr fun i => Finset.mem_Icc.mp
          ((Fintype.mem_piFinset.mp hfree.1) i)⟩
    have hymem : y ∈ vinogradovTuples (r + k) P := by
      rw [splitEquiv_mem_tuples, hysplit]
      exact ⟨(Finset.mem_filter.mp huv.2).1,
        mem_vinogradovTuples.mpr fun i => Finset.mem_Icc.mp
          ((Fintype.mem_piFinset.mp hfree.2) i)⟩
    refine ⟨(x, y), ?_, ?_⟩
    · dsimp [L]
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_filter.mpr ⟨hxmem, ?_⟩,
        Finset.mem_filter.mpr ⟨hymem, ?_⟩⟩, ?_⟩
      · rw [splitEquiv_firstWellConditioned, hxsplit]
        exact (Finset.mem_filter.mp huv.1).2
      · rw [splitEquiv_firstWellConditioned, hysplit]
        exact (Finset.mem_filter.mp huv.2).2
      · apply isVinogradovSolution_iff_momentVector_eq.mp
        rw [isVinogradovSolution_iff_agreeUpTo]
        intro j hj
        rw [splitEquiv_powerSum, splitEquiv_powerSum, hxsplit, hysplit]
        exact (blockCurve_eq_iff_totalPowerSums_eq z.1.1 z.1.2 z.2.1 z.2.2
          (fun i => (mem_vinogradovTuples.mp (Finset.mem_filter.mp huv.1).1 i).2)
          (fun i => (mem_vinogradovTuples.mp (Finset.mem_filter.mp huv.2).1 i).2)
          (fun i => (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hfree.1) i)).2)
          (fun i => (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hfree.2) i)).2)).mp hz.2 j hj
    · dsimp [splitPair]
      rw [hxsplit, hysplit]

private theorem selectedFullEnergy_le {r k P p : ℕ}
    (hp : p.Prime) (hr : 0 < r) (hk : 0 < k)
    (hpk : k < p) (hP : P < p ^ k) :
    let N := vinogradovSafeModulus (r + k) k P
    letI : NeZero N :=
      ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos (r + k) k P)⟩
    vinogradovSelectedEnergy (vinogradovBlockCurve N k)
        ((vinogradovTuples k P).filter (VinogradovWellConditioned p))
        (vinogradovModCurve N k)
        (fun _ : Fin r => Finset.Icc 1 P)
        (fun _ : Fin r => Finset.Icc 1 P) ≤
      p ^ (2 * r) *
        (2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1))) := by
  classical
  dsimp only
  let N := vinogradovSafeModulus (r + k) k P
  letI : NeZero N :=
    ⟨Nat.ne_of_gt (vinogradovSafeModulus_pos (r + k) k P)⟩
  let W := (vinogradovTuples k P).filter (VinogradovWellConditioned p)
  let S := (((W ×ˢ W) ×ˢ
      (Fintype.piFinset (fun _ : Fin r => Finset.Icc 1 P) ×ˢ
        Fintype.piFinset (fun _ : Fin r => Finset.Icc 1 P))).filter fun z =>
      vinogradovBlockCurve N k z.1.1 +
          ∑ i, vinogradovModCurve N k (z.2.1 i) =
        vinogradovBlockCurve N k z.1.2 +
          ∑ i, vinogradovModCurve N k (z.2.2 i))
  let residues : (((Fin k → ℕ) × (Fin k → ℕ)) ×
      ((Fin r → ℕ) × (Fin r → ℕ))) →
      ((Fin r → Fin p) × (Fin r → Fin p)) := fun z =>
    (fun i => ⟨z.2.1 i % p, Nat.mod_lt _ hp.pos⟩,
      fun i => ⟨z.2.2 i % p, Nat.mod_lt _ hp.pos⟩)
  change S.card ≤ _
  have hmaps : ∀ z ∈ S, residues z ∈
      (Finset.univ : Finset ((Fin r → Fin p) × (Fin r → Fin p))) := by
    simp
  have hfiber : ∀ uv ∈
      (Finset.univ : Finset ((Fin r → Fin p) × (Fin r → Fin p))),
      (S.filter fun z => residues z = uv).card ≤
        2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1)) := by
    intro uv huv
    let A : Fin r → Finset ℕ := fun i =>
      vinogradovResidueClass P p (uv.1 i).val
    let B : Fin r → Finset ℕ := fun i =>
      vinogradovResidueClass P p (uv.2 i).val
    let T := (((W ×ˢ W) ×ˢ
        (Fintype.piFinset A ×ˢ Fintype.piFinset B)).filter fun z =>
        vinogradovBlockCurve N k z.1.1 +
            ∑ i, vinogradovModCurve N k (z.2.1 i) =
          vinogradovBlockCurve N k z.1.2 +
            ∑ i, vinogradovModCurve N k (z.2.2 i))
    have hsub : S.filter (fun z => residues z = uv) ⊆ T := by
      intro z hz
      rw [Finset.mem_filter] at hz
      have hzS := hz.1
      dsimp [S] at hzS
      rw [Finset.mem_filter] at hzS
      have hout := Finset.mem_product.mp hzS.1
      have hfree := Finset.mem_product.mp hout.2
      have hxfull := Fintype.mem_piFinset.mp hfree.1
      have hyfull := Fintype.mem_piFinset.mp hfree.2
      dsimp [T]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hout.1,
        Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_,
          Fintype.mem_piFinset.mpr fun i => ?_⟩⟩, hzS.2⟩
      · apply mem_vinogradovResidueClass.mpr
        refine ⟨(Finset.mem_Icc.mp (hxfull i)).1,
          (Finset.mem_Icc.mp (hxfull i)).2, ?_⟩
        have hcoord := congrArg (fun q => (q.1 i).val) hz.2
        simpa [residues] using hcoord
      · apply mem_vinogradovResidueClass.mpr
        refine ⟨(Finset.mem_Icc.mp (hyfull i)).1,
          (Finset.mem_Icc.mp (hyfull i)).2, ?_⟩
        have hcoord := congrArg (fun q => (q.2 i).val) hz.2
        simpa [residues] using hcoord
    calc
      (S.filter fun z => residues z = uv).card ≤ T.card :=
        Finset.card_le_card hsub
      _ = vinogradovSelectedEnergy (vinogradovBlockCurve N k) W
          (vinogradovModCurve N k) A B := rfl
      _ ≤ (∑ i, vinogradovSelectedEnergy (vinogradovBlockCurve N k) W
            (vinogradovModCurve N k)
            (fun _ : Fin r => A i) (fun _ : Fin r => A i)) +
          ∑ i, vinogradovSelectedEnergy (vinogradovBlockCurve N k) W
            (vinogradovModCurve N k)
            (fun _ : Fin r => B i) (fun _ : Fin r => B i) :=
        selectedEnergy_le_sum_diagonal hr _ _ _ _ _
      _ ≤ (∑ _i : Fin r,
            P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
              vinogradovJ r k (P / p + 1)) +
          ∑ _i : Fin r,
            P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
              vinogradovJ r k (P / p + 1) := by
        apply Nat.add_le_add <;> apply Finset.sum_le_sum <;> intro i hi
        · exact selectedDiagonalEnergy_le hp hk hpk hP
        · exact selectedDiagonalEnergy_le hp hk hpk hP
      _ = 2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1)) := by
        simp [two_mul, add_mul]
  calc
    S.card ≤ (2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1))) *
        (Finset.univ : Finset ((Fin r → Fin p) ×
          (Fin r → Fin p))).card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber
    _ = p ^ (2 * r) *
        (2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1))) := by
      simp
      ring

/-- Fixed-prime fundamental estimate for the nonsingular first block. -/
theorem vinogradov_firstWell_pairCount_le {r k P p : ℕ}
    (hp : p.Prime) (hr : 0 < r) (hk : 0 < k)
    (hpk : k < p) (hP : P < p ^ k) :
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) ≤
      p ^ (2 * r) *
        (2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1))) := by
  rw [firstWellPairCount_eq_selectedEnergy]
  exact selectedFullEnergy_le hp hr hk hpk hP

/-! ## A bounded family of separating primes -/

private noncomputable def vinogradovNextPrime (n : ℕ) : ℕ :=
  if hn : n = 0 then 2 else Classical.choose (Nat.bertrand n hn)

private theorem nextPrime_spec {n : ℕ} (hn : 0 < n) :
    (vinogradovNextPrime n).Prime ∧ n < vinogradovNextPrime n ∧
      vinogradovNextPrime n ≤ 2 * n := by
  rw [vinogradovNextPrime, dif_neg hn.ne']
  exact Classical.choose_spec (Nat.bertrand n hn.ne')

private noncomputable def vinogradovPrimeChain (q : ℕ) : ℕ → ℕ
  | 0 => q
  | t + 1 => vinogradovNextPrime (vinogradovPrimeChain q t)

private theorem primeChain_pos {q : ℕ} (hq : 0 < q) :
    ∀ t, 0 < vinogradovPrimeChain q t := by
  intro t
  induction t with
  | zero => exact hq
  | succ t ih => exact (nextPrime_spec ih).1.pos

private theorem primeChain_succ_prime {q : ℕ} (hq : 0 < q) (t : ℕ) :
    (vinogradovPrimeChain q (t + 1)).Prime := by
  exact (nextPrime_spec (primeChain_pos hq t)).1

private theorem primeChain_strictMono {q : ℕ} (hq : 0 < q) :
    StrictMono (vinogradovPrimeChain q) := by
  apply strictMono_nat_of_lt_succ
  intro t
  exact (nextPrime_spec (primeChain_pos hq t)).2.1

private theorem primeChain_le {q t : ℕ} (hq : 0 < q) :
    vinogradovPrimeChain q t ≤ 2 ^ t * q := by
  induction t with
  | zero => simp [vinogradovPrimeChain]
  | succ t ih =>
      calc
        vinogradovPrimeChain q (t + 1) ≤
            2 * vinogradovPrimeChain q t :=
          (nextPrime_spec (primeChain_pos hq t)).2.2
        _ ≤ 2 * (2 ^ t * q) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (t + 1) * q := by ring

private def vinogradovDiscriminant {k : ℕ} (u : Fin k → ℕ) : ℕ :=
  ∏ q : VinogradovIndexPair k,
    Nat.dist (u (vinogradovIndexPairFirst q))
      (u (vinogradovIndexPairSecond q))

private theorem prime_dvd_discriminant_of_not_well {k p : ℕ}
    (u : Fin k → ℕ) (hbad : ¬ VinogradovWellConditioned p u) :
    p ∣ vinogradovDiscriminant u := by
  simp only [VinogradovWellConditioned] at hbad
  push_neg at hbad
  obtain ⟨i, j, hij, hmod⟩ := hbad
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let q : VinogradovIndexPair k := ⟨j, ⟨i, hijlt⟩⟩
    apply dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
    have hme : Nat.ModEq p (u i) (u j) := by
      simpa [Nat.ModEq] using hmod
    rw [show vinogradovIndexPairFirst q = i by rfl,
      show vinogradovIndexPairSecond q = j by rfl]
    by_cases huv : u i ≤ u j
    · rw [Nat.dist_eq_sub_of_le huv]
      exact (Nat.modEq_iff_dvd' huv).mp hme
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_not_ge huv)]
      exact (Nat.modEq_iff_dvd' (Nat.le_of_not_ge huv)).mp hme.symm
  · let q : VinogradovIndexPair k := ⟨i, ⟨j, hjilt⟩⟩
    apply dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
    have hme : Nat.ModEq p (u j) (u i) := by
      simpa [Nat.ModEq] using hmod.symm
    rw [show vinogradovIndexPairFirst q = j by rfl,
      show vinogradovIndexPairSecond q = i by rfl]
    by_cases huv : u j ≤ u i
    · rw [Nat.dist_eq_sub_of_le huv]
      exact (Nat.modEq_iff_dvd' huv).mp hme
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_not_ge huv)]
      exact (Nat.modEq_iff_dvd' (Nat.le_of_not_ge huv)).mp hme.symm

private theorem discriminant_pos_of_injective {k : ℕ} (u : Fin k → ℕ)
    (hu : Function.Injective u) : 0 < vinogradovDiscriminant u := by
  rw [vinogradovDiscriminant]
  apply Finset.prod_pos
  intro q hq
  have hne := hu.ne (vinogradovIndexPair_ne q)
  by_cases hle : u (vinogradovIndexPairFirst q) ≤
      u (vinogradovIndexPairSecond q)
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_not_ge hle)]
    omega

private theorem discriminant_le_pow {k P : ℕ} (u : Fin k → ℕ)
    (huP : ∀ i, u i ≤ P) :
    vinogradovDiscriminant u ≤ P ^ k.choose 2 := by
  calc
    vinogradovDiscriminant u ≤
        ∏ _q : VinogradovIndexPair k, P := by
      apply Finset.prod_le_prod'
      intro q hq
      by_cases huv : u (vinogradovIndexPairFirst q) ≤
          u (vinogradovIndexPairSecond q)
      · rw [Nat.dist_eq_sub_of_le huv]
        exact (Nat.sub_le _ _).trans (huP _)
      · rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_not_ge huv)]
        exact (Nat.sub_le _ _).trans (huP _)
    _ = P ^ k.choose 2 := by
      rw [Finset.prod_const, Finset.card_univ, card_vinogradovIndexPair]

/-! ### A polynomial-cost separating-prime family -/

/-- The primes in the dyadic interval `(q,2q]`. -/
private def vinogradovShortPrimes (q : ℕ) : Finset ℕ :=
  (Finset.Ioc q (2 * q)).filter Nat.Prime

private theorem blockLog_eq_sum_vinogradovShortPrimes (q : ℕ) :
    blockLog q = ∑ p ∈ vinogradovShortPrimes q, Real.log p := by
  unfold blockLog vinogradovShortPrimes
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp, hprime⟩, hq⟩
      exact ⟨⟨hq, by omega⟩, hprime⟩
    · rintro ⟨⟨hq, hp⟩, hprime⟩
      exact ⟨⟨by omega, hprime⟩, hq⟩
  · intro p hp
    rfl

/-- The elementary Chebyshev block estimate supplies any prescribed number
of primes in `(q,2q]` once `q` is a quadratic function of that number. -/
private theorem card_vinogradovShortPrimes_ge (q L : ℕ)
    (hq28 : 2 ^ 28 ≤ q) (hqL : 288 * L ^ 2 ≤ q) :
    L ≤ (vinogradovShortPrimes q).card := by
  have hq0 : 0 < q := by omega
  have hlogupper : blockLog q ≤
      ((vinogradovShortPrimes q).card : ℝ) * Real.log (2 * q) := by
    rw [blockLog_eq_sum_vinogradovShortPrimes]
    calc
      (∑ p ∈ vinogradovShortPrimes q, Real.log p) ≤
          (vinogradovShortPrimes q).card • Real.log (2 * (q : ℝ)) := by
        apply Finset.sum_le_card_nsmul
        intro p hp
        unfold vinogradovShortPrimes at hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        exact Real.log_le_log (by exact_mod_cast hq0.trans hp.1.1)
          (by exact_mod_cast hp.1.2)
      _ = ((vinogradovShortPrimes q).card : ℝ) * Real.log (2 * q) := by
        rw [nsmul_eq_mul]
  have hloglower := blockLog_ge hq28
  have hlogsqrt : Real.log (2 * (q : ℝ)) ≤ 2 * Real.sqrt (2 * q) := by
    have h := Real.log_le_rpow_div (x := 2 * (q : ℝ)) (by positivity)
      (by norm_num : (0 : ℝ) < 1 / 2)
    rw [show (2 * (q : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt (2 * q) by
      rw [Real.sqrt_eq_rpow]] at h
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (2 * (q : ℝ)) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (2 * (q : ℝ)) ^ 2 = 2 * q := by
    rw [Real.sq_sqrt]
    positivity
  have h24 : (24 * (L : ℝ)) ^ 2 ≤ 2 * q := by
    have hnat : 576 * L ^ 2 ≤ 2 * q := by
      calc
        576 * L ^ 2 = 2 * (288 * L ^ 2) := by ring
        _ ≤ 2 * q := Nat.mul_le_mul_left 2 hqL
    have hnatR : (576 : ℝ) * (L : ℝ) ^ 2 ≤ 2 * (q : ℝ) := by
      exact_mod_cast hnat
    calc
      (24 * (L : ℝ)) ^ 2 = (576 : ℝ) * (L : ℝ) ^ 2 := by ring
      _ ≤ (2 : ℝ) * (q : ℝ) := hnatR
  have h24sqrt : 24 * (L : ℝ) ≤ Real.sqrt (2 * q) := by
    apply (sq_le_sq₀ (by positivity) hsqrt0).mp
    rw [hsqrtSq]
    exact h24
  have hbudget : 6 * (L : ℝ) * Real.log (2 * q) ≤ q := by
    calc
      6 * (L : ℝ) * Real.log (2 * q) ≤
          12 * L * Real.sqrt (2 * q) := by
        nlinarith [hlogsqrt]
      _ ≤ q := by nlinarith
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith
  by_contra hcard
  have hcardlt : (vinogradovShortPrimes q).card < L :=
    Nat.lt_of_not_ge hcard
  have hcardR : ((vinogradovShortPrimes q).card : ℝ) < L := by
    exact_mod_cast hcardlt
  have hlogpos : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by
    exact_mod_cast (show 1 < 2 * q by omega))
  have hstrict : ((vinogradovShortPrimes q).card : ℝ) * Real.log (2 * q) <
      (L : ℝ) * Real.log (2 * q) :=
    mul_lt_mul_of_pos_right hcardR hlogpos
  have hmain : (q : ℝ) * Real.log 4 / 6 <
      (L : ℝ) * Real.log (2 * q) := lt_of_le_of_lt
        (hloglower.trans hlogupper) hstrict
  have hsmall : (L : ℝ) * Real.log (2 * q) ≤ (q : ℝ) / 6 := by
    nlinarith [hbudget]
  nlinarith [mul_le_mul_of_nonneg_left hlog4
    (show (0 : ℝ) ≤ q by positivity)]

private def vinogradovSeparatingFamilySize (k : ℕ) : ℕ :=
  (2 * k.choose 2) * k + 1

/-- A threshold at which one dyadic prime interval contains the complete
separating family.  Its growth is polynomial in `k`. -/
def vinogradovPrimeThreshold (k : ℕ) : ℕ :=
  max (2 ^ 28) (max k (288 * vinogradovSeparatingFamilySize k ^ 2))

private theorem vinogradovPrimeThreshold_ge_twoPow (k : ℕ) :
    2 ^ 28 ≤ vinogradovPrimeThreshold k := le_max_left _ _

private theorem vinogradovPrimeThreshold_ge_self (k : ℕ) :
    k ≤ vinogradovPrimeThreshold k :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem vinogradovPrimeThreshold_ge_family (k : ℕ) :
    288 * vinogradovSeparatingFamilySize k ^ 2 ≤
      vinogradovPrimeThreshold k :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- A fixed family of the required cardinality selected from `(q,2q]`.
Outside its intended range it is defined to be empty. -/
private noncomputable def vinogradovSeparatingPrimeFamily (k q : ℕ) : Finset ℕ :=
  if h : vinogradovSeparatingFamilySize k ≤ (vinogradovShortPrimes q).card then
    Classical.choose (Finset.exists_subset_card_eq h)
  else ∅

private theorem vinogradovSeparatingPrimeFamily_spec {k q : ℕ}
    (hq : vinogradovPrimeThreshold k ≤ q) :
    vinogradovSeparatingPrimeFamily k q ⊆ vinogradovShortPrimes q ∧
      (vinogradovSeparatingPrimeFamily k q).card =
        vinogradovSeparatingFamilySize k := by
  have hcard : vinogradovSeparatingFamilySize k ≤
      (vinogradovShortPrimes q).card :=
    card_vinogradovShortPrimes_ge q (vinogradovSeparatingFamilySize k)
      ((vinogradovPrimeThreshold_ge_twoPow k).trans hq)
      ((vinogradovPrimeThreshold_ge_family k).trans hq)
  rw [vinogradovSeparatingPrimeFamily, dif_pos hcard]
  exact Classical.choose_spec (Finset.exists_subset_card_eq hcard)

/-- A separating prime can be chosen in the single dyadic interval
`(q,2q]`; unlike the older Bertrand-chain construction, this costs only a
factor `2` in the mean-value recursion. -/
private theorem exists_short_separating_prime {k P q : ℕ}
    (hk : 2 ≤ k) (hq : vinogradovPrimeThreshold k ≤ q)
    (hPq : P < q ^ k)
    (u v : Fin k → ℕ) (huP : ∀ i, u i ≤ P) (hvP : ∀ i, v i ≤ P)
    (hu : Function.Injective u) (hv : Function.Injective v) :
    ∃ p ∈ vinogradovSeparatingPrimeFamily k q,
      p.Prime ∧ k < p ∧ p ≤ 2 * q ∧
        VinogradovWellConditioned p u ∧ VinogradovWellConditioned p v := by
  classical
  let E := 2 * k.choose 2
  let M := E * k + 1
  let T := vinogradovSeparatingPrimeFamily k q
  have hspec := vinogradovSeparatingPrimeFamily_spec hq
  have hTcard : T.card = M := by
    simpa only [T, M, E, vinogradovSeparatingFamilySize] using hspec.2
  have hkq : k ≤ q := (vinogradovPrimeThreshold_ge_self k).trans hq
  have hq0 : 0 < q := lt_of_lt_of_le (by omega : 0 < k) hkq
  by_contra hnone
  push_neg at hnone
  have hdata : ∀ p ∈ T, p.Prime ∧ q < p ∧ p ≤ 2 * q := by
    intro p hp
    have hpS := hspec.1 hp
    unfold vinogradovShortPrimes at hpS
    rw [Finset.mem_filter, Finset.mem_Ioc] at hpS
    exact ⟨hpS.2, hpS.1.1, hpS.1.2⟩
  have hdvd : ∀ p ∈ T,
      p ∣ vinogradovDiscriminant u * vinogradovDiscriminant v := by
    intro p hp
    have hs := hnone p hp
    have hd := hdata p hp
    have hkp : k < p := lt_of_le_of_lt hkq hd.2.1
    specialize hs hd.1 hkp hd.2.2
    by_cases hwu : VinogradovWellConditioned p u
    · exact dvd_mul_of_dvd_right
        (prime_dvd_discriminant_of_not_well v (hs hwu)) _
    · exact dvd_mul_of_dvd_left
        (prime_dvd_discriminant_of_not_well u hwu) _
  have hpairwise : (T : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp r hr hpr
    exact (Nat.coprime_primes (hdata p hp).1 (hdata r hr).1).mpr hpr
  have hprodDaux : ∀ s : Finset ℕ, s ⊆ T →
      (∀ p ∈ s, p ∣ vinogradovDiscriminant u * vinogradovDiscriminant v) →
      (∏ p ∈ s, p) ∣ vinogradovDiscriminant u * vinogradovDiscriminant v := by
    intro s hsT
    induction s using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
        intro hall
        rw [Finset.prod_insert hps]
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        · apply Nat.Coprime.prod_right
          intro r hr
          exact hpairwise (hsT (Finset.mem_insert_self p s))
            (hsT (Finset.mem_insert_of_mem hr)) (by
              intro h
              exact hps (h ▸ hr))
        · exact hall p (Finset.mem_insert_self p s)
        · exact ih (fun r hr => hsT (Finset.mem_insert_of_mem hr))
            (fun r hr => hall r (Finset.mem_insert_of_mem hr))
  have hprodD : (∏ p ∈ T, p) ∣
      vinogradovDiscriminant u * vinogradovDiscriminant v :=
    hprodDaux T (fun _ hp => hp) hdvd
  have hDpos : 0 < vinogradovDiscriminant u * vinogradovDiscriminant v :=
    Nat.mul_pos (discriminant_pos_of_injective u hu)
      (discriminant_pos_of_injective v hv)
  have hprodLeD := Nat.le_of_dvd hDpos hprodD
  have hDle : vinogradovDiscriminant u * vinogradovDiscriminant v ≤ P ^ E := by
    calc
      vinogradovDiscriminant u * vinogradovDiscriminant v ≤
          P ^ k.choose 2 * P ^ k.choose 2 :=
        Nat.mul_le_mul (discriminant_le_pow u huP)
          (discriminant_le_pow v hvP)
      _ = P ^ (2 * k.choose 2) := by rw [← pow_add]; congr 1; omega
      _ = P ^ E := rfl
  have hE0 : 0 < E := by
    dsimp [E]
    exact Nat.mul_pos (by omega) (Nat.choose_pos hk)
  have hPE : P ^ E < (q ^ k) ^ E := Nat.pow_lt_pow_left hPq hE0.ne'
  have hqexp : (q ^ k) ^ E ≤ q ^ M := by
    calc
      (q ^ k) ^ E = q ^ (k * E) := (pow_mul q k E).symm
      _ ≤ q ^ M := by
        apply Nat.pow_le_pow_right hq0
        dsimp [M]
        rw [mul_comm k E]
        exact Nat.le_succ _
  have hqprod : q ^ M < ∏ p ∈ T, p := by
    calc
      q ^ M = ∏ _p ∈ T, q := by simp [hTcard]
      _ < ∏ p ∈ T, p := by
        apply Finset.prod_lt_prod (fun _ _ => hq0)
        · intro p hp
          exact (hdata p hp).2.1.le
        · have hTne : T.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hTempty
            rw [hTempty] at hTcard
            simp only [Finset.card_empty] at hTcard
            dsimp [M, E, vinogradovSeparatingFamilySize] at hTcard
            omega
          obtain ⟨p, hp⟩ := hTne
          exact ⟨p, hp, (hdata p hp).2.1⟩
  have hcontra : P ^ E < P ^ E :=
    (((hPE.trans_le hqexp).trans hqprod).trans_le hprodLeD).trans_le hDle
  exact (lt_irrefl _ hcontra)

/-- Among a fixed number of consecutive Bertrand primes, one separates two
ordered `k`-blocks whose coordinates are individually distinct. -/
private theorem exists_separating_prime {k P q : ℕ}
    (hk : 2 ≤ k) (hq : k ≤ q) (hPq : P < q ^ k)
    (u v : Fin k → ℕ) (huP : ∀ i, u i ≤ P) (hvP : ∀ i, v i ≤ P)
    (hu : Function.Injective u) (hv : Function.Injective v) :
    let M := (2 * k.choose 2) * k + 1
    ∃ t : Fin M,
      let p := vinogradovPrimeChain q (t + 1)
      p.Prime ∧ k < p ∧ p ≤ 2 ^ M * q ∧
        VinogradovWellConditioned p u ∧ VinogradovWellConditioned p v := by
  dsimp only
  let E := 2 * k.choose 2
  let M := E * k + 1
  have hq0 : 0 < q := lt_of_lt_of_le (by omega : 0 < k) hq
  by_contra hnone
  push_neg at hnone
  have hdvd : ∀ t : Fin M,
      vinogradovPrimeChain q (t + 1) ∣
        vinogradovDiscriminant u * vinogradovDiscriminant v := by
    intro t
    have hs := hnone t
    have hp := primeChain_succ_prime hq0 t
    have hkp : k < vinogradovPrimeChain q (t + 1) :=
      lt_of_le_of_lt hq ((primeChain_strictMono hq0) (Nat.zero_lt_succ t))
    have hpupper : vinogradovPrimeChain q (t + 1) ≤ 2 ^ M * q := by
      exact (primeChain_le (q := q) (t := t + 1) hq0).trans (Nat.mul_le_mul_right q
        (Nat.pow_le_pow_right (by omega : 0 < 2)
          (Nat.succ_le_of_lt t.isLt)))
    specialize hs hp hkp hpupper
    by_cases hwu : VinogradovWellConditioned (vinogradovPrimeChain q (t + 1)) u
    · exact dvd_mul_of_dvd_right
        (prime_dvd_discriminant_of_not_well v (hs hwu)) _
    · exact dvd_mul_of_dvd_left
        (prime_dvd_discriminant_of_not_well u hwu) _
  have hpairwise : Pairwise
      (Function.onFun Nat.Coprime fun t : Fin M =>
        vinogradovPrimeChain q (t + 1)) := by
    intro i j hij
    have hne : vinogradovPrimeChain q (i + 1) ≠
        vinogradovPrimeChain q (j + 1) :=
      (primeChain_strictMono hq0).injective.ne (by
        intro h
        apply hij
        exact Fin.ext (Nat.succ.inj h))
    exact (Nat.coprime_primes (primeChain_succ_prime hq0 i)
      (primeChain_succ_prime hq0 j)).mpr hne
  have hprodDaux : ∀ s : Finset (Fin M),
      (∀ t ∈ s, vinogradovPrimeChain q (t + 1) ∣
        vinogradovDiscriminant u * vinogradovDiscriminant v) →
      (∏ t ∈ s, vinogradovPrimeChain q (t + 1)) ∣
        vinogradovDiscriminant u * vinogradovDiscriminant v := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert t s hts ih =>
        intro hall
        rw [Finset.prod_insert hts]
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        · apply Nat.Coprime.prod_right
          intro i hi
          exact hpairwise (by
            intro hit
            exact hts (hit ▸ hi))
        · exact hall t (Finset.mem_insert_self t s)
        · exact ih fun i hi => hall i (Finset.mem_insert_of_mem hi)
  have hprodD : (∏ t : Fin M, vinogradovPrimeChain q (t + 1)) ∣
      vinogradovDiscriminant u * vinogradovDiscriminant v := by
    simpa using hprodDaux Finset.univ (fun t ht => hdvd t)
  have hDpos : 0 < vinogradovDiscriminant u * vinogradovDiscriminant v :=
    Nat.mul_pos (discriminant_pos_of_injective u hu)
      (discriminant_pos_of_injective v hv)
  have hprodLeD := Nat.le_of_dvd hDpos hprodD
  have hDle : vinogradovDiscriminant u * vinogradovDiscriminant v ≤ P ^ E := by
    calc
      vinogradovDiscriminant u * vinogradovDiscriminant v ≤
          P ^ k.choose 2 * P ^ k.choose 2 :=
        Nat.mul_le_mul (discriminant_le_pow u huP)
          (discriminant_le_pow v hvP)
      _ = P ^ (2 * k.choose 2) := by rw [← pow_add]; congr 1; omega
      _ = P ^ E := rfl
  have hE0 : 0 < E := by
    dsimp [E]
    exact Nat.mul_pos (by omega) (Nat.choose_pos hk)
  have hPE : P ^ E < (q ^ k) ^ E := Nat.pow_lt_pow_left hPq hE0.ne'
  have hqexp : (q ^ k) ^ E ≤ q ^ M := by
    calc
      (q ^ k) ^ E = q ^ (k * E) := (pow_mul q k E).symm
      _ ≤ q ^ M := by
        apply Nat.pow_le_pow_right hq0
        dsimp [M]
        rw [mul_comm k E]
        exact Nat.le_succ _
  have hqprod : q ^ M < ∏ t : Fin M,
      vinogradovPrimeChain q (t + 1) := by
    calc
      q ^ M = ∏ _t : Fin M, q := by simp
      _ < ∏ t : Fin M, vinogradovPrimeChain q (t + 1) := by
        apply Finset.prod_lt_prod (fun _ _ => hq0)
        · intro t ht
          exact ((primeChain_strictMono hq0) (Nat.zero_lt_succ t)).le
        · exact ⟨⟨0, by dsimp [M, E]; omega⟩, Finset.mem_univ _,
            (primeChain_strictMono hq0) (Nat.zero_lt_succ _)⟩
  have hcontra : P ^ E < P ^ E :=
    (((hPE.trans_le hqexp).trans hqprod).trans_le hprodLeD).trans_le hDle
  exact (lt_irrefl _ hcontra)

/-! ## Singular tuples and coordinate permutations -/

private def vinogradovValueSet {s : ℕ} (x : Fin s → ℕ) : Finset ℕ :=
  Finset.univ.image x

private def vinogradovFewValues (s k P : ℕ) : Finset (Fin s → ℕ) :=
  (vinogradovTuples s P).filter fun x => (vinogradovValueSet x).card < k

private theorem fewValues_subset_cover {s k P : ℕ} :
    vinogradovFewValues s k P ⊆
      (Finset.range k).biUnion fun t =>
        (Finset.powersetCard t (Finset.Icc 1 P)).biUnion fun V =>
          Fintype.piFinset fun _ : Fin s => V := by
  intro x hx
  rw [vinogradovFewValues, Finset.mem_filter] at hx
  rw [Finset.mem_biUnion]
  let V := vinogradovValueSet x
  refine ⟨V.card, Finset.mem_range.mpr hx.2, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨V, Finset.mem_powersetCard.mpr ⟨?_, rfl⟩, ?_⟩
  · intro n hn
    dsimp [V, vinogradovValueSet] at hn
    rw [Finset.mem_image] at hn
    obtain ⟨i, hi, rfl⟩ := hn
    exact Finset.mem_Icc.mpr (mem_vinogradovTuples.mp hx.1 i)
  · rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- A tuple using fewer than `k` distinct values has only `k-1` genuinely
free values; the remaining factor records the assignments of coordinates. -/
theorem card_vinogradovFewValues_le {s k P : ℕ} (hP : 1 ≤ P) :
    (vinogradovFewValues s k P).card ≤
      k * (P ^ (k - 1) * k ^ s) := by
  classical
  calc
    (vinogradovFewValues s k P).card ≤
        ((Finset.range k).biUnion fun t =>
          (Finset.powersetCard t (Finset.Icc 1 P)).biUnion fun V =>
            Fintype.piFinset fun _ : Fin s => V).card :=
      Finset.card_le_card fewValues_subset_cover
    _ ≤ ∑ t ∈ Finset.range k,
        ∑ V ∈ Finset.powersetCard t (Finset.Icc 1 P),
          t ^ s := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t ht => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun V hV => ?_)
      calc
        (Fintype.piFinset fun _ : Fin s => V).card = V.card ^ s := by
          simp [Fintype.card_piFinset]
        _ ≤ t ^ s := by rw [(Finset.mem_powersetCard.mp hV).2]
    _ ≤ ∑ _t ∈ Finset.range k, P ^ (k - 1) * k ^ s := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.sum_const, Finset.card_powersetCard, Nat.card_Icc]
      have htlt := Finset.mem_range.mp ht
      calc
        (P.choose t) * t ^ s ≤ P ^ t * t ^ s :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow P t)
        _ ≤ P ^ (k - 1) * k ^ s := Nat.mul_le_mul
          (Nat.pow_le_pow_right hP (by omega))
          (Nat.pow_le_pow_left (Nat.le_of_lt htlt) s)
    _ = k * (P ^ (k - 1) * k ^ s) := by simp

private def vinogradovPermutedFirstWell {r k : ℕ} (p : ℕ)
    (σ : Equiv.Perm (Fin (r + k))) (x : Fin (r + k) → ℕ) : Prop :=
  VinogradovFirstWellConditioned p (fun i => x (σ i))

noncomputable instance {r k p : ℕ} (σ : Equiv.Perm (Fin (r + k)))
    (x : Fin (r + k) → ℕ) : Decidable (vinogradovPermutedFirstWell p σ x) :=
  Classical.propDecidable _

private def vinogradovFirstEmbedding (r k : ℕ) : Fin k ↪ Fin (r + k) where
  toFun := vinogradovFirstIndex r
  inj' := by
    intro i j h
    apply Fin.ext
    simpa [vinogradovFirstIndex] using congrArg Fin.val h

private theorem exists_perm_first_injective {r k : ℕ} (x : Fin (r + k) → ℕ)
    (hx : k ≤ (vinogradovValueSet x).card) :
    ∃ σ : Equiv.Perm (Fin (r + k)),
      Function.Injective fun i : Fin k => x (σ (vinogradovFirstIndex r i)) := by
  classical
  obtain ⟨values, hvalues⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (s := vinogradovValueSet x) (by simpa using hx)
  have hmem : ∀ i, values i ∈ vinogradovValueSet x := fun i =>
    hvalues (Set.mem_range_self i)
  choose selected hselected using fun i =>
    (Finset.mem_image.mp (show values i ∈ Finset.univ.image x by
      simpa [vinogradovValueSet] using hmem i))
  have hsel : ∀ i, x (selected i) = values i := fun i => (hselected i).2
  let e : Fin k ↪ Fin (r + k) :=
    ⟨selected, fun i j hij => values.injective (by
      rw [← hsel i, hij, hsel j])⟩
  let f := vinogradovFirstEmbedding r k
  let rangeEquiv : Set.range f ≃ Set.range e :=
    f.toEquivRange.symm.trans e.toEquivRange
  let σ : Equiv.Perm (Fin (r + k)) := rangeEquiv.extendSubtype
  refine ⟨σ, ?_⟩
  intro i j hij
  have hsigma : ∀ t : Fin k, σ (f t) = e t := by
    intro t
    change rangeEquiv.extendSubtype (f t) = e t
    rw [Equiv.extendSubtype_apply_of_mem rangeEquiv (f t)
      (Set.mem_range_self t)]
    change ↑((f.toEquivRange.symm.trans e.toEquivRange)
      ⟨f t, Set.mem_range_self t⟩) = e t
    simp
  have hvaluesEq : values i = values j := by
    calc
      values i = x (e i) := (hsel i).symm
      _ = x (σ (f i)) := by rw [hsigma i]
      _ = x (σ (f j)) := by simpa [f, vinogradovFirstEmbedding] using hij
      _ = x (e j) := by rw [hsigma j]
      _ = values j := hsel j
  exact values.injective hvaluesEq

private theorem permute_powerSum {s : ℕ} (σ : Equiv.Perm (Fin s))
    (x : Fin s → ℕ) (j : ℕ) :
    vinogradovPowerSum (fun i => x (σ i)) j = vinogradovPowerSum x j := by
  rw [vinogradovPowerSum, vinogradovPowerSum]
  exact Equiv.sum_comp σ (fun i => x i ^ j)

private theorem permute_mem_tuples {s : ℕ} (σ : Equiv.Perm (Fin s))
    (x : Fin s → ℕ) {P : ℕ} :
    (fun i => x (σ i)) ∈ vinogradovTuples s P ↔ x ∈ vinogradovTuples s P := by
  simp only [mem_vinogradovTuples]
  constructor
  · intro h i
    simpa using h (σ.symm i)
  · intro h i
    exact h (σ i)

private theorem permute_momentVector {s : ℕ} (σ : Equiv.Perm (Fin s))
    (x : Fin s → ℕ) (k : ℕ) :
    vinogradovMomentVector k (fun i => x (σ i)) =
      vinogradovMomentVector k x := by
  funext j
  exact permute_powerSum σ x (j + 1)

private theorem permutedFirst_pairCount_eq {r k P p : ℕ}
    (σ : Equiv.Perm (Fin (r + k))) :
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (vinogradovPermutedFirstWell p σ))
        ((vinogradovTuples (r + k) P).filter
          (vinogradovPermutedFirstWell p σ)) =
      vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) := by
  classical
  let perm : (Fin (r + k) → ℕ) → (Fin (r + k) → ℕ) := fun x i => x (σ i)
  let L := (((vinogradovTuples (r + k) P).filter
      (vinogradovPermutedFirstWell p σ)) ×ˢ
    ((vinogradovTuples (r + k) P).filter
      (vinogradovPermutedFirstWell p σ))).filter fun xy =>
        vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2
  let R := (((vinogradovTuples (r + k) P).filter
      (VinogradovFirstWellConditioned p)) ×ˢ
    ((vinogradovTuples (r + k) P).filter
      (VinogradovFirstWellConditioned p))).filter fun xy =>
        vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2
  change L.card = R.card
  apply Finset.card_bij (fun xy _ => (perm xy.1, perm xy.2))
  · intro xy hxy
    dsimp [L] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    change (perm xy.1, perm xy.2) ∈
      ((((vinogradovTuples (r + k) P).filter
        (VinogradovFirstWellConditioned p)) ×ˢ
      ((vinogradovTuples (r + k) P).filter
        (VinogradovFirstWellConditioned p))).filter fun zw =>
          vinogradovMomentVector k zw.1 = vinogradovMomentVector k zw.2)
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Finset.mem_filter.mpr ⟨(permute_mem_tuples σ xy.1).mpr
        (Finset.mem_filter.mp hxy.1.1).1, ?_⟩,
      Finset.mem_filter.mpr ⟨(permute_mem_tuples σ xy.2).mpr
        (Finset.mem_filter.mp hxy.1.2).1, ?_⟩⟩, ?_⟩
    · exact (Finset.mem_filter.mp hxy.1.1).2
    · exact (Finset.mem_filter.mp hxy.1.2).2
    · dsimp [perm]
      rw [permute_momentVector, permute_momentVector]
      exact hxy.2
  · intro x hx y hy heq
    apply Prod.ext <;> funext i
    · have hcomp := congrArg Prod.fst heq
      have hi := congrFun hcomp (σ.symm i)
      simpa [perm] using hi
    · have hcomp := congrArg Prod.snd heq
      have hi := congrFun hcomp (σ.symm i)
      simpa [perm] using hi
  · intro xy hxy
    dsimp [R] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    let x : Fin (r + k) → ℕ := fun i => xy.1 (σ.symm i)
    let y : Fin (r + k) → ℕ := fun i => xy.2 (σ.symm i)
    refine ⟨(x, y), ?_, ?_⟩
    · dsimp [L]
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_filter.mpr ⟨?_, ?_⟩,
        Finset.mem_filter.mpr ⟨?_, ?_⟩⟩, ?_⟩
      · exact (permute_mem_tuples σ x).mp (by simpa [x] using
          (Finset.mem_filter.mp hxy.1.1).1)
      · simpa [vinogradovPermutedFirstWell, x] using
          (Finset.mem_filter.mp hxy.1.1).2
      · exact (permute_mem_tuples σ y).mp (by simpa [y] using
          (Finset.mem_filter.mp hxy.1.2).1)
      · simpa [vinogradovPermutedFirstWell, y] using
          (Finset.mem_filter.mp hxy.1.2).2
      · simpa [x, y, permute_momentVector] using hxy.2
    · simp [perm, x, y]

private theorem vinogradovPairCount_mono {s k : ℕ}
    {A A' B B' : Finset (Fin s → ℕ)} (hA : A ⊆ A') (hB : B ⊆ B') :
    vinogradovPairCount k A B ≤ vinogradovPairCount k A' B' := by
  rw [vinogradovPairCount, vinogradovPairCount]
  apply Finset.card_le_card
  intro xy hxy
  rw [Finset.mem_filter, Finset.mem_product] at hxy ⊢
  exact ⟨⟨hA hxy.1.1, hB hxy.1.2⟩, hxy.2⟩

private def vinogradovManyValues (s k P : ℕ) : Finset (Fin s → ℕ) :=
  (vinogradovTuples s P).filter fun x => k ≤ (vinogradovValueSet x).card

private theorem vinogradovTuples_eq_few_union_many (s k P : ℕ) :
    vinogradovTuples s P =
      vinogradovFewValues s k P ∪ vinogradovManyValues s k P := by
  ext x
  simp only [vinogradovFewValues, vinogradovManyValues, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro hx
    by_cases hcard : (vinogradovValueSet x).card < k
    · exact Or.inl ⟨hx, hcard⟩
    · exact Or.inr ⟨hx, Nat.le_of_not_gt hcard⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

private def vinogradovFundamentalTerm (r k P q : ℕ) : ℕ :=
  let M := (2 * k.choose 2) * k + 1
  let L := 2 ^ M * q
  L ^ (2 * r) *
    (2 * r * (P ^ k * (k.factorial * L ^ (k * (k - 1) / 2)) *
      vinogradovJ r k (P / q + 1)))

private theorem firstWell_pairCount_le_fundamentalTerm {r k P q p : ℕ}
    (hr : 0 < r) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hp : p.Prime) (hqp : q < p)
    (hpL : p ≤ 2 ^ ((2 * k.choose 2) * k + 1) * q)
    (hP : P < p ^ k) :
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) ≤
      vinogradovFundamentalTerm r k P q := by
  let M := (2 * k.choose 2) * k + 1
  let L := 2 ^ M * q
  have hbase := vinogradov_firstWell_pairCount_le hp hr (by omega)
    (lt_of_le_of_lt hkq hqp) hP
  dsimp [vinogradovFundamentalTerm, M, L]
  calc
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) ≤
      p ^ (2 * r) *
        (2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1))) := hbase
    _ ≤ (2 ^ ((2 * k.choose 2) * k + 1) * q) ^ (2 * r) *
        (2 * r * (P ^ k *
          (k.factorial * (2 ^ ((2 * k.choose 2) * k + 1) * q) ^
            (k * (k - 1) / 2)) * vinogradovJ r k (P / q + 1))) := by
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_left hpL _
      · apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpL _))
        · apply vinogradovJ_mono
          exact Nat.add_le_add_right (Nat.div_le_div_left hqp.le
            (lt_of_lt_of_le (by omega : 0 < k) hkq)) 1

/-- The fundamental nonsingular term when the separating prime lies in the
single dyadic interval `(q,2q]`. -/
private def vinogradovFundamentalTermShort (r k P q : ℕ) : ℕ :=
  let L := 2 * q
  L ^ (2 * r) *
    (2 * r * (P ^ k * (k.factorial * L ^ (k * (k - 1) / 2)) *
      vinogradovJ r k (P / q + 1)))

private theorem firstWell_pairCount_le_fundamentalTermShort {r k P q p : ℕ}
    (hr : 0 < r) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hp : p.Prime) (hqp : q < p) (hpL : p ≤ 2 * q)
    (hP : P < p ^ k) :
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) ≤
      vinogradovFundamentalTermShort r k P q := by
  let L := 2 * q
  have hbase := vinogradov_firstWell_pairCount_le hp hr (by omega)
    (lt_of_le_of_lt hkq hqp) hP
  dsimp [vinogradovFundamentalTermShort, L]
  calc
    vinogradovPairCount k
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p))
        ((vinogradovTuples (r + k) P).filter
          (VinogradovFirstWellConditioned p)) ≤
      p ^ (2 * r) *
        (2 * r * (P ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovJ r k (P / p + 1))) := hbase
    _ ≤ (2 * q) ^ (2 * r) *
        (2 * r * (P ^ k *
          (k.factorial * (2 * q) ^ (k * (k - 1) / 2)) *
            vinogradovJ r k (P / q + 1))) := by
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_left hpL _
      · apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpL _))
        · apply vinogradovJ_mono
          exact Nat.add_le_add_right (Nat.div_le_div_left hqp.le
            (lt_of_lt_of_le (by omega : 0 < k) hkq)) 1

/-- The nonsingular--nonsingular part is covered by two coordinate
permutations and one of the bounded Bertrand primes. -/
private theorem manyValues_pairCount_le {r k P q : ℕ}
    (hr : 0 < r) (hk : 2 ≤ k)
    (hq : k ≤ q) (hPq : P < q ^ k) :
    vinogradovPairCount k (vinogradovManyValues (r + k) k P)
        (vinogradovManyValues (r + k) k P) ≤
      ((r + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1)) *
        vinogradovFundamentalTerm r k P q := by
  classical
  let M := (2 * k.choose 2) * k + 1
  let G := vinogradovManyValues (r + k) k P
  let Sol := ((G ×ˢ G).filter fun xy =>
    vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2)
  let piece (σ τ : Equiv.Perm (Fin (r + k))) (t : Fin M) :=
    ((((vinogradovTuples (r + k) P).filter
        (vinogradovPermutedFirstWell (vinogradovPrimeChain q (t + 1)) σ)) ×ˢ
      ((vinogradovTuples (r + k) P).filter
        (vinogradovPermutedFirstWell (vinogradovPrimeChain q (t + 1)) τ))).filter
      fun xy => vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2)
  have hcover : Sol ⊆
      (Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun σ =>
        (Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun τ =>
          (Finset.univ : Finset (Fin M)).biUnion fun t => piece σ τ t := by
    intro xy hxy
    dsimp [Sol, G] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    have hxG := Finset.mem_filter.mp hxy.1.1
    have hyG := Finset.mem_filter.mp hxy.1.2
    obtain ⟨σ, hσ⟩ := exists_perm_first_injective xy.1 hxG.2
    obtain ⟨τ, hτ⟩ := exists_perm_first_injective xy.2 hyG.2
    let u : Fin k → ℕ := fun i => xy.1 (σ (vinogradovFirstIndex r i))
    let v : Fin k → ℕ := fun i => xy.2 (τ (vinogradovFirstIndex r i))
    obtain ⟨t, hp, hkp, hpL, hwu, hwv⟩ := exists_separating_prime
      hk hq hPq u v
      (fun i => (mem_vinogradovTuples.mp hxG.1 _).2)
      (fun i => (mem_vinogradovTuples.mp hyG.1 _).2) hσ hτ
    simp only [Finset.mem_biUnion]
    refine ⟨σ, Finset.mem_univ _, τ, Finset.mem_univ _, t, Finset.mem_univ _, ?_⟩
    dsimp [piece]
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_filter.mpr ⟨hxG.1, hwu⟩,
      Finset.mem_filter.mpr ⟨hyG.1, hwv⟩⟩, hxy.2⟩
  have hpiece : ∀ σ τ : Equiv.Perm (Fin (r + k)), ∀ t : Fin M,
      (piece σ τ t).card ≤ vinogradovFundamentalTerm r k P q := by
    intro σ τ t
    let p := vinogradovPrimeChain q (t + 1)
    let Aσ := (vinogradovTuples (r + k) P).filter
      (vinogradovPermutedFirstWell p σ)
    let Aτ := (vinogradovTuples (r + k) P).filter
      (vinogradovPermutedFirstWell p τ)
    have hp := primeChain_succ_prime (lt_of_lt_of_le (by omega : 0 < k) hq) t
    have hqp := (primeChain_strictMono
      (lt_of_lt_of_le (by omega : 0 < k) hq)) (Nat.zero_lt_succ t)
    have hpL : p ≤ 2 ^ M * q := (primeChain_le
      (q := q) (t := t + 1) (lt_of_lt_of_le (by omega : 0 < k) hq)).trans
        (Nat.mul_le_mul_right q (Nat.pow_le_pow_right (by omega : 0 < 2)
          (Nat.succ_le_of_lt t.isLt)))
    have hPp : P < p ^ k := hPq.trans_le
      (Nat.pow_le_pow_left hqp.le k)
    have hdiagσ : vinogradovPairCount k Aσ Aσ ≤
        vinogradovFundamentalTerm r k P q := by
      rw [permutedFirst_pairCount_eq]
      exact firstWell_pairCount_le_fundamentalTerm hr hk hq hp hqp hpL hPp
    have hdiagτ : vinogradovPairCount k Aτ Aτ ≤
        vinogradovFundamentalTerm r k P q := by
      rw [permutedFirst_pairCount_eq]
      exact firstWell_pairCount_le_fundamentalTerm hr hk hq hp hqp hpL hPp
    have hsq := vinogradovPairCount_sq_le (k := k) Aσ Aτ
    have hsq' : vinogradovPairCount k Aσ Aτ ^ 2 ≤
        vinogradovFundamentalTerm r k P q ^ 2 := by
      exact hsq.trans (Nat.mul_le_mul hdiagσ hdiagτ) |>.trans_eq (pow_two _).symm
    change vinogradovPairCount k Aσ Aτ ≤ _
    exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hsq'
  calc
    vinogradovPairCount k G G = Sol.card := rfl
    _ ≤ ((Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun σ =>
        (Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun τ =>
          (Finset.univ : Finset (Fin M)).biUnion fun t => piece σ τ t).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ _σ : Equiv.Perm (Fin (r + k)),
        ∑ _τ : Equiv.Perm (Fin (r + k)),
          ∑ _t : Fin M, vinogradovFundamentalTerm r k P q := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun σ hσ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun τ hτ => ?_)
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t ht => hpiece σ τ t)
    _ = ((r + k).factorial ^ 2 * M) *
        vinogradovFundamentalTerm r k P q := by
      simp [M, pow_two]
      rw [Fintype.card_perm]
      simp only [Fintype.card_fin]
      ring
    _ = ((r + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1)) *
        vinogradovFundamentalTerm r k P q := rfl

/-- Polynomial-cost version of `manyValues_pairCount_le`, using a fixed
family of primes from the single dyadic block `(q,2q]`. -/
private theorem manyValues_pairCount_le_short {r k P q : ℕ}
    (hr : 0 < r) (hk : 2 ≤ k)
    (hq : vinogradovPrimeThreshold k ≤ q) (hPq : P < q ^ k) :
    vinogradovPairCount k (vinogradovManyValues (r + k) k P)
        (vinogradovManyValues (r + k) k P) ≤
      ((r + k).factorial ^ 2 * vinogradovSeparatingFamilySize k) *
        vinogradovFundamentalTermShort r k P q := by
  classical
  let T := vinogradovSeparatingPrimeFamily k q
  let G := vinogradovManyValues (r + k) k P
  let Sol := ((G ×ˢ G).filter fun xy =>
    vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2)
  let piece (σ τ : Equiv.Perm (Fin (r + k))) (p : ℕ) :=
    ((((vinogradovTuples (r + k) P).filter
        (vinogradovPermutedFirstWell p σ)) ×ˢ
      ((vinogradovTuples (r + k) P).filter
        (vinogradovPermutedFirstWell p τ))).filter
      fun xy => vinogradovMomentVector k xy.1 = vinogradovMomentVector k xy.2)
  have hcover : Sol ⊆
      (Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun σ =>
        (Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun τ =>
          T.biUnion fun p => piece σ τ p := by
    intro xy hxy
    dsimp [Sol, G] at hxy
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    have hxG := Finset.mem_filter.mp hxy.1.1
    have hyG := Finset.mem_filter.mp hxy.1.2
    obtain ⟨σ, hσ⟩ := exists_perm_first_injective xy.1 hxG.2
    obtain ⟨τ, hτ⟩ := exists_perm_first_injective xy.2 hyG.2
    let u : Fin k → ℕ := fun i => xy.1 (σ (vinogradovFirstIndex r i))
    let v : Fin k → ℕ := fun i => xy.2 (τ (vinogradovFirstIndex r i))
    obtain ⟨p, hpT, hp, hkp, hpL, hwu, hwv⟩ := exists_short_separating_prime
      hk hq hPq u v
      (fun i => (mem_vinogradovTuples.mp hxG.1 _).2)
      (fun i => (mem_vinogradovTuples.mp hyG.1 _).2) hσ hτ
    simp only [Finset.mem_biUnion]
    refine ⟨σ, Finset.mem_univ _, τ, Finset.mem_univ _, p, hpT, ?_⟩
    dsimp [piece]
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_filter.mpr ⟨hxG.1, hwu⟩,
      Finset.mem_filter.mpr ⟨hyG.1, hwv⟩⟩, hxy.2⟩
  have hpiece : ∀ σ τ : Equiv.Perm (Fin (r + k)), ∀ p ∈ T,
      (piece σ τ p).card ≤ vinogradovFundamentalTermShort r k P q := by
    intro σ τ p hpT
    let Aσ := (vinogradovTuples (r + k) P).filter
      (vinogradovPermutedFirstWell p σ)
    let Aτ := (vinogradovTuples (r + k) P).filter
      (vinogradovPermutedFirstWell p τ)
    have hspec := vinogradovSeparatingPrimeFamily_spec hq
    have hpS := hspec.1 hpT
    unfold vinogradovShortPrimes at hpS
    rw [Finset.mem_filter, Finset.mem_Ioc] at hpS
    have hp : p.Prime := hpS.2
    have hqp : q < p := hpS.1.1
    have hpL : p ≤ 2 * q := hpS.1.2
    have hkq : k ≤ q := (vinogradovPrimeThreshold_ge_self k).trans hq
    have hPp : P < p ^ k := hPq.trans_le (Nat.pow_le_pow_left hqp.le k)
    have hdiagσ : vinogradovPairCount k Aσ Aσ ≤
        vinogradovFundamentalTermShort r k P q := by
      rw [permutedFirst_pairCount_eq]
      exact firstWell_pairCount_le_fundamentalTermShort hr hk hkq hp hqp hpL hPp
    have hdiagτ : vinogradovPairCount k Aτ Aτ ≤
        vinogradovFundamentalTermShort r k P q := by
      rw [permutedFirst_pairCount_eq]
      exact firstWell_pairCount_le_fundamentalTermShort hr hk hkq hp hqp hpL hPp
    have hsq := vinogradovPairCount_sq_le (k := k) Aσ Aτ
    have hsq' : vinogradovPairCount k Aσ Aτ ^ 2 ≤
        vinogradovFundamentalTermShort r k P q ^ 2 := by
      exact hsq.trans (Nat.mul_le_mul hdiagσ hdiagτ) |>.trans_eq (pow_two _).symm
    change vinogradovPairCount k Aσ Aτ ≤ _
    exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hsq'
  calc
    vinogradovPairCount k G G = Sol.card := rfl
    _ ≤ ((Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun σ =>
        (Finset.univ : Finset (Equiv.Perm (Fin (r + k)))).biUnion fun τ =>
          T.biUnion fun p => piece σ τ p).card := Finset.card_le_card hcover
    _ ≤ ∑ _σ : Equiv.Perm (Fin (r + k)),
        ∑ _τ : Equiv.Perm (Fin (r + k)),
          ∑ _p ∈ T, vinogradovFundamentalTermShort r k P q := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun σ hσ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun τ hτ => ?_)
      exact Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun p hp => hpiece σ τ p hp)
    _ = ((r + k).factorial ^ 2 * T.card) *
        vinogradovFundamentalTermShort r k P q := by
      simp [pow_two]
      rw [Fintype.card_perm]
      simp only [Fintype.card_fin]
      ring
    _ = ((r + k).factorial ^ 2 * vinogradovSeparatingFamilySize k) *
        vinogradovFundamentalTermShort r k P q := by
      rw [(vinogradovSeparatingPrimeFamily_spec hq).2]

/-- Fundamental Linnik--Karatsuba recursion, with all constants explicit.
The second summand is the singular contribution (tuples taking fewer than
`k` distinct values); the first is the nonsingular `p`-adic term. -/
theorem vinogradov_fundamental_lemma {r k P q : ℕ}
    (hr : 0 < r) (hk : 2 ≤ k) (hP : 1 ≤ P)
    (hq : k ≤ q) (hPq : P < q ^ k) :
    vinogradovJ (r + k) k P ≤
      2 * (((r + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1)) *
        vinogradovFundamentalTerm r k P q) +
      2 * (k * (P ^ (k - 1) * k ^ (r + k))) ^ 2 := by
  classical
  let A := vinogradovFewValues (r + k) k P
  let G := vinogradovManyValues (r + k) k P
  let T := vinogradovTuples (r + k) P
  let J := vinogradovJ (r + k) k P
  let H := vinogradovPairCount k G T
  let B := vinogradovPairCount k A T
  let G₀ := ((r + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1)) *
    vinogradovFundamentalTerm r k P q
  let A₀ := k * (P ^ (k - 1) * k ^ (r + k))
  have hsplit : J ≤ H + B := by
    have hcover := vinogradovTuples_eq_few_union_many (r + k) k P
    change vinogradovJ (r + k) k P ≤ H + B
    rw [vinogradovJ_eq_pairCount]
    change vinogradovPairCount k T T ≤ H + B
    calc
      vinogradovPairCount k T T = vinogradovPairCount k (A ∪ G) T := by
        congr 2
      _ ≤ vinogradovPairCount k A T + vinogradovPairCount k G T :=
        vinogradovPairCount_union_le A G T
      _ = H + B := by simp only [H, B, add_comm]
  have hHsq : H ^ 2 ≤ G₀ * J := by
    dsimp [H, G₀, J, G, T]
    calc
      vinogradovPairCount k (vinogradovManyValues (r + k) k P)
          (vinogradovTuples (r + k) P) ^ 2 ≤
        vinogradovPairCount k (vinogradovManyValues (r + k) k P)
            (vinogradovManyValues (r + k) k P) *
          vinogradovPairCount k (vinogradovTuples (r + k) P)
            (vinogradovTuples (r + k) P) :=
        vinogradovPairCount_sq_le _ _
      _ ≤ (((r + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1)) *
          vinogradovFundamentalTerm r k P q) *
          vinogradovPairCount k (vinogradovTuples (r + k) P)
            (vinogradovTuples (r + k) P) :=
        Nat.mul_le_mul_right _ (manyValues_pairCount_le hr hk hq hPq)
      _ = (((r + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1)) *
          vinogradovFundamentalTerm r k P q) *
          vinogradovJ (r + k) k P := by rw [vinogradovJ_eq_pairCount]
  have hAsq : vinogradovPairCount k A A ≤ A₀ ^ 2 := by
    dsimp [A, A₀]
    calc
      vinogradovPairCount k (vinogradovFewValues (r + k) k P)
          (vinogradovFewValues (r + k) k P) ≤
        (vinogradovFewValues (r + k) k P).card ^ 2 := by
          rw [vinogradovPairCount]
          calc
            (((vinogradovFewValues (r + k) k P) ×ˢ
                (vinogradovFewValues (r + k) k P)).filter fun xy =>
                vinogradovMomentVector k xy.1 =
                  vinogradovMomentVector k xy.2).card ≤
              ((vinogradovFewValues (r + k) k P) ×ˢ
                (vinogradovFewValues (r + k) k P)).card :=
              Finset.card_filter_le _ _
            _ = (vinogradovFewValues (r + k) k P).card ^ 2 := by
              simp [pow_two]
      _ ≤ (k * (P ^ (k - 1) * k ^ (r + k))) ^ 2 :=
        Nat.pow_le_pow_left (card_vinogradovFewValues_le hP) 2
  have hBsq : B ^ 2 ≤ A₀ ^ 2 * J := by
    dsimp [B, J, T]
    calc
      vinogradovPairCount k A (vinogradovTuples (r + k) P) ^ 2 ≤
          vinogradovPairCount k A A *
            vinogradovPairCount k (vinogradovTuples (r + k) P)
              (vinogradovTuples (r + k) P) :=
        vinogradovPairCount_sq_le _ _
      _ ≤ A₀ ^ 2 *
          vinogradovPairCount k (vinogradovTuples (r + k) P)
            (vinogradovTuples (r + k) P) := Nat.mul_le_mul_right _ hAsq
      _ = A₀ ^ 2 * vinogradovJ (r + k) k P := by
        rw [vinogradovJ_eq_pairCount]
  by_cases hJ0 : J = 0
  · dsimp [J] at hJ0 ⊢
    omega
  have hsqsum : (H + B) ^ 2 ≤ 2 * (H ^ 2 + B ^ 2) := by
    nlinarith [sq_nonneg (H - B : ℤ)]
  have hJJ : J * J ≤ (2 * (G₀ + A₀ ^ 2)) * J := by
    calc
      J * J = J ^ 2 := by ring
      _ ≤ (H + B) ^ 2 := Nat.pow_le_pow_left hsplit 2
      _ ≤ 2 * (H ^ 2 + B ^ 2) := hsqsum
      _ ≤ 2 * (G₀ * J + A₀ ^ 2 * J) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add hHsq hBsq)
      _ = (2 * (G₀ + A₀ ^ 2)) * J := by ring
  have hfinal := Nat.le_of_mul_le_mul_right hJJ (Nat.pos_of_ne_zero hJ0)
  dsimp [J, G₀, A₀] at hfinal ⊢
  exact hfinal.trans_eq (by ring)

/-- Fundamental Linnik--Karatsuba recursion using a separating family from
one dyadic prime block.  In particular, every prime factor in the
nonsingular term is at most `2q`. -/
theorem vinogradov_fundamental_lemma_short {r k P q : ℕ}
    (hr : 0 < r) (hk : 2 ≤ k) (hP : 1 ≤ P)
    (hq : vinogradovPrimeThreshold k ≤ q) (hPq : P < q ^ k) :
    vinogradovJ (r + k) k P ≤
      2 * (((r + k).factorial ^ 2 * vinogradovSeparatingFamilySize k) *
        vinogradovFundamentalTermShort r k P q) +
      2 * (k * (P ^ (k - 1) * k ^ (r + k))) ^ 2 := by
  classical
  let A := vinogradovFewValues (r + k) k P
  let G := vinogradovManyValues (r + k) k P
  let T := vinogradovTuples (r + k) P
  let J := vinogradovJ (r + k) k P
  let H := vinogradovPairCount k G T
  let B := vinogradovPairCount k A T
  let G₀ := ((r + k).factorial ^ 2 * vinogradovSeparatingFamilySize k) *
    vinogradovFundamentalTermShort r k P q
  let A₀ := k * (P ^ (k - 1) * k ^ (r + k))
  have hsplit : J ≤ H + B := by
    have hcover := vinogradovTuples_eq_few_union_many (r + k) k P
    change vinogradovJ (r + k) k P ≤ H + B
    rw [vinogradovJ_eq_pairCount]
    change vinogradovPairCount k T T ≤ H + B
    calc
      vinogradovPairCount k T T = vinogradovPairCount k (A ∪ G) T := by
        congr 2
      _ ≤ vinogradovPairCount k A T + vinogradovPairCount k G T :=
        vinogradovPairCount_union_le A G T
      _ = H + B := by simp only [H, B, add_comm]
  have hHsq : H ^ 2 ≤ G₀ * J := by
    dsimp [H, G₀, J, G, T]
    calc
      vinogradovPairCount k (vinogradovManyValues (r + k) k P)
          (vinogradovTuples (r + k) P) ^ 2 ≤
        vinogradovPairCount k (vinogradovManyValues (r + k) k P)
            (vinogradovManyValues (r + k) k P) *
          vinogradovPairCount k (vinogradovTuples (r + k) P)
            (vinogradovTuples (r + k) P) :=
        vinogradovPairCount_sq_le _ _
      _ ≤ (((r + k).factorial ^ 2 * vinogradovSeparatingFamilySize k) *
          vinogradovFundamentalTermShort r k P q) *
          vinogradovPairCount k (vinogradovTuples (r + k) P)
            (vinogradovTuples (r + k) P) :=
        Nat.mul_le_mul_right _ (manyValues_pairCount_le_short hr hk hq hPq)
      _ = (((r + k).factorial ^ 2 * vinogradovSeparatingFamilySize k) *
          vinogradovFundamentalTermShort r k P q) *
          vinogradovJ (r + k) k P := by rw [vinogradovJ_eq_pairCount]
  have hAsq : vinogradovPairCount k A A ≤ A₀ ^ 2 := by
    dsimp [A, A₀]
    calc
      vinogradovPairCount k (vinogradovFewValues (r + k) k P)
          (vinogradovFewValues (r + k) k P) ≤
        (vinogradovFewValues (r + k) k P).card ^ 2 := by
          rw [vinogradovPairCount]
          calc
            (((vinogradovFewValues (r + k) k P) ×ˢ
                (vinogradovFewValues (r + k) k P)).filter fun xy =>
                vinogradovMomentVector k xy.1 =
                  vinogradovMomentVector k xy.2).card ≤
              ((vinogradovFewValues (r + k) k P) ×ˢ
                (vinogradovFewValues (r + k) k P)).card :=
              Finset.card_filter_le _ _
            _ = (vinogradovFewValues (r + k) k P).card ^ 2 := by
              simp [pow_two]
      _ ≤ (k * (P ^ (k - 1) * k ^ (r + k))) ^ 2 :=
        Nat.pow_le_pow_left (card_vinogradovFewValues_le hP) 2
  have hBsq : B ^ 2 ≤ A₀ ^ 2 * J := by
    dsimp [B, J, T]
    calc
      vinogradovPairCount k A (vinogradovTuples (r + k) P) ^ 2 ≤
          vinogradovPairCount k A A *
            vinogradovPairCount k (vinogradovTuples (r + k) P)
              (vinogradovTuples (r + k) P) :=
        vinogradovPairCount_sq_le _ _
      _ ≤ A₀ ^ 2 *
          vinogradovPairCount k (vinogradovTuples (r + k) P)
            (vinogradovTuples (r + k) P) := Nat.mul_le_mul_right _ hAsq
      _ = A₀ ^ 2 * vinogradovJ (r + k) k P := by
        rw [vinogradovJ_eq_pairCount]
  by_cases hJ0 : J = 0
  · dsimp [J] at hJ0 ⊢
    omega
  have hsqsum : (H + B) ^ 2 ≤ 2 * (H ^ 2 + B ^ 2) := by
    nlinarith [sq_nonneg (H - B : ℤ)]
  have hJJ : J * J ≤ (2 * (G₀ + A₀ ^ 2)) * J := by
    calc
      J * J = J ^ 2 := by ring
      _ ≤ (H + B) ^ 2 := Nat.pow_le_pow_left hsplit 2
      _ ≤ 2 * (H ^ 2 + B ^ 2) := hsqsum
      _ ≤ 2 * (G₀ * J + A₀ ^ 2 * J) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add hHsq hBsq)
      _ = (2 * (G₀ + A₀ ^ 2)) * J := by ring
  have hfinal := Nat.le_of_mul_le_mul_right hJJ (Nat.pos_of_ne_zero hJ0)
  dsimp [J, G₀, A₀] at hfinal ⊢
  exact hfinal.trans_eq (by ring)

/-! ## Iterating the fundamental lemma -/

private theorem vinogradovRpowProductBound {P q Q E N κ : ℝ}
    (hP : 0 < P) (hq : 0 < q) (hQ0 : 0 ≤ Q)
    (hE : 0 ≤ E) (hgap : 0 ≤ N - E)
    (hQ : Q ≤ 2 * P / q)
    (hqB : q ≤ 2 * P ^ κ⁻¹) :
    q ^ N * Q ^ E ≤
      2 ^ E * 2 ^ (N - E) * P ^ (E + (N - E) * κ⁻¹) := by
  have hq0 : 0 ≤ q := hq.le
  have hP0 : 0 ≤ P := hP.le
  calc
    q ^ N * Q ^ E ≤ q ^ N * (2 * P / q) ^ E := by
      gcongr
    _ = 2 ^ E * P ^ E * q ^ (N - E) := by
      rw [show 2 * P / q = (2 * P) / q by ring,
        Real.div_rpow (by positivity) hq0,
        Real.mul_rpow (by positivity) hP0,
        Real.rpow_sub hq N E]
      field_simp [Real.rpow_pos_of_pos hq]
    _ ≤ 2 ^ E * P ^ E * (2 * P ^ κ⁻¹) ^ (N - E) := by
      gcongr
    _ = 2 ^ E * 2 ^ (N - E) * P ^ (E + (N - E) * κ⁻¹) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hP0 _),
        ← Real.rpow_mul hP0, Real.rpow_add hP E,
        mul_comm κ⁻¹ (N - E)]
      ring

private theorem cast_nthRoot_le_rpow {k P : ℕ} (hk : 0 < k) :
    (Nat.nthRoot k P : ℝ) ≤ (P : ℝ) ^ ((k : ℝ)⁻¹) := by
  rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hk)]
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_nthRoot_le (Or.inl hk.ne')

private theorem vinogradovRootTwoLe {k P : ℕ} (hk : 0 < k)
    (h2 : 2 ^ k ≤ P) :
    (2 : ℝ) ≤ (P : ℝ) ^ ((k : ℝ)⁻¹) := by
  rw [Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity)
    (by exact_mod_cast hk)]
  rw [Real.rpow_natCast]
  exact_mod_cast h2

private theorem vinogradovTwoMulRootLe {k P : ℕ} (hk : 2 ≤ k)
    (h2 : 2 ^ k ≤ P) :
    2 * (P : ℝ) ^ ((k : ℝ)⁻¹) ≤ P := by
  let R := (P : ℝ) ^ ((k : ℝ)⁻¹)
  have hR2 : 2 ≤ R := vinogradovRootTwoLe (by omega) h2
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR2
  have hR1 : 1 ≤ R := le_trans (by norm_num) hR2
  have hpow : R ^ (k : ℝ) = P := by
    dsimp [R]
    rw [Real.rpow_inv_rpow (by positivity)
      (by exact_mod_cast (show k ≠ 0 by omega))]
  calc
    2 * R ≤ R ^ (2 : ℕ) := by
      rw [pow_two]
      nlinarith
    _ = R ^ (2 : ℝ) := (Real.rpow_natCast R 2).symm
    _ ≤ R ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by exact_mod_cast hk)
    _ = P := hpow

private theorem vinogradovQBounds {k P : ℕ} (hk : 2 ≤ k)
    (hkpow : k ^ k ≤ P) (h2pow : 2 ^ k ≤ P) :
    let q := max k (Nat.nthRoot k P + 1)
    P < q ^ k ∧ k ≤ q ∧
      (q : ℝ) ≤ 2 * (P : ℝ) ^ ((k : ℝ)⁻¹) ∧ q ≤ P := by
  let q := max k (Nat.nthRoot k P + 1)
  have hroot : k ≤ Nat.nthRoot k P :=
    (Nat.le_nthRoot_iff (by omega)).2 hkpow
  have hqeq : q = Nat.nthRoot k P + 1 := by
    dsimp [q]
    rw [max_eq_right]
    omega
  have hrootR := cast_nthRoot_le_rpow (P := P) (by omega : 0 < k)
  have hR1 : (1 : ℝ) ≤ (P : ℝ) ^ ((k : ℝ)⁻¹) := by
    apply Real.one_le_rpow
    · exact_mod_cast (le_trans (Nat.one_le_pow k 2 (by norm_num)) h2pow)
    · positivity
  have hqR : (q : ℝ) ≤ 2 * (P : ℝ) ^ ((k : ℝ)⁻¹) := by
    rw [hqeq, Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨?_, ?_, hqR, ?_⟩
  · change P < q ^ k
    rw [hqeq]
    exact Nat.lt_pow_nthRoot_add_one (by omega) P
  · exact le_max_left _ _
  · exact_mod_cast hqR.trans (vinogradovTwoMulRootLe hk h2pow)

private theorem vinogradovCastDivAddOneLe {P q : ℕ} (hq : 0 < q)
    (hqp : q ≤ P) :
    ((P / q + 1 : ℕ) : ℝ) ≤ 2 * (P : ℝ) / q := by
  have hone : (1 : ℝ) ≤ (P : ℝ) / q := by
    rw [le_div_iff₀ (by exact_mod_cast hq)]
    simpa using (show (q : ℝ) ≤ P by exact_mod_cast hqp)
  calc
    ((P / q + 1 : ℕ) : ℝ) = ((P / q : ℕ) : ℝ) + 1 := by norm_cast
    _ ≤ (P : ℝ) / q + 1 := by
      have := Nat.cast_div_le (α := ℝ) (m := P) (n := q)
      linarith
    _ ≤ 2 * ((P : ℝ) / q) := by linarith
    _ = 2 * (P : ℝ) / q := by ring

/-- The decaying excess in the weak Vinogradov mean-value exponent. -/
noncomputable def vinogradovDelta (k τ : ℕ) : ℝ :=
  (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ τ

/-- The exponent produced after `τ` rounds of the `p`-adic iteration. -/
noncomputable def vinogradovExponent (k τ : ℕ) : ℝ :=
  2 * (k : ℝ) * τ - (k : ℝ) * (k + 1) / 2 + vinogradovDelta k τ

private theorem cast_vinogradovUpperTri (k : ℕ) :
    ((k * (k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) * (k + 1) / 2 := by
  rw [Nat.cast_div (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))
    (by norm_num)]
  norm_num

private theorem cast_vinogradovLowerTri {k : ℕ} (hk : 1 ≤ k) :
    ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * (k - 1) / 2 := by
  rw [Nat.cast_div (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    (by norm_num), Nat.cast_mul, Nat.cast_sub hk]
  norm_num

private theorem vinogradovDelta_succ (k τ : ℕ) :
    vinogradovDelta k (τ + 1) =
      vinogradovDelta k τ * (1 - 1 / (k : ℝ)) := by
  simp only [vinogradovDelta, pow_succ]
  ring

private theorem vinogradovExponent_one {k : ℕ} (hk : 2 ≤ k) :
    vinogradovExponent k 1 = k := by
  simp only [vinogradovExponent, vinogradovDelta, Nat.cast_one, mul_one, pow_one]
  field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (show k ≠ 0 by omega)]
  ring

private theorem vinogradovExponent_succ {k τ : ℕ} (hk : 2 ≤ k) :
    vinogradovExponent k (τ + 1) =
      vinogradovExponent k τ + 2 * k - vinogradovDelta k τ / k := by
  rw [vinogradovExponent, vinogradovExponent, vinogradovDelta_succ]
  push_cast
  field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (show k ≠ 0 by omega)]
  ring

private theorem vinogradovDelta_le_half_sq {k τ : ℕ} (hk : 2 ≤ k) :
    vinogradovDelta k τ ≤ (k : ℝ) ^ 2 / 2 := by
  apply mul_le_of_le_one_right (by positivity)
  apply pow_le_one₀
  · field_simp
    nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk]
  · field_simp
    nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk]

private theorem vinogradovExponent_nonneg {k τ : ℕ} (hk : 2 ≤ k)
    (hτ : 1 ≤ τ) : 0 ≤ vinogradovExponent k τ := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hτR : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbase : (0 : ℝ) ≤ 1 - 1 / k := by
    field_simp
    nlinarith
  have hδ : 0 ≤ vinogradovDelta k τ := by
    dsimp [vinogradovDelta]
    exact mul_nonneg (by positivity) (pow_nonneg hbase _)
  have hbern : (1 : ℝ) - τ / k ≤ (1 - 1 / k) ^ τ := by
    have h := one_add_mul_le_pow (a := -(1 / (k : ℝ))) (n := τ) (by
      field_simp
      nlinarith)
    convert h using 1
    · ring
  have hδlower : (k : ℝ) ^ 2 / 2 * (1 - τ / k) ≤
      vinogradovDelta k τ := by
    dsimp [vinogradovDelta]
    exact mul_le_mul_of_nonneg_left hbern (by positivity)
  simp only [vinogradovExponent, vinogradovDelta]
  dsimp [vinogradovDelta] at hδ hδlower
  field_simp at hδlower ⊢
  nlinarith [mul_nonneg hk0.le (zero_le_one.trans hτR)]

private theorem vinogradovGapIdentity {k τ : ℕ} (hk : 2 ≤ k) :
    ((2 * (k * τ) + k * (k - 1) / 2 : ℕ) : ℝ) -
        vinogradovExponent k τ =
      (k : ℝ) ^ 2 - vinogradovDelta k τ := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  norm_num
  rw [cast_vinogradovLowerTri (show 1 ≤ k by omega)]
  simp only [vinogradovExponent]
  ring

private theorem vinogradovGapNonneg {k τ : ℕ} (hk : 2 ≤ k) :
    0 ≤ ((2 * (k * τ) + k * (k - 1) / 2 : ℕ) : ℝ) -
      vinogradovExponent k τ := by
  rw [vinogradovGapIdentity hk]
  have hδ := vinogradovDelta_le_half_sq (τ := τ) hk
  nlinarith [sq_nonneg (k : ℝ)]

private theorem vinogradovSuccessorExponentIdentity {k τ : ℕ}
    (hk : 2 ≤ k) :
    (k : ℝ) + vinogradovExponent k τ +
        ((((2 * (k * τ) + k * (k - 1) / 2 : ℕ) : ℝ) -
            vinogradovExponent k τ) * (k : ℝ)⁻¹) =
      vinogradovExponent k (τ + 1) := by
  rw [vinogradovGapIdentity hk, vinogradovExponent_succ hk]
  field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (show k ≠ 0 by omega)]
  ring

private theorem vinogradovScaledRpowProductBound
    {A P q Q J C E N κ : ℝ} {d : ℕ}
    (hA : 0 ≤ A) (hP : 0 < P) (hq : 0 < q) (hQ0 : 0 ≤ Q)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hgap : 0 ≤ N - E)
    (hQ : Q ≤ 2 * P / q) (hqB : q ≤ 2 * P ^ κ⁻¹)
    (hJ : J ≤ C * Q ^ E) :
    A * P ^ d * q ^ N * J ≤
      A * C * (2 ^ E * 2 ^ (N - E)) *
        P ^ ((d : ℝ) + E + (N - E) * κ⁻¹) := by
  have hprod := vinogradovRpowProductBound hP hq hQ0 hE hgap hQ hqB
  calc
    A * P ^ d * q ^ N * J ≤ A * P ^ d * q ^ N * (C * Q ^ E) := by
      gcongr
    _ = A * C * P ^ d * (q ^ N * Q ^ E) := by ring
    _ ≤ A * C * P ^ d *
        (2 ^ E * 2 ^ (N - E) * P ^ (E + (N - E) * κ⁻¹)) := by
      gcongr
    _ = A * C * (2 ^ E * 2 ^ (N - E)) *
        P ^ ((d : ℝ) + E + (N - E) * κ⁻¹) := by
      rw [show P ^ d = P ^ (d : ℝ) by rw [Real.rpow_natCast],
        show (d : ℝ) + E + (N - E) * κ⁻¹ =
          (d : ℝ) + (E + (N - E) * κ⁻¹) by ring,
        Real.rpow_add hP (d : ℝ) (E + (N - E) * κ⁻¹)]
      ring

private theorem cast_vinogradovFundamentalTerm (r k P q : ℕ) :
    (vinogradovFundamentalTerm r k P q : ℝ) =
      (((2 * r) * k.factorial *
          (2 ^ ((2 * k.choose 2) * k + 1)) ^
            (2 * r + k * (k - 1) / 2) : ℕ) : ℝ) *
        (P : ℝ) ^ k * (q : ℝ) ^ (2 * r + k * (k - 1) / 2) *
          (vinogradovJ r k (P / q + 1) : ℝ) := by
  norm_cast
  simp only [vinogradovFundamentalTerm]
  rw [mul_pow]
  conv_rhs =>
    rw [pow_add, pow_add]
  ring

private theorem vinogradovFundamentalTerm_le_power {k τ P q : ℕ} {C : ℝ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hP : 1 ≤ P)
    (hqk : k ≤ q) (hqp : q ≤ P)
    (hqR : (q : ℝ) ≤ 2 * (P : ℝ) ^ ((k : ℝ)⁻¹))
    (hC : 0 ≤ C)
    (hbound : ∀ Q : ℕ, 1 ≤ Q →
      (vinogradovJ (k * τ) k Q : ℝ) ≤
        C * (Q : ℝ) ^ vinogradovExponent k τ) :
    (vinogradovFundamentalTerm (k * τ) k P q : ℝ) ≤
      ((((2 * (k * τ)) * k.factorial *
          (2 ^ ((2 * k.choose 2) * k + 1)) ^
            (2 * (k * τ) + k * (k - 1) / 2) : ℕ) : ℝ) * C *
        (2 ^ vinogradovExponent k τ *
          2 ^ (((2 * (k * τ) + k * (k - 1) / 2 : ℕ) : ℝ) -
            vinogradovExponent k τ))) *
        (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
  let Q := P / q + 1
  let N := 2 * (k * τ) + k * (k - 1) / 2
  let A := (2 * (k * τ)) * k.factorial *
    (2 ^ ((2 * k.choose 2) * k + 1)) ^ N
  have hk0 : 0 < k := by omega
  have hq0 : 0 < q := lt_of_lt_of_le hk0 hqk
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ1 : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hJR := hbound Q hQ1
  have hscaled := vinogradovScaledRpowProductBound
    (A := (A : ℝ)) (P := (P : ℝ)) (q := (q : ℝ)) (Q := (Q : ℝ))
    (J := (vinogradovJ (k * τ) k Q : ℝ)) (C := C)
    (E := vinogradovExponent k τ) (N := (N : ℝ)) (κ := (k : ℝ))
    (d := k) (by positivity) hP0 (by exact_mod_cast hq0) (by positivity)
    hC (vinogradovExponent_nonneg hk hτ) (by
      dsimp [N]
      exact vinogradovGapNonneg hk)
    (by
      dsimp [Q]
      exact vinogradovCastDivAddOneLe hq0 hqp)
    hqR hJR
  rw [cast_vinogradovFundamentalTerm]
  change (A : ℝ) * (P : ℝ) ^ k * (q : ℝ) ^ N *
      (vinogradovJ (k * τ) k Q : ℝ) ≤ _
  rw [show (q : ℝ) ^ N = (q : ℝ) ^ (N : ℝ) by
    rw [Real.rpow_natCast]]
  calc
    (A : ℝ) * (P : ℝ) ^ k * (q : ℝ) ^ (N : ℝ) *
        (vinogradovJ (k * τ) k Q : ℝ) ≤
      (A : ℝ) * C *
          (2 ^ vinogradovExponent k τ *
            2 ^ ((N : ℝ) - vinogradovExponent k τ)) *
        (P : ℝ) ^ ((k : ℝ) + vinogradovExponent k τ +
          ((N : ℝ) - vinogradovExponent k τ) * (k : ℝ)⁻¹) := hscaled
    _ = _ := by
      dsimp [A, N]
      rw [vinogradovSuccessorExponentIdentity hk]

private theorem cast_vinogradovFundamentalTermShort (r k P q : ℕ) :
    (vinogradovFundamentalTermShort r k P q : ℝ) =
      (((2 * r) * k.factorial *
          2 ^ (2 * r + k * (k - 1) / 2) : ℕ) : ℝ) *
        (P : ℝ) ^ k * (q : ℝ) ^ (2 * r + k * (k - 1) / 2) *
          (vinogradovJ r k (P / q + 1) : ℝ) := by
  norm_cast
  simp only [vinogradovFundamentalTermShort]
  rw [mul_pow]
  conv_rhs =>
    rw [pow_add, pow_add]
  ring

private theorem vinogradovFundamentalTermShort_le_power {k τ P q : ℕ} {C : ℝ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hP : 1 ≤ P)
    (hqk : k ≤ q) (hqp : q ≤ P)
    (hqR : (q : ℝ) ≤ 2 * (P : ℝ) ^ ((k : ℝ)⁻¹))
    (hC : 0 ≤ C)
    (hbound : ∀ Q : ℕ, 1 ≤ Q →
      (vinogradovJ (k * τ) k Q : ℝ) ≤
        C * (Q : ℝ) ^ vinogradovExponent k τ) :
    (vinogradovFundamentalTermShort (k * τ) k P q : ℝ) ≤
      ((((2 * (k * τ)) * k.factorial *
          2 ^ (2 * (k * τ) + k * (k - 1) / 2) : ℕ) : ℝ) * C *
        (2 ^ vinogradovExponent k τ *
          2 ^ (((2 * (k * τ) + k * (k - 1) / 2 : ℕ) : ℝ) -
            vinogradovExponent k τ))) *
        (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
  let Q := P / q + 1
  let N := 2 * (k * τ) + k * (k - 1) / 2
  let A := (2 * (k * τ)) * k.factorial * 2 ^ N
  have hk0 : 0 < k := by omega
  have hq0 : 0 < q := lt_of_lt_of_le hk0 hqk
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ1 : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hJR := hbound Q hQ1
  have hscaled := vinogradovScaledRpowProductBound
    (A := (A : ℝ)) (P := (P : ℝ)) (q := (q : ℝ)) (Q := (Q : ℝ))
    (J := (vinogradovJ (k * τ) k Q : ℝ)) (C := C)
    (E := vinogradovExponent k τ) (N := (N : ℝ)) (κ := (k : ℝ))
    (d := k) (by positivity) hP0 (by exact_mod_cast hq0) (by positivity)
    hC (vinogradovExponent_nonneg hk hτ) (by
      dsimp [N]
      exact vinogradovGapNonneg hk)
    (by
      dsimp [Q]
      exact vinogradovCastDivAddOneLe hq0 hqp)
    hqR hJR
  rw [cast_vinogradovFundamentalTermShort]
  change (A : ℝ) * (P : ℝ) ^ k * (q : ℝ) ^ N *
      (vinogradovJ (k * τ) k Q : ℝ) ≤ _
  rw [show (q : ℝ) ^ N = (q : ℝ) ^ (N : ℝ) by
    rw [Real.rpow_natCast]]
  calc
    (A : ℝ) * (P : ℝ) ^ k * (q : ℝ) ^ (N : ℝ) *
        (vinogradovJ (k * τ) k Q : ℝ) ≤
      (A : ℝ) * C *
          (2 ^ vinogradovExponent k τ *
            2 ^ ((N : ℝ) - vinogradovExponent k τ)) *
        (P : ℝ) ^ ((k : ℝ) + vinogradovExponent k τ +
          ((N : ℝ) - vinogradovExponent k τ) * (k : ℝ)⁻¹) := hscaled
    _ = _ := by
      dsimp [A, N]
      rw [vinogradovSuccessorExponentIdentity hk]

private theorem vinogradovSingularExponentLe {k τ : ℕ} (hk : 2 ≤ k)
    (hτ : 1 ≤ τ) :
    ((2 * (k - 1) : ℕ) : ℝ) ≤ vinogradovExponent k (τ + 1) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hτR : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbern : (1 : ℝ) - (τ + 1) / k ≤
      (1 - 1 / k) ^ (τ + 1) := by
    have h := one_add_mul_le_pow (a := -(1 / (k : ℝ))) (n := τ + 1) (by
      field_simp
      nlinarith)
    convert h using 1
    · push_cast
      ring
  have hδlower : (k : ℝ) ^ 2 / 2 * (1 - (τ + 1) / k) ≤
      vinogradovDelta k (τ + 1) := by
    dsimp [vinogradovDelta]
    exact mul_le_mul_of_nonneg_left hbern (by positivity)
  rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ k by omega)]
  norm_num
  simp only [vinogradovExponent, vinogradovDelta]
  dsimp [vinogradovDelta] at hδlower
  push_cast at hδlower ⊢
  field_simp at hδlower ⊢
  nlinarith [mul_nonneg hk0.le (zero_le_one.trans hτR)]

private theorem vinogradovSingularTerm_le_power {k τ P : ℕ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hP : 1 ≤ P) :
    ((2 * (k * (P ^ (k - 1) * k ^ (k * τ + k))) ^ 2 : ℕ) : ℝ) ≤
      ((2 * (k * k ^ (k * τ + k)) ^ 2 : ℕ) : ℝ) *
        (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hpow := Real.rpow_le_rpow_of_exponent_le hP1
    (vinogradovSingularExponentLe hk hτ)
  rw [Real.rpow_natCast] at hpow
  have heq :
      2 * (k * (P ^ (k - 1) * k ^ (k * τ + k))) ^ 2 =
        (2 * (k * k ^ (k * τ + k)) ^ 2) * P ^ (2 * (k - 1)) := by
    simp only [mul_pow]
    rw [show (P ^ (k - 1)) ^ 2 = P ^ (2 * (k - 1)) by
      rw [← pow_mul]
      congr 1
      omega]
    ring
  have hpow' : ((P ^ (2 * (k - 1)) : ℕ) : ℝ) ≤
      (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
    simpa using hpow
  calc
    ((2 * (k * (P ^ (k - 1) * k ^ (k * τ + k))) ^ 2 : ℕ) : ℝ) =
      ((2 * (k * k ^ (k * τ + k)) ^ 2 : ℕ) : ℝ) *
          ((P ^ (2 * (k - 1)) : ℕ) : ℝ) := by exact_mod_cast heq
    _ ≤ ((2 * (k * k ^ (k * τ + k)) ^ 2 : ℕ) : ℝ) *
        (P : ℝ) ^ vinogradovExponent k (τ + 1) :=
      mul_le_mul_of_nonneg_left hpow' (by positivity)

private theorem vinogradovTwoRpowProduct (E : ℝ) (N : ℕ) :
    (2 : ℝ) ^ E * 2 ^ ((N : ℝ) - E) = 2 ^ N := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- One explicit constant update in the polynomial-cost mean-value
iteration. -/
private noncomputable def vinogradovMeanValueStepConstant
    (k τ : ℕ) (C : ℝ) : ℝ :=
  let N := 2 * (k * τ) + k * (k - 1) / 2
  let A := (2 * (k * τ)) * k.factorial * 2 ^ N
  let B : ℝ := (A : ℝ) * C * (2 : ℝ) ^ N
  let F := ((k * τ + k).factorial ^ 2 * vinogradovSeparatingFamilySize k)
  let D : ℕ := 2 * (k * k ^ (k * τ + k)) ^ 2
  let T := vinogradovPrimeThreshold k ^ k
  2 * (F : ℝ) * B + (D : ℝ) +
    (T : ℝ) ^ (2 * (k * (τ + 1))) + 1

/-- The constant obtained by starting at `k!+1` and performing exactly `n`
explicit Linnik--Karatsuba updates. -/
private noncomputable def vinogradovMeanValueConstantAux
    (k : ℕ) : ℕ → ℝ
  | 0 => (k.factorial : ℝ) + 1
  | n + 1 => vinogradovMeanValueStepConstant k (n + 1)
      (vinogradovMeanValueConstantAux k n)

private theorem vinogradovMeanValueConstantAux_pos (k n : ℕ) :
    0 < vinogradovMeanValueConstantAux k n := by
  induction n with
  | zero =>
      rw [vinogradovMeanValueConstantAux]
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast Nat.factorial_pos k) (by norm_num)
  | succ n ih =>
      rw [vinogradovMeanValueConstantAux]
      unfold vinogradovMeanValueStepConstant
      positivity

private theorem vinogradovMeanValuePowerBoundExplicit (k : ℕ) (hk : 2 ≤ k) :
    ∀ n P : ℕ, 1 ≤ P →
      (vinogradovJ (k * (n + 1)) k P : ℝ) ≤
        vinogradovMeanValueConstantAux k n *
          (P : ℝ) ^ vinogradovExponent k (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro P hP
      have hdiag := vinogradovJ_diagonal k P
      calc
        (vinogradovJ (k * (0 + 1)) k P : ℝ) =
            (vinogradovJ k k P : ℝ) := by simp
        _ ≤ (k.factorial : ℝ) * (P : ℝ) ^ k := by exact_mod_cast hdiag
        _ ≤ ((k.factorial : ℝ) + 1) * (P : ℝ) ^ k := by
          gcongr
          norm_num
        _ = vinogradovMeanValueConstantAux k 0 *
            (P : ℝ) ^ vinogradovExponent k (0 + 1) := by
          rw [vinogradovExponent_one hk, Real.rpow_natCast]
          rfl
  | succ n ih =>
      intro P hP
      let τ := n + 1
      let C := vinogradovMeanValueConstantAux k n
      let T := vinogradovPrimeThreshold k ^ k
      let N := 2 * (k * τ) + k * (k - 1) / 2
      let A := (2 * (k * τ)) * k.factorial * 2 ^ N
      let B : ℝ := (A : ℝ) * C * (2 : ℝ) ^ N
      let F := ((k * τ + k).factorial ^ 2 * vinogradovSeparatingFamilySize k)
      let D := 2 * (k * k ^ (k * τ + k)) ^ 2
      let CL : ℝ := 2 * (F : ℝ) * B + D
      let CS : ℝ := (T : ℝ) ^ (2 * (k * (τ + 1)) : ℕ)
      have hC : 0 < C := vinogradovMeanValueConstantAux_pos k n
      have hCL : 0 ≤ CL := by
        dsimp [CL, B, A, D, F, C]
        positivity
      have hCS : 0 ≤ CS := by
        dsimp [CS]
        positivity
      have hbound : ∀ Q : ℕ, 1 ≤ Q →
          (vinogradovJ (k * τ) k Q : ℝ) ≤
            C * (Q : ℝ) ^ vinogradovExponent k τ := by
        simpa only [τ, C] using ih
      have hPE : (1 : ℝ) ≤ (P : ℝ) ^ vinogradovExponent k (τ + 1) :=
        Real.one_le_rpow (by exact_mod_cast hP)
          (vinogradovExponent_nonneg hk (by omega))
      by_cases hlarge : T ≤ P
      · have hkT : k ≤ vinogradovPrimeThreshold k :=
          vinogradovPrimeThreshold_ge_self k
        have h2T : 2 ≤ vinogradovPrimeThreshold k := by
          exact (show 2 ≤ 2 ^ 28 by norm_num).trans
            (vinogradovPrimeThreshold_ge_twoPow k)
        have hkpow : k ^ k ≤ P :=
          (Nat.pow_le_pow_left hkT k).trans hlarge
        have h2pow : 2 ^ k ≤ P :=
          (Nat.pow_le_pow_left h2T k).trans hlarge
        let q := max k (Nat.nthRoot k P + 1)
        obtain ⟨hPq, hkq, hqR, hqP⟩ := vinogradovQBounds hk hkpow h2pow
        have hthresholdRoot : vinogradovPrimeThreshold k ≤ Nat.nthRoot k P := by
          rw [Nat.le_nthRoot_iff (show k ≠ 0 by omega)]
          exact hlarge
        have hthresholdQ : vinogradovPrimeThreshold k ≤ q := by
          exact hthresholdRoot.trans (Nat.le_add_right _ _ |>.trans (le_max_right _ _))
        have hfund := vinogradov_fundamental_lemma_short
          (r := k * τ) (q := q) (by positivity) hk hP hthresholdQ hPq
        have hterm := vinogradovFundamentalTermShort_le_power hk (by omega)
          hP hkq hqP hqR hC.le hbound
        rw [vinogradovTwoRpowProduct] at hterm
        have hterm' : (vinogradovFundamentalTermShort (k * τ) k P q : ℝ) ≤
            B * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
          simpa [B, A, N] using hterm
        have hsing := vinogradovSingularTerm_le_power hk (show 1 ≤ τ by omega) hP
        have hsing' :
            2 * ((k : ℝ) * ((P : ℝ) ^ (k - 1) *
                (k : ℝ) ^ (k * τ + k))) ^ 2 ≤
              (D : ℝ) * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
          simpa [D] using hsing
        have hmain : (vinogradovJ (k * (τ + 1)) k P : ℝ) ≤
            CL * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
          calc
            (vinogradovJ (k * (τ + 1)) k P : ℝ) =
                (vinogradovJ (k * τ + k) k P : ℝ) := by
              congr 1
            _ ≤ (2 * (F * vinogradovFundamentalTermShort (k * τ) k P q) +
                2 * (k * (P ^ (k - 1) * k ^ (k * τ + k))) ^ 2 : ℕ) := by
              exact_mod_cast hfund
            _ ≤ 2 * (F : ℝ) *
                  (B * (P : ℝ) ^ vinogradovExponent k (τ + 1)) +
                (D : ℝ) * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
              have hterm'' : 2 * (F : ℝ) *
                    (vinogradovFundamentalTermShort (k * τ) k P q : ℝ) ≤
                  2 * (F : ℝ) *
                    (B * (P : ℝ) ^ vinogradovExponent k (τ + 1)) :=
                mul_le_mul_of_nonneg_left hterm'
                  (mul_nonneg (by norm_num) (Nat.cast_nonneg F))
              have hsing'' :
                  2 * ((k : ℝ) * ((P : ℝ) ^ (k - 1) *
                      (k : ℝ) ^ (k * τ + k))) ^ 2 ≤
                    2 * ((k : ℝ) * (k : ℝ) ^ (k * τ + k)) ^ 2 *
                      (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
                simpa [D] using hsing'
              dsimp only [D]
              push_cast
              simpa only [mul_assoc] using add_le_add hterm'' hsing''
            _ = CL * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
              dsimp [CL]
              ring
        calc
          (vinogradovJ (k * (n + 1 + 1)) k P : ℝ) =
              (vinogradovJ (k * (τ + 1)) k P : ℝ) := by rfl
          _ ≤ CL * (P : ℝ) ^ vinogradovExponent k (τ + 1) := hmain
          _ ≤ vinogradovMeanValueConstantAux k (n + 1) *
              (P : ℝ) ^ vinogradovExponent k (n + 1 + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hconst : vinogradovMeanValueConstantAux k (n + 1) =
                CL + CS + 1 := by
              rw [vinogradovMeanValueConstantAux]
              rfl
            rw [hconst]
            linarith
      · have hPT : P ≤ T := by omega
        have htriv := vinogradovJ_le_trivial (k * (τ + 1)) k P
        have hpowPT : P ^ (2 * (k * (τ + 1))) ≤
            T ^ (2 * (k * (τ + 1))) := Nat.pow_le_pow_left hPT _
        have hsmall : (vinogradovJ (k * (τ + 1)) k P : ℝ) ≤ CS := by
          dsimp [CS]
          exact_mod_cast htriv.trans hpowPT
        calc
          (vinogradovJ (k * (n + 1 + 1)) k P : ℝ) =
              (vinogradovJ (k * (τ + 1)) k P : ℝ) := by rfl
          _ ≤ CS := hsmall
          _ ≤ CS * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
            nlinarith
          _ ≤ vinogradovMeanValueConstantAux k (n + 1) *
              (P : ℝ) ^ vinogradovExponent k (n + 1 + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hconst : vinogradovMeanValueConstantAux k (n + 1) =
                CL + CS + 1 := by
              rw [vinogradovMeanValueConstantAux]
              rfl
            rw [hconst]
            linarith

private theorem vinogradovMeanValuePowerBound (k : ℕ) (hk : 2 ≤ k)
    (τ : ℕ) (hτ : 1 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 1 ≤ P →
      (vinogradovJ (k * τ) k P : ℝ) ≤
        C * (P : ℝ) ^ vinogradovExponent k τ := by
  induction τ, hτ using Nat.le_induction with
  | base =>
      refine ⟨(k.factorial : ℝ) + 1, by positivity, ?_⟩
      intro P hP
      have hdiag := vinogradovJ_diagonal k P
      calc
        (vinogradovJ (k * 1) k P : ℝ) = (vinogradovJ k k P : ℝ) := by simp
        _ ≤ (k.factorial : ℝ) * (P : ℝ) ^ k := by exact_mod_cast hdiag
        _ ≤ ((k.factorial : ℝ) + 1) * (P : ℝ) ^ k := by
          gcongr
          norm_num
        _ = ((k.factorial : ℝ) + 1) *
            (P : ℝ) ^ vinogradovExponent k 1 := by
          rw [vinogradovExponent_one hk, Real.rpow_natCast]
  | succ τ hτ ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let T := k ^ k + 2 ^ k
      let N := 2 * (k * τ) + k * (k - 1) / 2
      let A := (2 * (k * τ)) * k.factorial *
        (2 ^ ((2 * k.choose 2) * k + 1)) ^ N
      let B : ℝ := (A : ℝ) * C *
        (2 ^ vinogradovExponent k τ *
          2 ^ ((N : ℝ) - vinogradovExponent k τ))
      let F := ((k * τ + k).factorial ^ 2 * ((2 * k.choose 2) * k + 1))
      let D := 2 * (k * k ^ (k * τ + k)) ^ 2
      let CL : ℝ := 2 * (F : ℝ) * B + D
      let CS : ℝ := (T : ℝ) ^ (2 * (k * (τ + 1)) : ℕ)
      let C' := CL + CS + 1
      have hA : 0 < A := by
        dsimp [A, N]
        positivity
      have hB : 0 < B := by
        dsimp [B]
        positivity
      have hCL : 0 ≤ CL := by
        dsimp [CL]
        positivity
      have hCS : 0 ≤ CS := by
        dsimp [CS]
        positivity
      refine ⟨C', by dsimp [C']; positivity, ?_⟩
      intro P hP
      have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
      have hPE : (1 : ℝ) ≤ (P : ℝ) ^ vinogradovExponent k (τ + 1) :=
        Real.one_le_rpow (by exact_mod_cast hP)
          (vinogradovExponent_nonneg hk (by omega))
      by_cases hlarge : T ≤ P
      · have hkpow : k ^ k ≤ P := by
          exact (Nat.le_add_right (k ^ k) (2 ^ k)).trans hlarge
        have h2pow : 2 ^ k ≤ P := by
          exact (Nat.le_add_left (2 ^ k) (k ^ k)).trans hlarge
        let q := max k (Nat.nthRoot k P + 1)
        obtain ⟨hPq, hkq, hqR, hqP⟩ := vinogradovQBounds hk hkpow h2pow
        have hfund := vinogradov_fundamental_lemma
          (r := k * τ) (q := q) (by positivity) hk hP hkq hPq
        have hterm := vinogradovFundamentalTerm_le_power hk hτ hP hkq hqP hqR
          hC.le hbound
        have hterm' : (vinogradovFundamentalTerm (k * τ) k P q : ℝ) ≤
            B * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
          simpa [B, A, N] using hterm
        have hsing := vinogradovSingularTerm_le_power hk hτ hP
        have hsing' :
            2 * ((k : ℝ) * ((P : ℝ) ^ (k - 1) *
                (k : ℝ) ^ (k * τ + k))) ^ 2 ≤
              (D : ℝ) * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
          simpa [D] using hsing
        have hmain : (vinogradovJ (k * (τ + 1)) k P : ℝ) ≤
            CL * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
          calc
            (vinogradovJ (k * (τ + 1)) k P : ℝ) =
                (vinogradovJ (k * τ + k) k P : ℝ) := by
              congr 1
            _ ≤ (2 * (F * vinogradovFundamentalTerm (k * τ) k P q) +
                2 * (k * (P ^ (k - 1) * k ^ (k * τ + k))) ^ 2 : ℕ) := by
              exact_mod_cast hfund
            _ ≤ 2 * (F : ℝ) *
                  (B * (P : ℝ) ^ vinogradovExponent k (τ + 1)) +
                ((D : ℕ) : ℝ) *
                  (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
              have hterm'' : 2 * (F : ℝ) *
                    (vinogradovFundamentalTerm (k * τ) k P q : ℝ) ≤
                  2 * (F : ℝ) *
                    (B * (P : ℝ) ^ vinogradovExponent k (τ + 1)) :=
                mul_le_mul_of_nonneg_left hterm'
                  (mul_nonneg (by norm_num) (Nat.cast_nonneg F))
              have hsing'' :
                  2 * ((k : ℝ) * ((P : ℝ) ^ (k - 1) *
                      (k : ℝ) ^ (k * τ + k))) ^ 2 ≤
                    2 * ((k : ℝ) * (k : ℝ) ^ (k * τ + k)) ^ 2 *
                      (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
                simpa [D] using hsing'
              dsimp only [D]
              push_cast
              simpa only [mul_assoc] using add_le_add hterm'' hsing''
            _ = CL * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
              dsimp [CL]
              ring
        calc
          (vinogradovJ (k * (τ + 1)) k P : ℝ) ≤
              CL * (P : ℝ) ^ vinogradovExponent k (τ + 1) := hmain
          _ ≤ C' * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            dsimp [C']
            linarith

      · have hPT : P ≤ T := by omega
        have htriv := vinogradovJ_le_trivial (k * (τ + 1)) k P
        have hpowPT : P ^ (2 * (k * (τ + 1))) ≤
            T ^ (2 * (k * (τ + 1))) := Nat.pow_le_pow_left hPT _
        have hsmall : (vinogradovJ (k * (τ + 1)) k P : ℝ) ≤ CS := by
          dsimp [CS]
          exact_mod_cast htriv.trans hpowPT
        calc
          (vinogradovJ (k * (τ + 1)) k P : ℝ) ≤ CS := hsmall
          _ ≤ CS * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
            nlinarith
          _ ≤ C' * (P : ℝ) ^ vinogradovExponent k (τ + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            dsimp [C']
            linarith

/-- Polynomial base used by the closed constant envelope. -/
def vinogradovMeanValueEnvelopeBase (k τ : ℕ) : ℕ :=
  2 ^ 32 * (k + τ + 1) ^ 16

/-- A closed envelope for the constant produced by the explicit recursion. -/
noncomputable def vinogradovMeanValueEnvelope (k τ : ℕ) : ℝ :=
  (vinogradovMeanValueEnvelopeBase k τ : ℝ) ^
    (128 * k * τ * (k + τ + 1))

private theorem vinogradovSeparatingFamilySize_le_pow_four {k m : ℕ}
    (hk : k ≤ m) (hm : 3 ≤ m) :
    vinogradovSeparatingFamilySize k ≤ m ^ 4 := by
  have hchoose : k.choose 2 ≤ k ^ 2 := Nat.choose_le_pow k 2
  have hkpow : k ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hk 3
  have hmpos : 0 < m ^ 3 := by positivity
  calc
    vinogradovSeparatingFamilySize k ≤ 2 * k ^ 3 + 1 := by
      dsimp [vinogradovSeparatingFamilySize]
      calc
        2 * k.choose 2 * k + 1 ≤ 2 * k ^ 2 * k + 1 := by gcongr
        _ = 2 * k ^ 3 + 1 := by ring
    _ ≤ 2 * m ^ 3 + m ^ 3 :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 hkpow) hmpos
    _ = 3 * m ^ 3 := by ring
    _ ≤ m ^ 4 := by
      rw [show m ^ 4 = m * m ^ 3 by ring]
      exact Nat.mul_le_mul_right (m ^ 3) hm

private theorem vinogradovPrimeThreshold_le_envelopeBase {k τ : ℕ}
    (hk : 2 ≤ k) :
    vinogradovPrimeThreshold k ≤ vinogradovMeanValueEnvelopeBase k τ := by
  let m := k + τ + 1
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  have hfamily := vinogradovSeparatingFamilySize_le_pow_four hkm hm
  have hm8 : vinogradovSeparatingFamilySize k ^ 2 ≤ m ^ 8 := by
    calc
      vinogradovSeparatingFamilySize k ^ 2 ≤ (m ^ 4) ^ 2 :=
        Nat.pow_le_pow_left hfamily 2
      _ = m ^ 8 := by rw [← pow_mul]
  have hm8m16 : m ^ 8 ≤ m ^ 16 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ m) (by norm_num)
  dsimp [vinogradovPrimeThreshold, vinogradovMeanValueEnvelopeBase]
  apply max_le
  · exact calc
      2 ^ 28 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ 2 ^ 32 * m ^ 16 := by
        exact le_mul_of_one_le_right' (Nat.one_le_pow 16 m (by omega))
  · apply max_le
    · calc
        k ≤ m := hkm
        _ ≤ 2 ^ 32 * m ^ 16 := by
          calc
            m = 1 * m ^ 1 := by simp
            _ ≤ 2 ^ 32 * m ^ 16 := Nat.mul_le_mul (by norm_num)
              (Nat.pow_le_pow_right (by omega : 1 ≤ m) (by norm_num))
    · exact calc
        288 * vinogradovSeparatingFamilySize k ^ 2 ≤ 288 * m ^ 8 :=
          Nat.mul_le_mul_left 288 hm8
        _ ≤ 2 ^ 32 * m ^ 16 := Nat.mul_le_mul
          (by norm_num) hm8m16

private theorem vinogradovMeanValueEnvelopeBase_mono (k : ℕ) :
    Monotone (vinogradovMeanValueEnvelopeBase k) := by
  intro a b hab
  dsimp [vinogradovMeanValueEnvelopeBase]
  gcongr

set_option maxHeartbeats 1000000 in
private theorem vinogradovMeanValueStepConstant_le_envelope
    {k τ : ℕ} {C : ℝ} (hk : 2 ≤ k) (hτ : 1 ≤ τ)
    (hC0 : 0 ≤ C)
    (hC : C ≤ vinogradovMeanValueEnvelope k τ) :
    vinogradovMeanValueStepConstant k τ C ≤
      vinogradovMeanValueEnvelope k (τ + 1) := by
  let m := k + τ + 2
  let b := vinogradovMeanValueEnvelopeBase k (τ + 1)
  let L := k * τ + k
  let N := 2 * (k * τ) + k * (k - 1) / 2
  let A := (2 * (k * τ)) * k.factorial * 2 ^ N
  let F := L.factorial ^ 2 * vinogradovSeparatingFamilySize k
  let D := 2 * (k * k ^ L) ^ 2
  let T := vinogradovPrimeThreshold k ^ k
  let E₀ := 128 * k * τ * (k + τ + 1)
  let E₁ := 128 * k * (τ + 1) * m
  let e := 2 * L + k + 2 * N + 5
  have hm : 5 ≤ m := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  have hτm : τ ≤ m := by dsimp [m]; omega
  have hτone : τ + 1 ≤ m := by dsimp [m]; omega
  have hmb : m ≤ b := by
    dsimp [b, vinogradovMeanValueEnvelopeBase, m]
    calc
      k + τ + 2 = 1 * (k + (τ + 1) + 1) ^ 1 := by ring
      _ ≤ 2 ^ 32 * (k + (τ + 1) + 1) ^ 16 := Nat.mul_le_mul
        (by norm_num) (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hb1 : 1 ≤ b := by omega
  have h2b : 2 ≤ b := (by omega : 2 ≤ m).trans hmb
  have hkb : k ≤ b := hkm.trans hmb
  have hτb : τ ≤ b := hτm.trans hmb
  have hfamilym := vinogradovSeparatingFamilySize_le_pow_four hkm (by omega)
  have hm4b : m ^ 4 ≤ b := by
    dsimp [b, vinogradovMeanValueEnvelopeBase, m]
    calc
      (k + τ + 2) ^ 4 = 1 * (k + (τ + 1) + 1) ^ 4 := by ring
      _ ≤ 2 ^ 32 * (k + (τ + 1) + 1) ^ 16 := Nat.mul_le_mul
        (by norm_num) (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hfamilyb : vinogradovSeparatingFamilySize k ≤ b :=
    hfamilym.trans hm4b
  have hthresholdb : vinogradovPrimeThreshold k ≤ b := by
    simpa only [b] using vinogradovPrimeThreshold_le_envelopeBase
      (k := k) (τ := τ + 1) hk
  have hLb : L ≤ b := by
    calc
      L = k * (τ + 1) := by dsimp [L]; ring
      _ ≤ m * m := Nat.mul_le_mul hkm hτone
      _ ≤ b := by
        calc
          m * m = m ^ 2 := by ring
          _ ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          _ ≤ b := hm4b
  have hN : N ≤ 3 * k * m := by
    have hdiv : k * (k - 1) / 2 ≤ k * k := by
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left k (Nat.sub_le k 1))
    calc
      N ≤ 2 * (k * τ) + k * k := Nat.add_le_add_left hdiv _
      _ ≤ 2 * (k * m) + k * m := Nat.add_le_add
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left k hτm))
        (Nat.mul_le_mul_left k hkm)
      _ = 3 * k * m := by ring
  have hfac : L.factorial ≤ b ^ L := by
    exact Nat.factorial_le_pow L |>.trans (Nat.pow_le_pow_left hLb L)
  have hF : F ≤ b ^ (2 * L + 1) := by
    calc
      F ≤ (b ^ L) ^ 2 * b := Nat.mul_le_mul
        (Nat.pow_le_pow_left hfac 2) hfamilyb
      _ = b ^ (2 * L + 1) := by
        calc
          (b ^ L) ^ 2 * b = b ^ (L * 2) * b := by rw [pow_mul]
          _ = b ^ (L * 2 + 1) := by rw [← pow_succ]
          _ = b ^ (2 * L + 1) := by congr 1; omega
  have hsmallProduct : 2 * (k * τ) ≤ b ^ 3 := by
    calc
      2 * (k * τ) ≤ b * (b * b) := Nat.mul_le_mul h2b
        (Nat.mul_le_mul hkb hτb)
      _ = b ^ 3 := by ring
  have hkfac : k.factorial ≤ b ^ k := by
    exact Nat.factorial_le_pow k |>.trans (Nat.pow_le_pow_left hkb k)
  have htwoN : 2 ^ N ≤ b ^ N := Nat.pow_le_pow_left h2b N
  have hA : A ≤ b ^ (3 + k + N) := by
    calc
      A ≤ b ^ 3 * b ^ k * b ^ N := Nat.mul_le_mul
        (Nat.mul_le_mul hsmallProduct hkfac) htwoN
      _ = b ^ (3 + k + N) := by rw [← pow_add, ← pow_add]
  have hcoeff : 2 * F * A * 2 ^ N ≤ b ^ e := by
    calc
      2 * F * A * 2 ^ N ≤
          b * b ^ (2 * L + 1) * b ^ (3 + k + N) * b ^ N :=
        Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul h2b hF) hA) htwoN
      _ = b ^ e := by
        dsimp [e]
        rw [← pow_succ', ← pow_add, ← pow_add]
        congr 1
        omega
  have he : e ≤ 16 * k * m := by
    have hL : L ≤ k * m := by
      rw [show L = k * (τ + 1) by dsimp [L]; ring]
      exact Nat.mul_le_mul_left k hτone
    have h2L := Nat.mul_le_mul_left 2 hL
    have h2N := Nat.mul_le_mul_left 2 hN
    have h5 : 5 ≤ 7 * (k * m) := by
      have hkmpos : 0 < k * m := Nat.mul_pos (by omega) (by omega)
      omega
    calc
      e ≤ 2 * (k * m) + k * m + 2 * (3 * k * m) + 7 * (k * m) := by
        dsimp [e]
        omega
      _ = 16 * k * m := by ring
  have hD : D ≤ b ^ (2 * L + 3) := by
    calc
      D = 2 * k ^ 2 * k ^ (2 * L) := by
        dsimp [D]
        simp only [mul_pow]
        rw [← pow_mul]
        ring
      _ ≤ b * b ^ 2 * b ^ (2 * L) := Nat.mul_le_mul
        (Nat.mul_le_mul h2b (Nat.pow_le_pow_left hkb 2))
        (Nat.pow_le_pow_left hkb (2 * L))
      _ = b ^ (2 * L + 3) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
  have hTpow : T ^ (2 * (k * (τ + 1))) ≤
      b ^ (2 * k * k * (τ + 1)) := by
    calc
      T ^ (2 * (k * (τ + 1))) =
          vinogradovPrimeThreshold k ^ (2 * k * k * (τ + 1)) := by
        dsimp [T]
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ b ^ (2 * k * k * (τ + 1)) :=
        Nat.pow_le_pow_left hthresholdb _
  have hbmono : vinogradovMeanValueEnvelopeBase k τ ≤ b := by
    exact vinogradovMeanValueEnvelopeBase_mono k (Nat.le_succ τ)
  have henvold : vinogradovMeanValueEnvelope k τ ≤ (b : ℝ) ^ E₀ := by
    rw [vinogradovMeanValueEnvelope]
    have hbaseR : (vinogradovMeanValueEnvelopeBase k τ : ℝ) ≤ b := by
      exact_mod_cast hbmono
    have hexp : 128 * k * τ * (k + τ + 1) = E₀ := by
      rfl
    rw [hexp]
    exact_mod_cast Nat.pow_le_pow_left hbmono E₀
  have hC' : C ≤ (b : ℝ) ^ E₀ := hC.trans henvold
  have hE₁ : 2 ≤ E₁ := by
    dsimp [E₁]
    calc
      2 ≤ 128 * 1 * 1 * 1 := by norm_num
      _ ≤ 128 * k * (τ + 1) * m := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 128) (by omega)) (by omega)) (by omega)
  have hmainExp : e + E₀ + 2 ≤ E₁ := by
    have hkmpos : 0 < k * m := Nat.mul_pos (by omega) (by omega)
    have h16 : 16 * k * m ≤ 128 * k * m := by
      gcongr
      norm_num
    have h2 : 2 ≤ 128 * k * τ := by
      calc
        2 ≤ 128 * 1 * 1 := by norm_num
        _ ≤ 128 * k * τ := Nat.mul_le_mul
          (Nat.mul_le_mul (le_refl 128) (by omega)) (by omega)
    calc
      e + E₀ + 2 ≤ 16 * k * m + E₀ + 2 := by omega
      _ ≤ E₀ + (128 * k * m + 128 * k * τ) := by omega
      _ = E₁ := by dsimp [E₀, E₁, m]; ring
  have hDExp : 2 * L + 3 + 2 ≤ E₁ := by
    have hL : L ≤ k * m := by
      rw [show L = k * (τ + 1) by dsimp [L]; ring]
      exact Nat.mul_le_mul_left k hτone
    have hx : 0 < k * m := Nat.mul_pos (by omega) (by omega)
    have hsmall : 2 * (k * m) + 5 ≤ 128 * (k * m) := by omega
    have hlarge : 128 * k * m ≤ E₁ := by
      dsimp [E₁]
      calc
        128 * k * m = (128 * k * m) * 1 := by ring
        _ ≤ (128 * k * m) * (τ + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = 128 * k * (τ + 1) * m := by ring
    omega
  have hCSExp : 2 * k * k * (τ + 1) + 2 ≤ E₁ := by
    have hfirst : 2 * k * k * (τ + 1) ≤ 2 * k * m * (τ + 1) := by
      gcongr
    have hx : 0 < k * m * (τ + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hsmall : 2 * (k * m * (τ + 1)) + 2 ≤
        128 * (k * m * (τ + 1)) := by omega
    dsimp [E₁]
    calc
      2 * k * k * (τ + 1) + 2 ≤
          2 * (k * m * (τ + 1)) + 2 := by
            simpa only [mul_assoc] using Nat.add_le_add_right hfirst 2
      _ ≤ 128 * (k * m * (τ + 1)) := hsmall
      _ = 128 * k * (τ + 1) * m := by ring
  have hmain : (2 * F * A * 2 ^ N : ℝ) * C ≤
      (b : ℝ) ^ (E₁ - 2) := by
    have hcoeffR : (2 * F * A * 2 ^ N : ℝ) ≤ (b : ℝ) ^ e := by
      exact_mod_cast hcoeff
    have hmul : (2 * F * A * 2 ^ N : ℝ) * C ≤
        (b : ℝ) ^ e * (b : ℝ) ^ E₀ := by
      calc
        (2 * F * A * 2 ^ N : ℝ) * C ≤ (b : ℝ) ^ e * C :=
          mul_le_mul_of_nonneg_right hcoeffR hC0
        _ ≤ (b : ℝ) ^ e * (b : ℝ) ^ E₀ :=
          mul_le_mul_of_nonneg_left hC' (pow_nonneg (Nat.cast_nonneg b) _)
    have hexp : e + E₀ ≤ E₁ - 2 := by omega
    have hpow : (b : ℝ) ^ (e + E₀) ≤ (b : ℝ) ^ (E₁ - 2) := by
      exact_mod_cast Nat.pow_le_pow_right hb1 hexp
    calc
      (2 * F * A * 2 ^ N : ℝ) * C ≤
          (b : ℝ) ^ e * (b : ℝ) ^ E₀ := hmul
      _ = (b : ℝ) ^ (e + E₀) := (pow_add (b : ℝ) e E₀).symm
      _ ≤ (b : ℝ) ^ (E₁ - 2) := hpow
  have hD' : (D : ℝ) ≤ (b : ℝ) ^ (E₁ - 2) := by
    have hexp : 2 * L + 3 ≤ E₁ - 2 := by omega
    calc
      (D : ℝ) ≤ (b : ℝ) ^ (2 * L + 3) := by exact_mod_cast hD
      _ ≤ (b : ℝ) ^ (E₁ - 2) := by
        exact_mod_cast Nat.pow_le_pow_right hb1 hexp
  have hCS' : (T : ℝ) ^ (2 * (k * (τ + 1))) ≤
      (b : ℝ) ^ (E₁ - 2) := by
    have hexp : 2 * k * k * (τ + 1) ≤ E₁ - 2 := by omega
    calc
      (T : ℝ) ^ (2 * (k * (τ + 1))) ≤
          (b : ℝ) ^ (2 * k * k * (τ + 1)) := by exact_mod_cast hTpow
      _ ≤ (b : ℝ) ^ (E₁ - 2) := by
        exact_mod_cast Nat.pow_le_pow_right hb1 hexp
  have hone : (1 : ℝ) ≤ (b : ℝ) ^ (E₁ - 2) := by
    exact_mod_cast Nat.one_le_pow (E₁ - 2) b (by omega)
  have hfour : (4 : ℝ) ≤ (b : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left h2b 2
  rw [show vinogradovMeanValueEnvelope k (τ + 1) = (b : ℝ) ^ E₁ by
    rfl]
  unfold vinogradovMeanValueStepConstant
  change 2 * (F : ℝ) * ((A : ℝ) * C * (2 : ℝ) ^ N) +
      (D : ℝ) + (T : ℝ) ^ (2 * (k * (τ + 1))) + 1 ≤ _
  calc
    2 * (F : ℝ) * ((A : ℝ) * C * (2 : ℝ) ^ N) +
        (D : ℝ) + (T : ℝ) ^ (2 * (k * (τ + 1))) + 1 ≤
      4 * (b : ℝ) ^ (E₁ - 2) := by
        have hmain' : 2 * (F : ℝ) * ((A : ℝ) * C * (2 : ℝ) ^ N) ≤
            (b : ℝ) ^ (E₁ - 2) := by
          convert hmain using 1 <;> push_cast <;> ring
        linarith
    _ ≤ (b : ℝ) ^ 2 * (b : ℝ) ^ (E₁ - 2) :=
      mul_le_mul_of_nonneg_right hfour (pow_nonneg (Nat.cast_nonneg b) _)
    _ = (b : ℝ) ^ E₁ := by
      calc
        (b : ℝ) ^ 2 * (b : ℝ) ^ (E₁ - 2) =
            (b : ℝ) ^ (2 + (E₁ - 2)) :=
          (pow_add (b : ℝ) 2 (E₁ - 2)).symm
        _ = (b : ℝ) ^ E₁ := by congr 1; omega

set_option maxHeartbeats 1000000 in
private theorem vinogradovMeanValueConstantAux_le_envelope
    {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    vinogradovMeanValueConstantAux k n ≤
      vinogradovMeanValueEnvelope k (n + 1) := by
  induction n with
  | zero =>
      let b := vinogradovMeanValueEnvelopeBase k 1
      let E := 128 * k * (k + 2)
      have hm : k ≤ k + 2 := by omega
      have hmb : k + 2 ≤ b := by
        dsimp [b, vinogradovMeanValueEnvelopeBase]
        calc
          k + 2 = 1 * (k + 1 + 1) ^ 1 := by ring
          _ ≤ 2 ^ 32 * (k + 1 + 1) ^ 16 := Nat.mul_le_mul
            (by norm_num) (Nat.pow_le_pow_right (by omega) (by norm_num))
      have hkb : k ≤ b := hm.trans hmb
      have h2b : 2 ≤ b := (by omega : 2 ≤ k + 2).trans hmb
      have hfac : k.factorial ≤ b ^ k :=
        Nat.factorial_le_pow k |>.trans (Nat.pow_le_pow_left hkb k)
      have hone : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
      have hsum : k.factorial + 1 ≤ b ^ (k + 1) := by
        calc
          k.factorial + 1 ≤ b ^ k + b ^ k := Nat.add_le_add hfac hone
          _ = 2 * b ^ k := by ring
          _ ≤ b * b ^ k := Nat.mul_le_mul_right (b ^ k) h2b
          _ = b ^ (k + 1) := by rw [pow_succ']
      have hkE : k + 1 ≤ E := by
        dsimp [E]
        have hkpos : 0 < k := by omega
        nlinarith
      have hpow : b ^ (k + 1) ≤ b ^ E := Nat.pow_le_pow_right (by omega) hkE
      rw [vinogradovMeanValueConstantAux]
      unfold vinogradovMeanValueEnvelope
      rw [show 128 * k * (0 + 1) * (k + (0 + 1) + 1) = E by
        dsimp [E]; ring]
      simpa only [b] using
        (show (k.factorial : ℝ) + 1 ≤ (b : ℝ) ^ E by
          exact_mod_cast hsum.trans hpow)
  | succ n ih =>
      rw [vinogradovMeanValueConstantAux]
      exact vinogradovMeanValueStepConstant_le_envelope hk (by omega)
        (vinogradovMeanValueConstantAux_pos k n).le ih

/-- A fixed witness for the constant produced by the Linnik--Karatsuba
iteration.  The construction starts with `k! + 1`; at each round the proof
above adds its explicit nonsingular, singular, and finite-range constants. -/
noncomputable def vinogradovMeanValueConstant (k τ : ℕ) : ℝ :=
  if _hk : 2 ≤ k then
    if _hτ : 1 ≤ τ then vinogradovMeanValueConstantAux k (τ - 1)
    else 1
  else 1

/-- Positivity and the defining mean-value estimate for the named explicit
constant. -/
theorem vinogradovMeanValueConstant_spec {k τ : ℕ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) :
    0 < vinogradovMeanValueConstant k τ ∧
      ∀ P : ℕ, 1 ≤ P →
        (vinogradovJ (k * τ) k P : ℝ) ≤
          vinogradovMeanValueConstant k τ *
            (P : ℝ) ^ vinogradovExponent k τ := by
  rw [vinogradovMeanValueConstant, dif_pos hk, dif_pos hτ]
  refine ⟨vinogradovMeanValueConstantAux_pos k (τ - 1), ?_⟩
  intro P hP
  have hbound := vinogradovMeanValuePowerBoundExplicit k hk (τ - 1) P hP
  simpa only [Nat.sub_add_cancel hτ] using hbound

/-- The named mean-value constant is bounded by a closed expression whose
logarithm has polynomial-logarithmic growth in `k` and `τ`. -/
theorem vinogradovMeanValueConstant_le {k τ : ℕ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) :
    vinogradovMeanValueConstant k τ ≤
      vinogradovMeanValueEnvelope k τ := by
  rw [vinogradovMeanValueConstant, dif_pos hk, dif_pos hτ]
  simpa only [Nat.sub_add_cancel hτ] using
    vinogradovMeanValueConstantAux_le_envelope hk (τ - 1)

/-- Quantitative growth of the closed envelope.  Dividing the right-hand
side by `2*k*τ` gives at most
`3072 * (k+τ+1) * log (2*(k+τ+1))`. -/
theorem log_vinogradovMeanValueEnvelope_le {k τ : ℕ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) :
    Real.log (vinogradovMeanValueEnvelope k τ) ≤
      6144 * (k : ℝ) * τ * (k + τ + 1) *
        Real.log (2 * (k + τ + 1)) := by
  let m : ℕ := k + τ + 1
  let B : ℕ := vinogradovMeanValueEnvelopeBase k τ
  let E : ℕ := 128 * k * τ * m
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have htwo : (2 : ℝ) ≤ 2 * m := by nlinarith
  have hmmul : (m : ℝ) ≤ 2 * m := by nlinarith
  have hlogtwo : Real.log 2 ≤ Real.log (2 * m) :=
    Real.log_le_log (by norm_num) htwo
  have hlogm : Real.log m ≤ Real.log (2 * m) :=
    Real.log_le_log (by positivity) hmmul
  have hB : (B : ℝ) = (2 : ℝ) ^ 32 * (m : ℝ) ^ 16 := by
    norm_cast
  have hlogB : Real.log B ≤ 48 * Real.log (2 * m) := by
    rw [hB, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    nlinarith
  rw [vinogradovMeanValueEnvelope, Real.log_pow]
  change (E : ℝ) * Real.log B ≤ _
  calc
    (E : ℝ) * Real.log B ≤ (E : ℝ) *
        (48 * Real.log (2 * m)) :=
      mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = 6144 * (k : ℝ) * τ * (k + τ + 1) *
        Real.log (2 * (k + τ + 1)) := by
      dsimp [E, m]
      push_cast
      ring

/-- Vinogradov's mean value theorem in the weak explicit
Linnik--Karatsuba form.  The excess is
`(k² / 2) * (1 - 1 / k)^τ`, and hence decays geometrically in `τ`. -/
theorem vinogradov_mean_value (k : ℕ) (hk : 2 ≤ k) (τ : ℕ) (hτ : 1 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 1 ≤ P →
      (vinogradovJ (k * τ) k P : ℝ) ≤ C * (P : ℝ) ^
        (2 * k * τ - k * (k + 1) / 2 +
          (k ^ 2 / 2) * (1 - 1 / k) ^ τ : ℝ) := by
  refine ⟨vinogradovMeanValueConstant k τ,
    (vinogradovMeanValueConstant_spec hk hτ).1, ?_⟩
  intro P hP
  simpa only [vinogradovExponent, vinogradovDelta] using
    (vinogradovMeanValueConstant_spec hk hτ).2 P hP


end MoltResearch
