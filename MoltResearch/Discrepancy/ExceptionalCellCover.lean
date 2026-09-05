import MoltResearch.Discrepancy.LargePrimePolynomialCount
import MoltResearch.Discrepancy.LevelLegs

/-!
# Unit-cell covers of the exceptional first-index part

The top first-index part is the complement of all ordinary small-value sets.
Consequently every cell meeting that part contains a point at which a cell
polynomial from the last ordinary level is large.  This file records the finite
cover and the high-moment count for each resulting family of cells.
-/

namespace MoltResearch

open Finset MeasureTheory ExpSums

/-- Cells in `K` which contain a point of `G`.  Closed cells are used so the
maximising-sample lemma applies directly. -/
noncomputable def cellsMeetingSet (K : Finset ℤ) (G : Set ℝ) : Finset ℤ :=
  by
    classical
    exact K.filter fun k => ∃ t ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), t ∈ G

@[simp] theorem mem_cellsMeetingSet {K : Finset ℤ} {G : Set ℝ} {k : ℤ} :
    k ∈ cellsMeetingSet K G ↔
      k ∈ K ∧ ∃ t ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), t ∈ G := by
  classical
  simp [cellsMeetingSet]

/-- Cells in `K` on which `F` exceeds `V` somewhere. -/
noncomputable def largeValueCells (K : Finset ℤ) (F : ℝ → ℂ) (V : ℝ) : Finset ℤ :=
  by
    classical
    exact K.filter fun k => ∃ t ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), V < ‖F t‖

@[simp] theorem mem_largeValueCells {K : Finset ℤ} {F : ℝ → ℂ} {V : ℝ} {k : ℤ} :
    k ∈ largeValueCells K F V ↔
      k ∈ K ∧ ∃ t ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), V < ‖F t‖ := by
  classical
  simp [largeValueCells]

/-- **Phase 0 VI-9c — cells meeting the exceptional part are covered by
last-level large-value cells.** -/
theorem cellsMeeting_exceptional_subset_biUnion
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (hJ : 0 < J) (G : Set ℝ) (K : Finset ℤ) :
    cellsMeetingSet K
        (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G J) ⊆
      (Finset.Ico (v₀ (J - 1)) (v₁ (J - 1) + 1)).biUnion fun r =>
        largeValueCells K (levelCellPoly (P (J - 1)) (N (J - 1)) r g)
          (Real.exp (-(alpha (J - 1) * (r : ℝ) /
            ((2 * N (J - 1) : ℕ) : ℝ)))) := by
  classical
  intro k hk
  rw [mem_cellsMeetingSet] at hk
  obtain ⟨hkK, t, htcell, htExceptional⟩ := hk
  have htNotSmall :
      t ∉ levelSmallSet P N v₀ v₁ g alpha (J - 1) := by
    intro htSmall
    have htTop := htExceptional.2
    rw [bandPart, if_neg (lt_irrefl J)] at htTop
    exact htTop (Set.mem_iUnion₂.mpr
      ⟨J - 1, Finset.mem_range.mpr (by omega), htSmall⟩)
  simp only [levelSmallSet, Set.mem_setOf_eq] at htNotSmall
  push_neg at htNotSmall
  obtain ⟨r, hr, hrLarge⟩ := htNotSmall
  rw [Finset.mem_biUnion]
  refine ⟨r, hr, ?_⟩
  rw [mem_largeValueCells]
  exact ⟨hkK, t, htcell, hrLarge⟩

/-- Cardinality form of `cellsMeeting_exceptional_subset_biUnion`. -/
theorem card_cellsMeeting_exceptional_le_sum
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (hJ : 0 < J) (G : Set ℝ) (K : Finset ℤ) :
    (cellsMeetingSet K
        (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G J)).card
      ≤ ∑ r ∈ Finset.Ico (v₀ (J - 1)) (v₁ (J - 1) + 1),
          (largeValueCells K (levelCellPoly (P (J - 1)) (N (J - 1)) r g)
            (Real.exp (-(alpha (J - 1) * (r : ℝ) /
              ((2 * N (J - 1) : ℕ) : ℝ))))).card := by
  classical
  exact (Finset.card_le_card
    (cellsMeeting_exceptional_subset_biUnion P N v₀ v₁ g alpha J hJ G K)).trans
      Finset.card_biUnion_le

/-- Two cells of the same parity, with their maximisers chosen in the closed
cells, give distinct sample points. -/
theorem injectiveOn_cell_samples_of_same_parity (K : Finset ℤ) (tau : ℤ → ℝ)
    (htau : ∀ k ∈ K, tau k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (hparity : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k) :
    Set.InjOn tau K := by
  intro k hk l hl heq
  by_contra hne
  rcases hparity k hk l hl hne with hkl | hlk
  · have hkhi := (htau k hk).2
    have hllo := (htau l hl).1
    rw [heq] at hkhi
    have hcast : (k : ℝ) + 2 ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  · have hlhi := (htau l hl).2
    have hklo := (htau k hk).1
    rw [← heq] at hlhi
    have hcast : (l : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hlk
    linarith

-- The two parity families duplicate the high-moment argument, so permit the
-- same bounded elaboration headroom as the underlying count.
set_option maxHeartbeats 800000 in
/-- **Phase 0 VI-9c — high-moment count for unit cells with a large prime
polynomial.**

The factor `2` is the even/odd split.  Maximisers in cells of one parity are
`1`-separated, so `card_large_prime_poly_pow_le` applies to both images. -/
theorem card_largeValueCells_prime_poly_pow_le (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (ell : ℕ) (hell : 1 ≤ ell)
    (K : Finset ℤ) (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hlam : 0 < lam)
    (hKT : ∀ k ∈ K, -(T : ℝ) ≤ k ∧ (k : ℝ) + 1 ≤ T) :
    ((largeValueCells K
        (fun t => ∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)) V).card : ℝ)
        * V ^ (2 * ell)
      ≤ 2 * (Real.exp Real.pi
          * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
        * ((Nat.factorial ell : ℝ) ^ 2
            * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
        * ((1 + lam) + (1 / lam)
            * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2)) := by
  classical
  let F : ℝ → ℂ := fun t => ∑ p ∈ Y, (b p / (p : ℂ))
    * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)
  let KL := largeValueCells K F V
  let KE := KL.filter Even
  let KO := KL.filter fun k => ¬Even k
  have hFc : Continuous F :=
    continuous_char_poly Y (fun p => b p / (p : ℂ)) (fun p => Real.log p)
  obtain ⟨tau, htauAll, hmax⟩ := exists_cell_max_sample F hFc
  have htau : ∀ k ∈ KL, tau k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) :=
    fun k _ => htauAll k
  have hKLK : KL ⊆ K := by
    intro k hk
    exact (mem_largeValueCells.mp hk).1
  have hgapE : ∀ k ∈ KE, ∀ l ∈ KE, k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k := by
    intro k hk l hl hne
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨n, hn⟩ := (Finset.mem_filter.mp hl).2
    omega
  have hgapO : ∀ k ∈ KO, ∀ l ∈ KO, k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k := by
    intro k hk l hl hne
    have hkOdd := (Finset.mem_filter.mp hk).2
    have hlOdd := (Finset.mem_filter.mp hl).2
    rw [Int.not_even_iff_odd] at hkOdd hlOdd
    obtain ⟨m, hm⟩ := hkOdd
    obtain ⟨n, hn⟩ := hlOdd
    omega
  have hfamily : ∀ K' : Finset ℤ, K' ⊆ KL →
      (∀ k ∈ K', ∀ l ∈ K', k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k) →
      ((K'.image tau).card : ℝ) * V ^ (2 * ell)
        ≤ Real.exp Real.pi
            * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
          * ((Nat.factorial ell : ℝ) ^ 2
              * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
          * ((1 + lam) + (1 / lam)
              * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2) := by
    intro K' hsub hgap
    apply card_large_prime_poly_pow_le Y hY P hP hlo hhi b hb ell hell
      (K'.image tau) T V lam hT hV hlam
    · intro t ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      have hkK := hKLK (hsub hk)
      exact ⟨(hKT k hkK).1.trans (htau k (hsub hk)).1,
        (htau k (hsub hk)).2.trans (hKT k hkK).2⟩
    · exact separated_of_sample_gap_two K' tau (fun k hk => htau k (hsub hk)) hgap
    · intro t ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨_hkK, u, hucell, huLarge⟩ := mem_largeValueCells.mp (hsub hk)
      exact huLarge.le.trans (hmax k u hucell)
  have hE := hfamily KE (Finset.filter_subset _ _) hgapE
  have hO := hfamily KO (Finset.filter_subset _ _) hgapO
  have hcardE : (KE.image tau).card = KE.card :=
    Finset.card_image_iff.mpr
      (injectiveOn_cell_samples_of_same_parity KE tau
        (fun k hk => htau k ((Finset.filter_subset Even KL) hk)) hgapE)
  have hcardO : (KO.image tau).card = KO.card :=
    Finset.card_image_iff.mpr
      (injectiveOn_cell_samples_of_same_parity KO tau
        (fun k hk => htau k
          ((Finset.filter_subset (fun k : ℤ => ¬Even k) KL) hk)) hgapO)
  rw [hcardE] at hE
  rw [hcardO] at hO
  have hpartition : KE.card + KO.card = KL.card := by
    exact Finset.card_filter_add_card_filter_not (s := KL) Even
  dsimp [KL] at hpartition ⊢
  rw [← hpartition]
  push_cast
  push_cast at hE hO
  nlinarith

end MoltResearch
