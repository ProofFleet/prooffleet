import Mathlib.Combinatorics.Hall.Finite
import Conjectures.C0004_erdos461_smooth.src.Reduction

/-!
# Erdős 461: component-graph foundations

This file supplies the elementary graph facts used by the matching reduction
in `Problems/erdos461_approach.md`.  The left vertices are the integers in
`[1, t / 2]`, the right vertices are the smooth-component values represented
in `(n, n + t]`, and divisibility is the edge relation.
-/

namespace MoltResearch.Erdos461

open Finset

/-- The lower-half divisor vertices in the component graph. -/
def componentLeft (t : ℕ) : Finset ℕ := Finset.Icc 1 (t / 2)

/-- The smooth-component values represented in `(n, n + t]`. -/
noncomputable def componentValues (n t : ℕ) : Finset ℕ :=
  (Finset.Ioc n (n + t)).image (smoothPart t)

/-- The component neighbours of a lower-half divisor `d`. -/
noncomputable def componentNeighbors (n t d : ℕ) : Finset ℕ :=
  (componentValues n t).filter (fun S => d ∣ S)

/-- The union of the component neighbourhoods of the vertices in `U`. -/
noncomputable def componentNeighborhood (n t : ℕ) (U : Finset ℕ) : Finset ℕ :=
  U.biUnion (componentNeighbors n t)

/-- A positive divisor smaller than the smoothness threshold divides the
smooth component. -/
theorem dvd_smoothPart_of_dvd_of_lt {d t m : ℕ} (hd : 0 < d) (hdt : d < t)
    (hm : 0 < m) (hdm : d ∣ m) : d ∣ smoothPart t m := by
  classical
  have hfac := Nat.factorization_prod_pow_eq_self hd.ne'
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hfac
  rw [← hfac]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_)
    (Finset.prod_dvd_prod_of_subset d.primeFactors
      (m.primeFactors.filter (fun p => p < t)) (fun p => p ^ m.factorization p) ?_)
  · exact pow_dvd_pow p ((Nat.factorization_le_iff_dvd hd.ne' hm.ne').mpr hdm p)
  · intro p hp
    have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
    have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, hpd.trans hdm, hm.ne'⟩
    exact Finset.mem_filter.mpr ⟨hpm, (Nat.le_of_dvd hd hpd).trans_lt hdt⟩

/-- Every left vertex has at least one component neighbour. -/
theorem componentNeighbors_nonempty {n t d : ℕ} (hd : d ∈ componentLeft t) :
    (componentNeighbors n t d).Nonempty := by
  classical
  have hdI := Finset.mem_Icc.mp hd
  let m := d * (n / d + 1)
  have hdpos : 0 < d := by omega
  have hdm : d ∣ m := dvd_mul_right d (n / d + 1)
  have hnm : n < m := by
    dsimp [m]
    exact Nat.lt_mul_div_succ n hdpos
  have hmn : m ≤ n + t := by
    have hm_le : d * (n / d + 1) ≤ n + d := by
      simpa [Nat.mul_add] using Nat.add_le_add_right (Nat.mul_div_le n d) d
    omega
  have hmt : d < t := by omega
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
  refine ⟨smoothPart t m, ?_⟩
  rw [componentNeighbors, Finset.mem_filter]
  exact ⟨Finset.mem_image.mpr ⟨m, Finset.mem_Ioc.mpr ⟨hnm, hmn⟩, rfl⟩,
    dvd_smoothPart_of_dvd_of_lt hdpos hmt hmpos hdm⟩

/-- A matching of at least `q` left vertices exists exactly when every set
`U` of left vertices has defect at most `|L| - q`.

This is the finite defect form of Hall's marriage theorem.  The reverse
implication applies ordinary Hall after adjoining `|L| - q` dummy right
vertices, then discards the left vertices sent to dummies.
-/
theorem exists_componentMatching_card_ge_iff_defectHall (n t q : ℕ)
    (hq : q ≤ (componentLeft t).card) :
    (∃ M : ComponentMatching n t, q ≤ M.domain.card) ↔
      ∀ U ⊆ componentLeft t,
        U.card ≤ (componentNeighborhood n t U).card + ((componentLeft t).card - q) := by
  classical
  let L := componentLeft t
  constructor
  · rintro ⟨M, hMcard⟩ U hUL
    have himage :
        (U ∩ M.domain).image M.component ⊆ componentNeighborhood n t U := by
      intro S hS
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hS
      have hdU : d ∈ U := (Finset.mem_inter.mp hd).1
      have hdM : d ∈ M.domain := (Finset.mem_inter.mp hd).2
      rw [componentNeighborhood, Finset.mem_biUnion]
      refine ⟨d, hdU, ?_⟩
      rw [componentNeighbors, Finset.mem_filter]
      exact ⟨M.component_mem d hdM, M.divisor_edge d hdM⟩
    have hinter_le : (U ∩ M.domain).card ≤ (componentNeighborhood n t U).card := by
      calc
        (U ∩ M.domain).card = ((U ∩ M.domain).image M.component).card := by
          exact (Finset.card_image_iff.mpr (M.injective.mono (by simp))).symm
        _ ≤ (componentNeighborhood n t U).card := Finset.card_le_card himage
    have hdiff_sub : U \ M.domain ⊆ L \ M.domain :=
      Finset.sdiff_subset_sdiff hUL (by simp)
    have hdiff_le : (U \ M.domain).card ≤ L.card - M.domain.card := by
      calc
        (U \ M.domain).card ≤ (L \ M.domain).card := Finset.card_le_card hdiff_sub
        _ = L.card - M.domain.card := Finset.card_sdiff_of_subset M.domain_subset
    have hpartition := Finset.card_inter_add_card_sdiff U M.domain
    dsimp [L] at hdiff_le
    omega
  · intro hdefect
    let k := (componentLeft t).card - q
    let augmented : ↥(componentLeft t) → Finset (ℕ ⊕ Fin k) := fun d =>
      (componentNeighbors n t d).image Sum.inl ∪
        (Finset.univ : Finset (Fin k)).image Sum.inr
    have hHall : ∀ s : Finset ↥(componentLeft t),
        s.card ≤ (s.biUnion augmented).card := by
      intro s
      by_cases hs : s = ∅
      · simp [hs]
      have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      let U : Finset ℕ := s.image Subtype.val
      have hUL : U ⊆ componentLeft t := by
        intro d hd
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hd
        exact x.property
      have hUcard : U.card = s.card :=
        Finset.card_image_of_injective s Subtype.val_injective
      have hbiUnion : s.biUnion augmented =
          (componentNeighborhood n t U).image Sum.inl ∪
            (Finset.univ : Finset (Fin k)).image Sum.inr := by
        ext z
        rcases z with S | j
        · simp [augmented, componentNeighborhood, U]
        · simp [augmented]
          obtain ⟨x, hx⟩ := hsne
          exact ⟨x, x.property, hx⟩
      have htags : Disjoint
          ((componentNeighborhood n t U).image Sum.inl)
          ((Finset.univ : Finset (Fin k)).image Sum.inr) := by
        rw [Finset.disjoint_left]
        simp
      rw [hbiUnion, Finset.card_union_of_disjoint htags,
        Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_fin]
      rw [← hUcard]
      simpa [k] using hdefect U hUL
    obtain ⟨f, hf_injective, hf_mem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' augmented).mp hHall
    let f' : ℕ → ℕ ⊕ Fin k := fun d =>
      if hd : d ∈ componentLeft t then f ⟨d, hd⟩ else Sum.inl 0
    let domain := (componentLeft t).filter (fun d => ∃ S, f' d = Sum.inl S)
    let dummyDomain := (componentLeft t).filter (fun d => ∃ j, f' d = Sum.inr j)
    let component : ℕ → ℕ := fun d => Sum.elim id (fun _ => 0) (f' d)
    have hf'_eq (d : ℕ) (hd : d ∈ componentLeft t) : f' d = f ⟨d, hd⟩ := by
      simp [f', hd]
    have hf'_injOn : Set.InjOn f' (componentLeft t : Set ℕ) := by
      intro a ha b hb hab
      have hab' : f ⟨a, ha⟩ = f ⟨b, hb⟩ :=
        (hf'_eq a ha).symm.trans (hab.trans (hf'_eq b hb))
      have hab'' : (⟨a, ha⟩ : ↥(componentLeft t)) = ⟨b, hb⟩ :=
        hf_injective hab'
      exact congrArg Subtype.val hab''
    have hreal (d : ℕ) (hd : d ∈ domain) : f' d = Sum.inl (component d) := by
      obtain ⟨-, S, hS⟩ := Finset.mem_filter.mp hd
      simp [component, hS]
    have hdomain_subset : domain ⊆ componentLeft t := Finset.filter_subset _ _
    have hdummy_subset : dummyDomain ⊆ componentLeft t := Finset.filter_subset _ _
    have hsplit : domain ∪ dummyDomain = componentLeft t := by
      ext d
      by_cases hd : d ∈ componentLeft t
      · rcases hfd : f' d with S | j
        · simp [domain, dummyDomain, hd, hfd]
        · simp [domain, dummyDomain, hd, hfd]
      · simp [domain, dummyDomain, hd]
    have hdisjoint : Disjoint domain dummyDomain := by
      rw [Finset.disjoint_left]
      intro d hdreal hddummy
      obtain ⟨-, S, hS⟩ := Finset.mem_filter.mp hdreal
      obtain ⟨-, j, hj⟩ := Finset.mem_filter.mp hddummy
      rw [hS] at hj
      exact Sum.inl_ne_inr hj
    have hdummy_image : dummyDomain.image f' ⊆
        (Finset.univ : Finset (Fin k)).image Sum.inr := by
      intro z hz
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨-, j, hj⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
    have hdummy_card : dummyDomain.card ≤ k := by
      calc
        dummyDomain.card = (dummyDomain.image f').card := by
          exact (Finset.card_image_iff.mpr (hf'_injOn.mono hdummy_subset)).symm
        _ ≤ ((Finset.univ : Finset (Fin k)).image Sum.inr).card :=
          Finset.card_le_card hdummy_image
        _ = k := by
          rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_fin]
    have hdomain_card : q ≤ domain.card := by
      have hcard := Finset.card_union_of_disjoint hdisjoint
      rw [hsplit] at hcard
      dsimp [k] at hdummy_card
      omega
    refine ⟨{
      domain := domain
      component := component
      domain_subset := hdomain_subset
      component_mem := ?_
      divisor_edge := ?_
      injective := ?_ }, hdomain_card⟩
    · intro d hd
      have hdL := hdomain_subset hd
      have hfmem := hf_mem ⟨d, hdL⟩
      rw [← hf'_eq d hdL, hreal d hd] at hfmem
      have hneighbor : component d ∈ componentNeighbors n t d := by
        simpa [augmented] using hfmem
      exact (Finset.mem_filter.mp hneighbor).1
    · intro d hd
      have hdL := hdomain_subset hd
      have hfmem := hf_mem ⟨d, hdL⟩
      rw [← hf'_eq d hdL, hreal d hd] at hfmem
      have hneighbor : component d ∈ componentNeighbors n t d := by
        simpa [augmented] using hfmem
      exact (Finset.mem_filter.mp hneighbor).2
    · intro a ha b hb hab
      apply hf'_injOn (hdomain_subset ha) (hdomain_subset hb)
      rw [hreal a ha, hreal b hb, hab]

end MoltResearch.Erdos461
