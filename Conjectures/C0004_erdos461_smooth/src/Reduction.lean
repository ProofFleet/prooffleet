import Conjectures.C0004_erdos461_smooth.src.Statement

/-!
# Erdős 461: a proportional-matching reduction

This file records the reduction described in
`Problems/erdos461_approach.md`.  It does not prove Erdős 461: the only
unproved mathematical input is isolated in
`ProportionalComponentMatchingAssumption`.

The tentative matching of dyadic divisors to distinct multiples is false.
The replacement below asks only for a positive-proportion partial matching,
and matches directly into distinct smooth-component values.  The elementary
fiber bound above the `t / 2` threshold is proved unconditionally.
-/

namespace MoltResearch.Erdos461

open Finset

/-- The elements of `(n, n + t]` whose `t`-smooth component is `S`. -/
noncomputable def smoothPartFiber (n t S : ℕ) : Finset ℕ :=
  (Finset.Ioc n (n + t)).filter (fun m => smoothPart t m = S)

private theorem eq_of_dvd_of_two_sided_sub_lt {S x y : ℕ}
    (hsx : S ∣ x) (hsy : S ∣ y)
    (hxy : x < y → y - x < S) (hyx : y < x → x - y < S) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hdvd : S ∣ y - x := Nat.dvd_sub hsy hsx
    have hle : S ≤ y - x := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
    exact (not_lt_of_ge hle (hxy hlt)).elim
  · exact heq
  · have hdvd : S ∣ x - y := Nat.dvd_sub hsx hsy
    have hle : S ≤ x - y := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd
    exact (not_lt_of_ge hle (hyx hgt)).elim

/-- A smooth-component value at least `t / 2` occurs at most twice in an
interval of length `t`.

The integer form of the threshold is `t ≤ 2 * S`.  The proof splits at
`n + S`; each side contains at most one multiple of `S`, since two such
multiples would differ by at least `S`.
-/
theorem smoothPartFiber_card_le_two (n t S : ℕ) (ht : t ≤ 2 * S) :
    (smoothPartFiber n t S).card ≤ 2 := by
  classical
  let fiber := smoothPartFiber n t S
  let left := fiber.filter (fun m => m ≤ n + S)
  let right := fiber.filter (fun m => ¬m ≤ n + S)
  have hleft : left.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxf := Finset.mem_filter.mp hx'.1
    have hyf := Finset.mem_filter.mp hy'.1
    have hxI := Finset.mem_Ioc.mp hxf.1
    have hyI := Finset.mem_Ioc.mp hyf.1
    have hsx : S ∣ x := by
      rw [← hxf.2]
      exact smoothPart_dvd t x
    have hsy : S ∣ y := by
      rw [← hyf.2]
      exact smoothPart_dvd t y
    apply eq_of_dvd_of_two_sided_sub_lt hsx hsy
    · intro hxy
      omega
    · intro hyx
      omega
  have hright : right.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxf := Finset.mem_filter.mp hx'.1
    have hyf := Finset.mem_filter.mp hy'.1
    have hxI := Finset.mem_Ioc.mp hxf.1
    have hyI := Finset.mem_Ioc.mp hyf.1
    have hsx : S ∣ x := by
      rw [← hxf.2]
      exact smoothPart_dvd t x
    have hsy : S ∣ y := by
      rw [← hyf.2]
      exact smoothPart_dvd t y
    apply eq_of_dvd_of_two_sided_sub_lt hsx hsy
    · intro hxy
      omega
    · intro hyx
      omega
  have hsplit : left ∪ right = fiber := by
    exact Finset.filter_union_filter_not_eq (fun m => m ≤ n + S) fiber
  calc
    fiber.card = (left ∪ right).card := congrArg Finset.card hsplit.symm
    _ ≤ left.card + right.card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add hleft hright
    _ = 2 := rfl

/-- A partial matching from lower-half divisors to distinct smooth-component
values present in `(n, n + t]`.

The divisibility condition is the edge relation in the component graph from
`Problems/erdos461_approach.md`.  It is retained even though cardinality of
the matching alone is enough for the final bridge.
-/
structure ComponentMatching (n t : ℕ) where
  domain : Finset ℕ
  component : ℕ → ℕ
  domain_subset : domain ⊆ Finset.Icc 1 (t / 2)
  component_mem : ∀ d ∈ domain,
    component d ∈ (Finset.Ioc n (n + t)).image (smoothPart t)
  divisor_edge : ∀ d ∈ domain, d ∣ component d
  injective : Set.InjOn component domain

/-- Any component matching injects its domain into the set counted by
`smoothComponentCount`. -/
theorem ComponentMatching.card_le_smoothComponentCount {n t : ℕ}
    (M : ComponentMatching n t) : M.domain.card ≤ smoothComponentCount n t := by
  classical
  rw [smoothComponentCount]
  calc
    M.domain.card = (M.domain.image M.component).card := by
      exact (Finset.card_image_iff.mpr M.injective).symm
    _ ≤ ((Finset.Ioc n (n + t)).image (smoothPart t)).card := by
      apply Finset.card_le_card
      intro S hS
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hS
      exact M.component_mem d hd

/-- The open input in the reduction: the component graph always contains a
positive-proportion partial matching.

This is deliberately weaker than a perfect matching, which is false.  It is
also stronger than the conclusion and is not claimed as known; see the
obstruction and proposed Phase-2 work in `Problems/erdos461_approach.md`.
-/
class ProportionalComponentMatchingAssumption : Prop where
  bound : ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t →
    ∃ M : ComponentMatching n t, c * t ≤ M.domain.card

/-- A positive-proportion component matching implies Erdős 461.

This theorem is conditional on the named assumption above and therefore is
not an unconditional proof of the open problem.
-/
theorem erdos461_of_assumptions [h : ProportionalComponentMatchingAssumption] :
    Erdos461 := by
  obtain ⟨c, hc, hmatching⟩ := h.bound
  refine ⟨c, hc, ?_⟩
  intro n t ht
  obtain ⟨M, hM⟩ := hmatching n t ht
  calc
    c * t ≤ M.domain.card := hM
    _ ≤ smoothComponentCount n t := by
      exact_mod_cast M.card_le_smoothComponentCount

end MoltResearch.Erdos461
