import Conjectures.C0004_erdos461_smooth.src.Expansion

/-!
# Erdős 461: obstruction to a bounded-degree Delta/sieve route

This file records the unconditional combinatorial obstruction isolated in
`Problems/erdos461_delta_sieve.md`.  Removing every component with more than
two lower-half divisor neighbours cannot leave the quarter-size matching
required by `MultiscaleComponentExpansionAssumption`: already at `t = 38`,
only nine left vertices can touch a retained component, whereas the target is
`ceil(38 / 4) = 10`.

This does not refute the full component graph or Erdős 461.  It only rules out
the indicated bounded-degree pruning step.
-/

namespace MoltResearch.Erdos461

open Finset

/-- The number of lower-half left vertices dividing a component value.  This
is the right degree of `S` in the full component graph whenever `S` is a
represented component value. -/
def componentDivisorDegree (t S : ℕ) : ℕ :=
  ((componentLeft t).filter (fun d => d ∣ S)).card

/-- A left divisor can touch a right vertex of degree at most `D` only if the
divisor itself has at most `D` positive divisors. -/
def boundedDegreeEligibleLeft (t D : ℕ) : Finset ℕ :=
  (componentLeft t).filter (fun d => d.divisors.card ≤ D)

/-- Every positive divisor of `d` is another lower-half neighbour of any
component divisible by `d`. -/
theorem divisors_subset_componentDivisors {d t S : ℕ}
    (hd : d ∈ componentLeft t) (hdS : d ∣ S) :
    d.divisors ⊆ (componentLeft t).filter (fun a => a ∣ S) := by
  intro a ha
  have hdI := Finset.mem_Icc.mp hd
  have had : a ∣ d := Nat.dvd_of_mem_divisors ha
  rw [Finset.mem_filter]
  refine ⟨?_, had.trans hdS⟩
  rw [componentLeft, Finset.mem_Icc]
  exact ⟨Nat.pos_of_mem_divisors ha,
    (Nat.le_of_dvd hdI.1 had).trans hdI.2⟩

/-- The divisor count of a matched left vertex lower-bounds the degree of its
component. -/
theorem card_divisors_le_componentDivisorDegree {d t S : ℕ}
    (hd : d ∈ componentLeft t) (hdS : d ∣ S) :
    d.divisors.card ≤ componentDivisorDegree t S := by
  exact Finset.card_le_card (divisors_subset_componentDivisors hd hdS)

/-- The factorial of the left cutoff is a maximally high-degree component:
every lower-half left vertex divides it. -/
theorem componentDivisorDegree_factorial (t : ℕ) :
    componentDivisorDegree t (t / 2).factorial = (componentLeft t).card := by
  rw [componentDivisorDegree, Finset.filter_eq_self.mpr]
  intro d hd
  have hdI := Finset.mem_Icc.mp hd
  exact Nat.dvd_factorial hdI.1 hdI.2

/-- Maximally high-degree components genuinely occur in intervals.  For
`t ≥ 2`, the number `(t / 2)!` is `t`-smooth and is represented in the
interval starting one below it. -/
theorem factorial_mem_componentValues (t : ℕ) (ht : 2 ≤ t) :
    (t / 2).factorial ∈
      componentValues ((t / 2).factorial - 1) t := by
  rw [componentValues, Finset.mem_image]
  refine ⟨(t / 2).factorial, ?_, ?_⟩
  · rw [Finset.mem_Ioc]
    constructor <;> have hpos := Nat.factorial_pos (t / 2) <;> omega
  · apply smoothPart_eq_self (Nat.factorial_ne_zero (t / 2))
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ t / 2 := hpprime.dvd_factorial.mp
      (Nat.dvd_of_mem_primeFactors hp)
    omega

/-- Consequently every left vertex matched through a degree-`D` component is
in the arithmetically restricted eligible set. -/
theorem mem_boundedDegreeEligibleLeft_of_dvd {d t S D : ℕ}
    (hd : d ∈ componentLeft t) (hdS : d ∣ S)
    (hdegree : componentDivisorDegree t S ≤ D) :
    d ∈ boundedDegreeEligibleLeft t D := by
  rw [boundedDegreeEligibleLeft, Finset.mem_filter]
  exact ⟨hd, (card_divisors_le_componentDivisorDegree hd hdS).trans hdegree⟩

/-- In `[1, 19]`, exactly nine integers have at most two positive divisors:
`1` and the eight primes through `19`. -/
theorem boundedDegreeEligibleLeft_card_38 :
    (boundedDegreeEligibleLeft 38 2).card = 9 := by
  native_decide

/-- A component matching at `t = 38` that discards every right vertex of
degree greater than two has domain size at most nine. -/
theorem degreeTwo_componentMatching_card_le_nine {n : ℕ}
    (M : ComponentMatching n 38)
    (hdegree : ∀ d ∈ M.domain,
      componentDivisorDegree 38 (M.component d) ≤ 2) :
    M.domain.card ≤ 9 := by
  have hsubset : M.domain ⊆ boundedDegreeEligibleLeft 38 2 := by
    intro d hd
    exact mem_boundedDegreeEligibleLeft_of_dvd
      (M.domain_subset hd) (M.divisor_edge d hd) (hdegree d hd)
  calc
    M.domain.card ≤ (boundedDegreeEligibleLeft 38 2).card :=
      Finset.card_le_card hsubset
    _ = 9 := boundedDegreeEligibleLeft_card_38

/-- Thus degree-two pruning cannot supply the B7 quarter target at `t = 38`.
The theorem is uniform in the interval start `n`. -/
theorem no_degreeTwo_quarterMatching_38 (n : ℕ) :
    ¬ ∃ M : ComponentMatching n 38,
      10 ≤ M.domain.card ∧
        ∀ d ∈ M.domain, componentDivisorDegree 38 (M.component d) ≤ 2 := by
  rintro ⟨M, hten, hdegree⟩
  have hnine := degreeTwo_componentMatching_card_le_nine M hdegree
  omega

end MoltResearch.Erdos461
