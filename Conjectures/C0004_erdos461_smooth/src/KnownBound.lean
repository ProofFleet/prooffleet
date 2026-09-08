import MoltResearch.Discrepancy.BrunIntervalSieve
import Conjectures.C0004_erdos461_smooth.src.Reduction

/-!
# Erdős 461: audit of the reported logarithmic bound

Erdős and Graham report `f(n,t) ≫ t / log t` on p. 92 of *Old and New
Problems and Results in Combinatorial Number Theory* (1980), but give no
proof or citation there.  The accompanying memo
`Problems/erdos461_known_bound.md` records the source audit and explains why
the available one-fibre Brun bound below does not yield the simultaneous
support estimate required for that report.

Accordingly this file does not assert the reported estimate as a theorem.
It proves the exact reduction to rough quotients, applies the tree's finite
Brun sieve to each individual fibre, proves the collision-loss identity, and
isolates the still-missing simultaneous estimate in a named assumption.
-/

namespace MoltResearch.Erdos461

open Finset

/-- A smooth component is positive, including when the original number is
zero (the empty product is one). -/
theorem smoothPart_pos (t m : ℕ) : 0 < smoothPart t m := by
  classical
  unfold smoothPart
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors
    (Finset.mem_of_mem_filter p hp)).pos _

/-- The exponent of `p` in the smooth component is the full exponent in
`m` exactly when `p` is prime and below the threshold. -/
private theorem smoothPart_factorization (t m p : ℕ) :
    (smoothPart t m).factorization p =
      if p.Prime ∧ p < t then m.factorization p else 0 := by
  classical
  unfold smoothPart
  rw [Nat.factorization_prod_apply]
  · by_cases hp : p.Prime
    · by_cases hpt : p < t
      · rw [if_pos ⟨hp, hpt⟩]
        rw [Finset.sum_eq_single p]
        · simp [hp]
        · intro q hq hqp
          have hqprime := Nat.prime_of_mem_primeFactors
            (Finset.mem_of_mem_filter q hq)
          rw [hqprime.factorization_pow]
          simp [hqp]
        · intro hpnot
          have hfac0 : m.factorization p = 0 := by
            by_contra hne
            apply hpnot
            exact Finset.mem_filter.mpr ⟨by
              rw [← Nat.support_factorization]
              exact Finsupp.mem_support_iff.mpr hne, hpt⟩
          simp [hfac0]
      · rw [if_neg (fun h => hpt h.2)]
        apply Finset.sum_eq_zero
        intro q hq
        have hqprime := Nat.prime_of_mem_primeFactors
          (Finset.mem_of_mem_filter q hq)
        rw [hqprime.factorization_pow]
        simp [Finsupp.single_apply]
        intro hqp
        subst q
        exact (hpt (Finset.mem_filter.mp hq).2).elim
    · rw [if_neg (fun h => hp h.1)]
      apply Finset.sum_eq_zero
      intro q _
      exact Nat.factorization_eq_zero_of_not_prime _ hp
  · intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors
      (Finset.mem_of_mem_filter q hq)).ne_zero

/-- After dividing a positive integer by its full smooth component, no prime
below the threshold remains.  This is the exact one-way input needed to place
a component fibre inside a sifted quotient interval. -/
theorem not_dvd_div_smoothPart_of_prime_lt {t m p : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpt : p < t) : ¬p ∣ m / smoothPart t m := by
  have hsdvd := smoothPart_dvd t m
  have hqpos : 0 < m / smoothPart t m :=
    Nat.div_pos (Nat.le_of_dvd hm hsdvd) (smoothPart_pos t m)
  have hfac := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_div hsdvd)
  change (m / smoothPart t m).factorization p =
    m.factorization p - (smoothPart t m).factorization p at hfac
  rw [smoothPart_factorization, if_pos ⟨hp, hpt⟩, Nat.sub_self] at hfac
  intro hpdvd
  have hpos := (hp.dvd_iff_one_le_factorization hqpos.ne').mp hpdvd
  omega

/-- Candidate quotients for the fibre with component `S`: an interval of
length about `t / S`, sifted by every prime below `t`. -/
def roughQuotients (n t S : ℕ) : Finset ℕ :=
  (Finset.Ioc (n / S) ((n + t) / S)).filter
    (fun q => ∀ p ∈ t.primesBelow, ¬p ∣ q)

/-- Division by `S` injects the component fibre into its sifted quotient
interval. -/
theorem smoothPartFiber_card_le_roughQuotients (n t S : ℕ) :
    (smoothPartFiber n t S).card ≤ (roughQuotients n t S).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun m => m / S) ?_ ?_
  · intro m hm
    change m ∈ smoothPartFiber n t S at hm
    have hm' := Finset.mem_filter.mp hm
    have hmI := Finset.mem_Ioc.mp hm'.1
    have hmS := hm'.2
    have hSpos : 0 < S := by
      rw [← hmS]
      exact smoothPart_pos t m
    have hSdvd : S ∣ m := by
      rw [← hmS]
      exact smoothPart_dvd t m
    change m / S ∈ roughQuotients n t S
    rw [roughQuotients, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, Nat.div_le_div_right hmI.2⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hSpos]
      simpa [Nat.div_mul_cancel hSdvd] using hmI.1
    · intro p hp
      have hp' := Nat.mem_primesBelow.mp hp
      simpa [hmS] using
        not_dvd_div_smoothPart_of_prime_lt (lt_of_le_of_lt (Nat.zero_le n) hmI.1)
          hp'.2 hp'.1
  · intro a ha b hb hab
    change a / S = b / S at hab
    change a ∈ smoothPartFiber n t S at ha
    change b ∈ smoothPartFiber n t S at hb
    have ha := Finset.mem_filter.mp ha
    have hb := Finset.mem_filter.mp hb
    have hSa : S ∣ a := by
      rw [← ha.2]
      exact smoothPart_dvd t a
    have hSb : S ∣ b := by
      rw [← hb.2]
      exact smoothPart_dvd t b
    calc
      a = a / S * S := (Nat.div_mul_cancel hSa).symm
      _ = b / S * S := by rw [hab]
      _ = b := Nat.div_mul_cancel hSb

/-- The tree's Brun sieve gives this explicit upper bound for one component
fibre.  The endpoint term and the lack of correlation between different `S`
are why summing these bounds does not prove the reported logarithmic result. -/
theorem smoothPartFiber_card_le_brun (n t S k : ℕ) :
    ((smoothPartFiber n t S).card : ℝ) ≤
      ((((n + t) / S : ℕ) : ℝ) - ((n / S : ℕ) : ℝ)) *
        ((∏ p ∈ t.primesBelow, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ t.primesBelow, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ)) +
        ((t.primesBelow.card : ℝ) + 1) ^ (2 * k) := by
  have hquotient := smoothPartFiber_card_le_roughQuotients n t S
  have hquotientR : ((smoothPartFiber n t S).card : ℝ) ≤
      ((roughQuotients n t S).card : ℝ) := by
    exact_mod_cast hquotient
  have hdiv : n / S ≤ (n + t) / S := Nat.div_le_div_right (by omega)
  have hbrun := MoltResearch.card_no_factor_Ioc_le_brun
    (n / S) ((n + t) / S) hdiv t.primesBelow
    (fun p hp => Nat.prime_of_mem_primesBelow hp) k
  exact hquotientR.trans (by simpa [roughQuotients] using hbrun)

/-- Total loss from collisions: a fibre of size `r` contributes `r - 1`. -/
noncomputable def collisionExcess (n t : ℕ) : ℕ :=
  Finset.sum ((Finset.Ioc n (n + t)).image (smoothPart t))
    (fun S => (smoothPartFiber n t S).card - 1)

/-- The component fibres partition the interval. -/
theorem sum_smoothPartFiber_card (n t : ℕ) :
    (∑ S ∈ (Finset.Ioc n (n + t)).image (smoothPart t),
      (smoothPartFiber n t S).card) = t := by
  classical
  simpa [smoothPartFiber] using
    (Finset.card_eq_sum_card_image (smoothPart t) (Finset.Ioc n (n + t))).symm

/-- Exact collision ledger: distinct components plus all repeated copies
account for the `t` integers in the interval. -/
theorem collisionExcess_add_smoothComponentCount (n t : ℕ) :
    collisionExcess n t + smoothComponentCount n t = t := by
  classical
  have hfiber_pos : ∀ S ∈ (Finset.Ioc n (n + t)).image (smoothPart t),
      1 ≤ (smoothPartFiber n t S).card := by
    intro S hS
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.one_le_card]
    exact ⟨m, Finset.mem_filter.mpr ⟨hm, rfl⟩⟩
  have hcollision : collisionExcess n t =
      (∑ S ∈ (Finset.Ioc n (n + t)).image (smoothPart t),
        (smoothPartFiber n t S).card) -
        ((Finset.Ioc n (n + t)).image (smoothPart t)).card := by
    unfold collisionExcess
    rw [Finset.sum_tsub_distrib _ hfiber_pos]
    simp
  rw [hcollision, sum_smoothPartFiber_card, smoothComponentCount]
  exact Nat.sub_add_cancel (smoothComponentCount_le n t)

/-- The logarithmic lower bound reported without proof by Erdős--Graham,
recorded as an open proposition rather than an unconditional theorem. -/
def Erdos461LogBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t →
    c * (t : ℝ) / Real.log t ≤ smoothComponentCount n t

/-- The precise missing simultaneous input.  Brun controls each rough fibre
separately; this class asks for the global collision-loss estimate that does
not follow by summing those one-fibre upper bounds.  No instance is declared. -/
class SimultaneousFiberLossAssumption : Prop where
  bound : ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t →
    (collisionExcess n t : ℝ) ≤
      (t : ℝ) - c * (t : ℝ) / Real.log t

/-- The missing simultaneous fibre-loss estimate implies the reported
`t / log t` lower bound.  This theorem is conditional and does not prove the
reported estimate. -/
theorem erdos461LogBound_of_simultaneousFiberLoss
    [h : SimultaneousFiberLossAssumption] : Erdos461LogBound := by
  obtain ⟨c, hc, hbound⟩ := h.bound
  refine ⟨c, hc, ?_⟩
  intro n t ht
  have hledger :
      (collisionExcess n t : ℝ) + (smoothComponentCount n t : ℝ) = t := by
    exact_mod_cast collisionExcess_add_smoothComponentCount n t
  linarith [hbound n t ht]

end MoltResearch.Erdos461
