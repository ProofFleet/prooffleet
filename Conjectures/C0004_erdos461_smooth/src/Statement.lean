import Mathlib

/-!
# Erdős problem 461: smooth components in a short interval

This file formalizes the question on the number of distinct `t`-smooth
components among the integers in `(n, n + t]`.  The problem is recorded as
Erdős--Graham, *Old and New Problems and Results in Combinatorial Number
Theory* (1980), p. 92, and at <https://www.erdosproblems.com/461>.
-/

namespace MoltResearch.Erdos461

open Finset

/-- The part of `n` supported on prime factors strictly below `t`.

This is the smooth component used by Erdős and Graham on p. 92 of *Old and
New Problems and Results in Combinatorial Number Theory* (1980); see also
<https://www.erdosproblems.com/461>.
-/
noncomputable def smoothPart (t n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p < t), p ^ n.factorization p

/-- The number of distinct `t`-smooth components represented in `(n, n + t]`. -/
noncomputable def smoothComponentCount (n t : ℕ) : ℕ :=
  ((Finset.Ioc n (n + t)).image (smoothPart t)).card

/-- Erdős problem 461: a positive constant proportion of an interval of
length `t` should have distinct `t`-smooth components, uniformly in the
starting point.  This is the open question on
<https://www.erdosproblems.com/461>, originating in Erdős--Graham (1980),
p. 92.
-/
def Erdos461 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t → c * t ≤ smoothComponentCount n t

/-- The smooth component always divides the original integer. -/
theorem smoothPart_dvd (t n : ℕ) : smoothPart t n ∣ n := by
  classical
  by_cases hn : n = 0
  · subst n
    exact dvd_zero _
  · refine ⟨∏ p ∈ n.primeFactors.filter (fun p => ¬p < t),
      p ^ n.factorization p, ?_⟩
    unfold smoothPart
    rw [Finset.prod_filter_mul_prod_filter_not]
    have hfactor := Nat.factorization_prod_pow_eq_self hn
    rw [Nat.prod_factorization_eq_prod_primeFactors] at hfactor
    exact hfactor.symm

/-- A nonzero integer all of whose prime factors are below `t` is its own
`t`-smooth component. -/
theorem smoothPart_eq_self {t n : ℕ} (hn : n ≠ 0)
    (hsmooth : ∀ p ∈ n.primeFactors, p < t) : smoothPart t n = n := by
  classical
  unfold smoothPart
  rw [Finset.filter_eq_self.mpr hsmooth]
  have hfactor := Nat.factorization_prod_pow_eq_self hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hfactor
  exact hfactor

/-- Every positive integer strictly below `t` is fixed by `smoothPart t`. -/
theorem smoothPart_eq_self_of_lt {t n : ℕ} (hn : 0 < n) (hnt : n < t) :
    smoothPart t n = n := by
  apply smoothPart_eq_self hn.ne'
  intro p hp
  exact lt_of_le_of_lt (Nat.le_of_mem_primeFactors hp) hnt

/-- Taking an image cannot produce more than the `t` integers in the
interval. -/
theorem smoothComponentCount_le (n t : ℕ) : smoothComponentCount n t ≤ t := by
  classical
  calc
    smoothComponentCount n t ≤ (Finset.Ioc n (n + t)).card := by
      exact Finset.card_image_le
    _ = t := by simp

/-- At the origin the only collision occurs when `t` itself is prime: its
smooth component is `1`, which is already represented by `1`.
-/
theorem smoothComponentCount_zero (t : ℕ) (ht : 2 ≤ t) :
    smoothComponentCount 0 t = if t.Prime then t - 1 else t := by
  classical
  by_cases hprime : t.Prime
  · rw [if_pos hprime]
    have htop : smoothPart t t = 1 := by
      simp [smoothPart, hprime.primeFactors]
    have himage :
        (Finset.Ioc 0 t).image (smoothPart t) = Finset.Ioc 0 (t - 1) := by
      ext x
      constructor
      · intro hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_Ioc] at hm ⊢
        by_cases hmt : m = t
        · subst m
          rw [htop]
          omega
        · rw [smoothPart_eq_self_of_lt hm.1 (lt_of_le_of_ne hm.2 hmt)]
          omega
      · intro hx
        rw [Finset.mem_Ioc] at hx
        apply Finset.mem_image.mpr
        refine ⟨x, ?_, ?_⟩
        · rw [Finset.mem_Ioc]
          omega
        · exact smoothPart_eq_self_of_lt hx.1 (by omega)
    rw [smoothComponentCount, zero_add, himage]
    simp
  · rw [if_neg hprime]
    have hfixed : ∀ m ∈ Finset.Ioc 0 t, smoothPart t m = m := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      apply smoothPart_eq_self hm.1.ne'
      intro p hp
      have hp_le : p ≤ t := (Nat.le_of_mem_primeFactors hp).trans hm.2
      have hp_ne : p ≠ t := by
        intro hpt
        apply hprime
        simpa [hpt] using Nat.prime_of_mem_primeFactors hp
      omega
    have himage :
        (Finset.Ioc 0 t).image (smoothPart t) = Finset.Ioc 0 t := by
      calc
        (Finset.Ioc 0 t).image (smoothPart t) =
            (Finset.Ioc 0 t).image id := by
              apply Finset.image_congr
              intro m hm
              simpa using hfixed m hm
        _ = Finset.Ioc 0 t := Finset.image_id
    rw [smoothComponentCount, zero_add, himage]
    simp

end MoltResearch.Erdos461
