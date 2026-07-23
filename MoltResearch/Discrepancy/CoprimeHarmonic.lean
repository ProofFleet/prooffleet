import MoltResearch.Discrepancy.SelbergGFloor
import MoltResearch.Discrepancy.MertensFloor

/-!
# Discrepancy: the coprime harmonic floor

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): restricting the harmonic sum to integers coprime to `q` costs
at most the Euler factor `∏_{p ∣ q} (1 − 1/p)` —

  `∏_{p ∣ q} (1 − 1/p) · log y ≤ ∑_{m ≤ y, (m,q)=1} 1/m`.

The proof removes one prime at a time (`Finset.induction` on the prime set):
deleting the multiples of `p` from any dvd-free harmonic filter costs a
factor `1 − 1/p`, because the removed mass reindexes along `m = p·j` into
`(1/p)`-scaled copies of the same filter. No smooth-part decomposition is
needed. Combined with the `G`-floor chain of `SelbergGFloor`, this gives
`G(R) ≥ (∏_{p∣2s}(1−1/p))² · log²(√R)` — the quantitative growth the
per-`s` Selberg bound consumes.
-/

namespace MoltResearch

open Finset

/-- **One-prime removal**: deleting the multiples of a prime `p` costs at most
a factor `1 − 1/p` on any dvd-closed harmonic filter. -/
theorem sum_one_div_filter_erase_ge {y p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (hpS : p ∉ S) :
    (1 - 1 / (p : ℝ)) * ∑ m ∈ (Finset.Icc 1 y).filter
        (fun m => ∀ r ∈ S, ¬ r ∣ m), (1 : ℝ) / m
      ≤ ∑ m ∈ (Finset.Icc 1 y).filter
        (fun m => ∀ r ∈ insert p S, ¬ r ∣ m), (1 : ℝ) / m := by
  classical
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  -- split the S-free sum by divisibility by p
  have hsplit : ∑ m ∈ (Finset.Icc 1 y).filter
      (fun m => ∀ r ∈ S, ¬ r ∣ m), (1 : ℝ) / m
      = (∑ m ∈ ((Finset.Icc 1 y).filter
          (fun m => ∀ r ∈ S, ¬ r ∣ m)).filter (fun m => p ∣ m), (1 : ℝ) / m)
        + ∑ m ∈ ((Finset.Icc 1 y).filter
          (fun m => ∀ r ∈ S, ¬ r ∣ m)).filter (fun m => ¬ p ∣ m),
          (1 : ℝ) / m :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the not-divisible part is exactly the (insert p S)-free sum
  have hnotpart : ((Finset.Icc 1 y).filter
      (fun m => ∀ r ∈ S, ¬ r ∣ m)).filter (fun m => ¬ p ∣ m)
      = (Finset.Icc 1 y).filter (fun m => ∀ r ∈ insert p S, ¬ r ∣ m) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun m _ => ?_
    constructor
    · rintro ⟨h1, h2⟩ r hr
      rcases Finset.mem_insert.mp hr with h | h
      · subst h
        exact h2
      · exact h1 r h
    · intro h1
      exact ⟨fun r hr => h1 r (Finset.mem_insert_of_mem hr),
        h1 p (Finset.mem_insert_self p S)⟩
  -- the divisible part reindexes along `m = p·j` and is at most `(1/p)·A_S`
  have hdvdpart : (∑ m ∈ ((Finset.Icc 1 y).filter
      (fun m => ∀ r ∈ S, ¬ r ∣ m)).filter (fun m => p ∣ m), (1 : ℝ) / m)
      ≤ (1 / (p : ℝ)) * ∑ m ∈ (Finset.Icc 1 y).filter
          (fun m => ∀ r ∈ S, ¬ r ∣ m), (1 : ℝ) / m := by
    have hbij : ∑ m ∈ ((Finset.Icc 1 y).filter
        (fun m => ∀ r ∈ S, ¬ r ∣ m)).filter (fun m => p ∣ m), (1 : ℝ) / m
        = ∑ j ∈ (Finset.Icc 1 (y / p)).filter
            (fun j => ∀ r ∈ S, ¬ r ∣ j), (1 : ℝ) / ((p * j : ℕ) : ℝ) := by
      refine Finset.sum_nbij' (fun m => m / p) (fun j => p * j) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        beta_reduce
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨⟨hm1, hmy⟩, hSfree⟩, hpm⟩ := hm
        rw [Finset.mem_filter, Finset.mem_Icc]
        obtain ⟨j, hj⟩ := hpm
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have hj0 : j ≠ 0 := by
            rintro rfl
            omega
          have : m / p = j := by
            rw [hj]
            exact Nat.mul_div_cancel_left j hp.pos
          omega
        · exact Nat.div_le_div_right hmy
        · intro r hr hrj
          refine hSfree r hr ?_
          exact hrj.trans (Nat.div_dvd_of_dvd ⟨j, hj⟩)
      · intro j hj
        beta_reduce
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, hjy⟩, hSfree⟩ := hj
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Dvd.intro j rfl⟩
        · exact Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero hp.pos.ne' (by omega))
        · have h10 : j * p ≤ y := (Nat.le_div_iff_mul_le hp.pos).mp hjy
          rw [Nat.mul_comm]
          exact h10
        · intro r hr hrm
          have hrp := hS r hr
          have hrne : r ≠ p := fun hc => hpS (hc ▸ hr)
          have hrj : r ∣ j := by
            rcases (Nat.Prime.dvd_mul hrp).mp hrm with h | h
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hrp hp).mp h) hrne
            · exact h
          exact hSfree r hr hrj
      · intro m hm
        beta_reduce
        rw [Finset.mem_filter] at hm
        obtain ⟨j, hj⟩ := hm.2
        rw [hj, Nat.mul_div_cancel_left j hp.pos]
      · intro j _
        beta_reduce
        exact Nat.mul_div_cancel_left j hp.pos
      · intro m hm
        beta_reduce
        rw [Finset.mem_filter] at hm
        obtain ⟨j, hj⟩ := hm.2
        rw [hj, Nat.mul_div_cancel_left j hp.pos]
    rw [hbij]
    have hper : ∀ j ∈ (Finset.Icc 1 (y / p)).filter
        (fun j => ∀ r ∈ S, ¬ r ∣ j),
        (1 : ℝ) / ((p * j : ℕ) : ℝ) = (1 / (p : ℝ)) * ((1 : ℝ) / j) := by
      intro j _
      push_cast
      rw [div_mul_div_comm, one_mul]
    rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · refine Finset.filter_subset_filter _ ?_
      refine Finset.Icc_subset_Icc le_rfl ?_
      exact Nat.div_le_self y p
    · intro j _ _
      positivity
  -- assemble
  rw [hnotpart] at hsplit
  have hA0 : (0 : ℝ) ≤ ∑ m ∈ (Finset.Icc 1 y).filter
      (fun m => ∀ r ∈ S, ¬ r ∣ m), (1 : ℝ) / m := by
    refine Finset.sum_nonneg fun m _ => ?_
    positivity
  nlinarith only [hsplit, hdvdpart, hA0, hp0]

/-- **The prime-set harmonic floor**: removing the multiples of a finite set
of primes costs at most `∏ (1 − 1/p)`. -/
theorem prod_mul_sum_le_sum_one_div_filter {y : ℕ} :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      (∏ p ∈ S, (1 - 1 / (p : ℝ))) * ∑ m ∈ Finset.Icc 1 y, (1 : ℝ) / m
      ≤ ∑ m ∈ (Finset.Icc 1 y).filter (fun m => ∀ r ∈ S, ¬ r ∣ m),
          (1 : ℝ) / m := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty, one_mul, Finset.filter_true_of_mem
      (fun m _ => fun r hr => absurd hr (Finset.notMem_empty r))]
  | insert p S hpS ih =>
    intro hprime
    have hp := hprime p (Finset.mem_insert_self p S)
    have hS : ∀ r ∈ S, r.Prime := fun r hr =>
      hprime r (Finset.mem_insert_of_mem hr)
    have hstep := sum_one_div_filter_erase_ge (y := y) hp S hS hpS
    have hfac0 : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      rw [sub_nonneg, div_le_one hp0]
      linarith
    calc (∏ r ∈ insert p S, (1 - 1 / (r : ℝ)))
        * ∑ m ∈ Finset.Icc 1 y, (1 : ℝ) / m
        = (1 - 1 / (p : ℝ)) * ((∏ r ∈ S, (1 - 1 / (r : ℝ)))
            * ∑ m ∈ Finset.Icc 1 y, (1 : ℝ) / m) := by
          rw [Finset.prod_insert hpS]
          ring
      _ ≤ (1 - 1 / (p : ℝ)) * ∑ m ∈ (Finset.Icc 1 y).filter
            (fun m => ∀ r ∈ S, ¬ r ∣ m), (1 : ℝ) / m :=
          mul_le_mul_of_nonneg_left (ih hS) hfac0
      _ ≤ ∑ m ∈ (Finset.Icc 1 y).filter
            (fun m => ∀ r ∈ insert p S, ¬ r ∣ m), (1 : ℝ) / m := hstep

/-- **The coprime harmonic floor**: the harmonic sum over `[1, y]` coprime to
`q ≠ 0` is at least `∏_{p ∣ q} (1 − 1/p) · log y`. -/
theorem log_le_sum_one_div_coprime {y q : ℕ} (hq0 : q ≠ 0) :
    (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) * Real.log y
      ≤ ∑ m ∈ (Finset.Icc 1 y).filter (fun m => Nat.Coprime m q),
          (1 : ℝ) / m := by
  classical
  have hfilter : (Finset.Icc 1 y).filter (fun m => Nat.Coprime m q)
      = (Finset.Icc 1 y).filter
        (fun m => ∀ r ∈ q.primeFactors, ¬ r ∣ m) := by
    refine Finset.filter_congr fun m _ => ?_
    constructor
    · intro hcop r hr hrm
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hrq := Nat.dvd_of_mem_primeFactors hr
      have h1 : r ∣ Nat.gcd m q := Nat.dvd_gcd hrm hrq
      rw [hcop, Nat.dvd_one] at h1
      exact hrp.one_lt.ne' h1
    · intro hfree
      by_contra hnc
      obtain ⟨r, hrp, hrm, hrq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      refine hfree r ?_ hrm
      rw [Nat.mem_primeFactors]
      exact ⟨hrp, hrq, hq0⟩
  have hprod0 : (0 : ℝ) ≤ ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    rw [sub_nonneg, div_le_one hp0]
    linarith
  have hlog : Real.log y ≤ ∑ m ∈ Finset.Icc 1 y, (1 : ℝ) / m := by
    refine le_trans (log_le_sum_one_div_Ico y) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.Ico_subset_Icc_self
    · intro m _ _
      positivity
  calc (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) * Real.log y
      ≤ (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)))
        * ∑ m ∈ Finset.Icc 1 y, (1 : ℝ) / m :=
        mul_le_mul_of_nonneg_left hlog hprod0
    _ ≤ ∑ m ∈ (Finset.Icc 1 y).filter
          (fun m => ∀ r ∈ q.primeFactors, ¬ r ∣ m), (1 : ℝ) / m :=
        prod_mul_sum_le_sum_one_div_filter q.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp)
    _ = ∑ m ∈ (Finset.Icc 1 y).filter (fun m => Nat.Coprime m q),
          (1 : ℝ) / m := by rw [hfilter]

end MoltResearch
