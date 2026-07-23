import MoltResearch.Discrepancy.SelbergWeights
import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Discrepancy: the `G`-floor of the Selberg sieve

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the lower bound machinery for the truncated Selberg mass
`G(R) = ∑_{k ∣ P, k ≤ R} h(k)`.

The chain, fully elementary:

- `sum_geom_weight_le` — the per-prime bound `∑_{a≥1} (a+1)/q^a ≤ 2/(q−2)`
  for odd `q` (via `(a+1) ≤ 2^a` and the closed-form geometric sum);
- `sum_fiber_div_le` — the radical-fiber collapse
  `∑_{n ≤ R, rad(n)=k} d(n)/n ≤ ∏_{p∣k} 2/(p−2)`, by peeling the least
  prime with the `ordProj`/`ordCompl` decomposition and dominating by the
  product rectangle;
- `selbergG_ge_sum_div` — the floor `G(R) ≥ ∑ d(n)/n` over `n ≤ R` coprime
  to `2s` and supported on the sifting primes (the `ρ(p) = 2` bridge);
- `sq_sum_one_div_le_sum_div` — the divisor-pairs square
  `(∑_{m ≤ √R} 1/m)² ≤ ∑ d(n)/n`.

Composed: `G(R) ≥ (∑_{m ≤ √R, (m,2s)=1} 1/m)²` — the coprime harmonic floor
(next unit) then produces the `log²R` growth against the singular series.
-/

namespace MoltResearch

open Finset

/-- `a + 1 ≤ 2^a` for `a ≥ 1`. -/
theorem succ_le_two_pow' {a : ℕ} (ha : 1 ≤ a) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0
      norm_num
    · have h2 := ih h1
      have h3 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-- **The per-prime divisor-weighted geometric bound**: for an odd sifting
prime with two removed residues, the truncated series of `(a+1)/q^a` stays
below `h(q) = 2/(q−2)`. -/
theorem sum_geom_weight_le {q R : ℕ} (hq : 3 ≤ q) :
    ∑ a ∈ Finset.Icc 1 R, ((a : ℝ) + 1) / (q : ℝ) ^ a
      ≤ 2 / ((q : ℝ) - 2) := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hx0 : (0 : ℝ) < 2 / (q : ℝ) := by positivity
  have hx1 : 2 / (q : ℝ) < 1 := by
    rw [div_lt_one hq0]
    linarith
  have hper : ∀ a ∈ Finset.Icc 1 R,
      ((a : ℝ) + 1) / (q : ℝ) ^ a ≤ (2 / (q : ℝ)) ^ a := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have h2a : ((a : ℝ) + 1) ≤ 2 ^ a := by
      exact_mod_cast succ_le_two_pow' ha.1
    rw [div_pow]
    gcongr
  refine le_trans (Finset.sum_le_sum hper) ?_
  have hins : Finset.range (R + 1) = insert 0 (Finset.Icc 1 R) := by
    ext a
    rw [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsplit : ∑ a ∈ Finset.range (R + 1), (2 / (q : ℝ)) ^ a
      = 1 + ∑ a ∈ Finset.Icc 1 R, (2 / (q : ℝ)) ^ a := by
    rw [hins, Finset.sum_insert (by
      rw [Finset.mem_Icc]
      omega), pow_zero]
  have hgeom : ∑ i ∈ Finset.range (R + 1), (2 / (q : ℝ)) ^ i
      ≤ (1 - 2 / (q : ℝ))⁻¹ := by
    rw [geom_sum_eq (ne_of_lt hx1) (R + 1)]
    have hxn : (0 : ℝ) ≤ (2 / (q : ℝ)) ^ (R + 1) := by positivity
    have h1x : (0 : ℝ) < 1 - 2 / (q : ℝ) := by linarith
    have hflip : ((2 / (q : ℝ)) ^ (R + 1) - 1) / ((2 / (q : ℝ)) - 1)
        = (1 - (2 / (q : ℝ)) ^ (R + 1)) / (1 - 2 / (q : ℝ)) := by
      rw [← neg_sub ((1 : ℝ)) ((2 / (q : ℝ)) ^ (R + 1)),
        ← neg_sub ((1 : ℝ)) (2 / (q : ℝ)), neg_div_neg_eq]
    rw [hflip, inv_eq_one_div]
    gcongr
    linarith
  have hinv : (1 - 2 / (q : ℝ))⁻¹ - 1 = 2 / ((q : ℝ) - 2) := by
    have h1 : (1 : ℝ) - 2 / (q : ℝ) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun hc => absurd hc.symm (ne_of_lt hx1)
    have h2 : (q : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  linarith [hsplit.le, hsplit.ge, hgeom, hinv.le, hinv.ge]

/-- The radical: the squarefree kernel of `n`. -/
def radN (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem radN_dvd {n : ℕ} : radN n ∣ n :=
  Finset.prod_primes_dvd n
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
    (fun p hp => Nat.dvd_of_mem_primeFactors hp)

theorem primeFactors_radN (n : ℕ) : (radN n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp

/-- **The fiber bound**: over the fiber of a squarefree odd-prime kernel `k`,
the divisor-weighted harmonic mass is at most `∏_{p ∣ k} 2/(p−2)`. -/
theorem sum_fiber_div_le {R : ℕ} :
    ∀ k : ℕ, Squarefree k → (∀ p ∈ k.primeFactors, 3 ≤ p) →
      ∑ n ∈ (Finset.range (R + 1)).filter
          (fun n => 0 < n ∧ radN n = k),
        ((n.divisors.card : ℝ) / n)
      ≤ ∏ p ∈ k.primeFactors, (2 / ((p : ℝ) - 2)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h3
    rcases eq_or_ne k 1 with h1 | h1
    · subst h1
      have hsub : (Finset.range (R + 1)).filter
          (fun n => 0 < n ∧ radN n = 1) ⊆ {1} := by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨-, hn0, hrad⟩ := hn
        rw [Finset.mem_singleton]
        have hpf : n.primeFactors = ∅ := by
          have h2 := primeFactors_radN n
          rw [hrad, Nat.primeFactors_one] at h2
          exact h2.symm
        rcases Nat.primeFactors_eq_empty.mp hpf with h | h
        · omega
        · exact h
      have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun n : ℕ => ((n.divisors.card : ℝ) / n))
        (fun n _ _ => by positivity)
      rw [Nat.primeFactors_one, Finset.prod_empty]
      refine le_trans hbound ?_
      rw [Finset.sum_singleton, Nat.divisors_one]
      norm_num
    · -- peel the least prime factor
      have hk0 : k ≠ 0 := hk.ne_zero
      have hq := Nat.minFac_prime h1
      set q := k.minFac with hq_def
      obtain ⟨k', hk'⟩ := k.minFac_dvd
      rw [← hq_def] at hk'
      have hk'0 : k' ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at hk'
        exact hk0 hk'
      have hk'lt : k' < k := by
        rw [hk']
        have h2 := hq.two_le
        have h3' : 0 < k' := Nat.pos_of_ne_zero hk'0
        calc k' = 1 * k' := (one_mul k').symm
          _ < q * k' := Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl h3'
      have hsq' : Squarefree k' :=
        Squarefree.squarefree_of_dvd ⟨q, by rw [hk']; ring⟩ hk
      have hqk' : ¬ q ∣ k' := by
        intro hc
        obtain ⟨e, he⟩ := hc
        have hqq : q * q ∣ k := ⟨e, by rw [hk', he]; ring⟩
        have hunit := hk q hqq
        rw [Nat.isUnit_iff] at hunit
        exact hq.one_lt.ne' hunit
      have hmemq : q ∈ k.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hq, k.minFac_dvd, hk0⟩
      have hq3 : 3 ≤ q := h3 q hmemq
      have hpfk : k.primeFactors = insert q k'.primeFactors := by
        rw [hk', Nat.primeFactors_mul (hq.pos.ne') hk'0,
          Nat.Prime.primeFactors hq, Finset.singleton_union]
      have hqnotin : q ∉ k'.primeFactors := fun hc =>
        hqk' (Nat.dvd_of_mem_primeFactors hc)
      have h3'' : ∀ p ∈ k'.primeFactors, 3 ≤ p := by
        intro p hp
        refine h3 p ?_
        rw [hpfk]
        exact Finset.mem_insert_of_mem hp
      -- per-element facts on the fiber
      have hfacts : ∀ n ∈ (Finset.range (R + 1)).filter
          (fun n => 0 < n ∧ radN n = k),
          1 ≤ n.factorization q ∧ n.factorization q ≤ R
          ∧ 0 < ordCompl[q] n ∧ ordCompl[q] n < R + 1
          ∧ radN (ordCompl[q] n) = k'
          ∧ n = q ^ n.factorization q * ordCompl[q] n
          ∧ (n.divisors.card : ℝ)
            = ((n.factorization q : ℝ) + 1) * ((ordCompl[q] n).divisors.card : ℝ) := by
        intro n hn
        rw [Finset.mem_filter, Finset.mem_range] at hn
        obtain ⟨hnR, hn0, hrad⟩ := hn
        have hn0' : n ≠ 0 := hn0.ne'
        have hqn : q ∣ n := by
          have h4 : q ∣ radN n := by
            rw [hrad, hk']
            exact dvd_mul_right q k'
          exact h4.trans radN_dvd
        have ha1 : 1 ≤ n.factorization q :=
          Nat.Prime.factorization_pos_of_dvd hq hn0' hqn
        have hrecon := Nat.ordProj_mul_ordCompl_eq_self n q
        have hqa_dvd : q ^ n.factorization q ∣ n := Nat.ordProj_dvd n q
        have haR : n.factorization q ≤ R := by
          have h5 : n.factorization q + 1 ≤ 2 ^ n.factorization q :=
            succ_le_two_pow' ha1
          have h6 : 2 ^ n.factorization q ≤ q ^ n.factorization q :=
            Nat.pow_le_pow_left hq.two_le _
          have h7 : q ^ n.factorization q ≤ n := Nat.le_of_dvd hn0 hqa_dvd
          omega
        have hm0 : 0 < ordCompl[q] n := Nat.ordCompl_pos q hn0'
        have hmR : ordCompl[q] n < R + 1 :=
          Nat.lt_succ_of_le (le_trans
            (Nat.le_of_dvd hn0 (Nat.ordCompl_dvd n q)) (by omega))
        have hqm : ¬ q ∣ ordCompl[q] n := Nat.not_dvd_ordCompl hq hn0'
        have hqm_notin : q ∉ (ordCompl[q] n).primeFactors := fun hc =>
          hqm (Nat.dvd_of_mem_primeFactors hc)
        have hpfn : n.primeFactors
            = insert q ((ordCompl[q] n).primeFactors) := by
          conv_lhs => rw [← hrecon]
          rw [Nat.primeFactors_mul (pow_ne_zero _ hq.pos.ne') hm0.ne',
            Nat.primeFactors_prime_pow (Nat.one_le_iff_ne_zero.mp ha1) hq,
            Finset.singleton_union]
        have hradm : radN (ordCompl[q] n) = k' := by
          have h8 : radN n = q * radN (ordCompl[q] n) := by
            rw [radN, radN, hpfn, Finset.prod_insert hqm_notin]
          rw [hrad, hk'] at h8
          exact (Nat.eq_of_mul_eq_mul_left hq.pos h8).symm
        have hcop : Nat.Coprime (q ^ n.factorization q) (ordCompl[q] n) :=
          Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm)
        have hdmul : n.divisors.card
            = (n.factorization q + 1) * (ordCompl[q] n).divisors.card := by
          calc n.divisors.card
              = ((q ^ n.factorization q) * (ordCompl[q] n)).divisors.card := by
                rw [hrecon]
            _ = (q ^ n.factorization q).divisors.card
                * (ordCompl[q] n).divisors.card :=
                Nat.Coprime.card_divisors_mul hcop
            _ = (n.factorization q + 1) * (ordCompl[q] n).divisors.card := by
                rw [Nat.divisors_prime_pow hq, Finset.card_map,
                  Finset.card_range]
        refine ⟨ha1, haR, hm0, hmR, hradm, hrecon.symm, ?_⟩
        rw [hdmul]
        push_cast
        ring
      -- compare with the product over the rectangle
      -- compare with the product over the rectangle
      have hval : ∀ n ∈ (Finset.range (R + 1)).filter
          (fun n => 0 < n ∧ radN n = k),
          ((n.divisors.card : ℝ) / n)
          = (((n.factorization q : ℝ) + 1) / (q : ℝ) ^ n.factorization q)
            * (((ordCompl[q] n).divisors.card : ℝ) / ((ordCompl[q] n : ℕ) : ℝ)) := by
        intro n hn
        obtain ⟨-, -, hm0, -, -, hrecon, hd⟩ := hfacts n hn
        rw [hd]
        have hnR : (n : ℝ) = (q : ℝ) ^ n.factorization q
            * ((ordCompl[q] n : ℕ) : ℝ) := by
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hrecon
        rw [hnR]
        have hq0R : ((q : ℝ)) ≠ 0 := by
          have := hq.pos
          positivity
        have hqf0 : ((q : ℝ)) ^ n.factorization q ≠ 0 := pow_ne_zero _ hq0R
        have hm0R : (((ordCompl[q] n : ℕ)) : ℝ) ≠ 0 := by
          exact_mod_cast hm0.ne'
        field_simp
      rw [Finset.sum_congr rfl hval]
      have hinj : Set.InjOn (fun n : ℕ => (n.factorization q, ordCompl[q] n))
          ((Finset.range (R + 1)).filter (fun n => 0 < n ∧ radN n = k)) := by
        intro n hn n' hn' heq
        rw [Finset.mem_coe] at hn hn'
        obtain ⟨-, -, -, -, -, hrecon, -⟩ := hfacts n hn
        obtain ⟨-, -, -, -, -, hrecon', -⟩ := hfacts n' hn'
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        simp only at h1 h2
        rw [hrecon, hrecon', h2, h1]
      have himg_eq : ∑ pr ∈ ((Finset.range (R + 1)).filter
            (fun n => 0 < n ∧ radN n = k)).image
              (fun n : ℕ => (n.factorization q, ordCompl[q] n)),
          (((pr.1 : ℝ) + 1) / (q : ℝ) ^ pr.1)
            * (((pr.2.divisors.card : ℝ)) / (pr.2 : ℝ))
          = ∑ n ∈ (Finset.range (R + 1)).filter
              (fun n => 0 < n ∧ radN n = k),
            (((n.factorization q : ℝ) + 1) / (q : ℝ) ^ n.factorization q)
              * (((ordCompl[q] n).divisors.card : ℝ) / ((ordCompl[q] n : ℕ) : ℝ)) := by
        rw [Finset.sum_image hinj]
      have himage : ∑ n ∈ (Finset.range (R + 1)).filter
          (fun n => 0 < n ∧ radN n = k),
          (((n.factorization q : ℝ) + 1) / (q : ℝ) ^ n.factorization q)
            * (((ordCompl[q] n).divisors.card : ℝ) / ((ordCompl[q] n : ℕ) : ℝ))
          ≤ ∑ pr ∈ (Finset.Icc 1 R) ×ˢ ((Finset.range (R + 1)).filter
              (fun m => 0 < m ∧ radN m = k')),
            (((pr.1 : ℝ) + 1) / (q : ℝ) ^ pr.1)
              * (((pr.2.divisors.card : ℝ)) / (pr.2 : ℝ)) := by
        rw [← himg_eq]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro pr hpr
          rw [Finset.mem_image] at hpr
          obtain ⟨n, hn, hpr'⟩ := hpr
          obtain ⟨ha1, haR, hm0, hmR, hradm, -, -⟩ := hfacts n hn
          subst hpr'
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_filter,
            Finset.mem_range]
          exact ⟨⟨ha1, haR⟩, hmR, hm0, hradm⟩
        · intro pr _ _
          exact mul_nonneg (by positivity)
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      refine le_trans himage ?_
      rw [Finset.sum_product]
      have hfactor : ∑ a ∈ Finset.Icc 1 R,
          ∑ m ∈ (Finset.range (R + 1)).filter
            (fun m => 0 < m ∧ radN m = k'),
          (((a : ℝ) + 1) / (q : ℝ) ^ a)
            * (((m.divisors.card : ℝ)) / (m : ℝ))
          = (∑ a ∈ Finset.Icc 1 R, ((a : ℝ) + 1) / (q : ℝ) ^ a)
            * ∑ m ∈ (Finset.range (R + 1)).filter
              (fun m => 0 < m ∧ radN m = k'),
              ((m.divisors.card : ℝ) / (m : ℝ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
      rw [hfactor, hpfk, Finset.prod_insert hqnotin]
      have hsum0 : (0 : ℝ) ≤ ∑ m ∈ (Finset.range (R + 1)).filter
          (fun m => 0 < m ∧ radN m = k'),
          ((m.divisors.card : ℝ) / (m : ℝ)) := by
        refine Finset.sum_nonneg fun m _ => ?_
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hgeom0 : (0 : ℝ) ≤ 2 / ((q : ℝ) - 2) := by
        have h9 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
        exact div_nonneg (by norm_num) (by linarith)
      exact mul_le_mul (sum_geom_weight_le hq3) (ih k' hk'lt hsq' h3'')
        hsum0 hgeom0

/-- **The `G`-floor, collapse form**: the truncated Selberg mass dominates the
divisor-weighted harmonic sum over integers coprime to `2s` and supported on
the sifting primes. -/
theorem selbergG_ge_sum_div {s P R : ℕ} (hP : Squarefree P)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p) :
    ∑ n ∈ (Finset.range (R + 1)).filter
        (fun n => 0 < n ∧ Nat.Coprime n (2 * s)
          ∧ ∀ p ∈ n.primeFactors, p ∈ P.primeFactors),
      ((n.divisors.card : ℝ) / n)
    ≤ selbergG s P R := by
  classical
  have hmaps : ∀ n ∈ (Finset.range (R + 1)).filter
      (fun n => 0 < n ∧ Nat.Coprime n (2 * s)
        ∧ ∀ p ∈ n.primeFactors, p ∈ P.primeFactors),
      radN n ∈ ((P.divisors.filter (fun k => k ≤ R)).filter
        (fun k => Nat.Coprime k (2 * s))) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnR, hn0, hcop, hsupp⟩ := hn
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨?_, hP.ne_zero⟩, ?_⟩, ?_⟩
    · exact Finset.prod_primes_dvd P
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
        (fun p hp => Nat.dvd_of_mem_primeFactors (hsupp p hp))
    · exact le_trans (Nat.le_of_dvd hn0 radN_dvd) (by omega)
    · exact Nat.Coprime.coprime_dvd_left radN_dvd hcop
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n : ℕ => ((n.divisors.card : ℝ) / n))]
  -- per fiber: dominate by the full radical fiber, then by `h(k)`
  have hper : ∀ k ∈ ((P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => Nat.Coprime k (2 * s))),
      ∑ n ∈ ((Finset.range (R + 1)).filter
          (fun n => 0 < n ∧ Nat.Coprime n (2 * s)
            ∧ ∀ p ∈ n.primeFactors, p ∈ P.primeFactors)).filter
        (fun n => radN n = k),
        ((n.divisors.card : ℝ) / n)
      ≤ ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors] at hk
    obtain ⟨⟨⟨hkP, -⟩, hkR⟩, hkcop⟩ := hk
    have hsqk : Squarefree k := hP.squarefree_of_dvd hkP
    have hk3 : ∀ p ∈ k.primeFactors, 3 ≤ p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpdvd := Nat.dvd_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        intro hc
        subst hc
        have h2 : (2 : ℕ) ∣ 2 * s := dvd_mul_right 2 s
        have h3 : (2 : ℕ) ∣ Nat.gcd k (2 * s) := Nat.dvd_gcd hpdvd h2
        rw [hkcop] at h3
        omega
      have := hpp.two_le
      omega
    have hsub : ((Finset.range (R + 1)).filter
        (fun n => 0 < n ∧ Nat.Coprime n (2 * s)
          ∧ ∀ p ∈ n.primeFactors, p ∈ P.primeFactors)).filter
        (fun n => radN n = k)
        ⊆ (Finset.range (R + 1)).filter (fun n => 0 < n ∧ radN n = k) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
    have hstep := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun n : ℕ => ((n.divisors.card : ℝ) / n))
      (fun n _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    refine le_trans hstep (le_trans (sum_fiber_div_le k hsqk hk3) ?_)
    -- the bridge: with `ρ(p) = 2` on the primes of `k`, the products agree
    refine le_of_eq (Finset.prod_congr rfl fun p hp => ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hps : ¬ p ∣ s := by
      intro hc
      have h2 : p ∣ 2 * s := Dvd.dvd.mul_left hc 2
      have h3 : p ∣ Nat.gcd k (2 * s) := Nat.dvd_gcd hpdvd h2
      rw [hkcop, Nat.dvd_one] at h3
      have := hpp.two_le
      omega
    rw [sieveRootCard_prime hpp, if_neg hps]
    norm_num
  refine le_trans (Finset.sum_le_sum hper) ?_
  -- fill the missing divisors with nonnegative `h`-mass
  rw [selbergG]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro k hk _
  exact (selberg_h_pos hP hρlt k (Finset.mem_filter.mp hk).1).le

/-- **The divisor-pairs square**: the divisor-weighted harmonic mass dominates
the square of the restricted harmonic sum up to `√R`. -/
theorem sq_sum_one_div_le_sum_div {s P R m₀ : ℕ} (hm₀ : m₀ * m₀ ≤ R) :
    (∑ m ∈ (Finset.Icc 1 m₀).filter
        (fun m => Nat.Coprime m (2 * s)
          ∧ ∀ p ∈ m.primeFactors, p ∈ P.primeFactors),
      (1 : ℝ) / m) ^ 2
    ≤ ∑ n ∈ (Finset.range (R + 1)).filter
        (fun n => 0 < n ∧ Nat.Coprime n (2 * s)
          ∧ ∀ p ∈ n.primeFactors, p ∈ P.primeFactors),
      ((n.divisors.card : ℝ) / n) := by
  classical
  set M := (Finset.Icc 1 m₀).filter
    (fun m => Nat.Coprime m (2 * s)
      ∧ ∀ p ∈ m.primeFactors, p ∈ P.primeFactors) with hM_def
  have hMfacts : ∀ m ∈ M, 1 ≤ m ∧ m ≤ m₀ ∧ Nat.Coprime m (2 * s)
      ∧ ∀ p ∈ m.primeFactors, p ∈ P.primeFactors := by
    intro m hm
    rw [hM_def, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2.1, hm.2.2⟩
  have hexpand : (∑ m ∈ M, (1 : ℝ) / m) ^ 2
      = ∑ pr ∈ M ×ˢ M, (1 : ℝ) / ((pr.1 * pr.2 : ℕ) : ℝ) := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun pr _ => ?_
    rw [div_mul_div_comm, one_mul, Nat.cast_mul]
  rw [hexpand]
  have hmaps : ∀ pr ∈ M ×ˢ M, pr.1 * pr.2
      ∈ (Finset.range (R + 1)).filter
        (fun n => 0 < n ∧ Nat.Coprime n (2 * s)
          ∧ ∀ p ∈ n.primeFactors, p ∈ P.primeFactors) := by
    intro pr hpr
    rw [Finset.mem_product] at hpr
    obtain ⟨h1, h2, h3, h4⟩ := hMfacts pr.1 hpr.1
    obtain ⟨h5, h6, h7, h8⟩ := hMfacts pr.2 hpr.2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Nat.mul_pos (by omega) (by omega),
      Nat.coprime_mul_iff_left.mpr ⟨h3, h7⟩, ?_⟩
    · have h9 : pr.1 * pr.2 ≤ m₀ * m₀ := Nat.mul_le_mul h2 h6
      omega
    · intro p hp
      rw [Nat.primeFactors_mul (by omega) (by omega),
        Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact h4 p hp
      · exact h8 p hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun pr : ℕ × ℕ => (1 : ℝ) / ((pr.1 * pr.2 : ℕ) : ℝ))]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hnR, hn0, -, -⟩ := hn
  have hconst : ∀ pr ∈ (M ×ˢ M).filter (fun pr => pr.1 * pr.2 = n),
      (1 : ℝ) / ((pr.1 * pr.2 : ℕ) : ℝ) = (1 : ℝ) / (n : ℝ) := by
    intro pr hpr
    rw [Finset.mem_filter] at hpr
    rw [hpr.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((M ×ˢ M).filter (fun pr => pr.1 * pr.2 = n)).card
      ≤ n.divisors.card := by
    refine Finset.card_le_card_of_injOn (fun pr => pr.1) ?_ ?_
    · intro pr hpr
      rw [Finset.mem_coe, Finset.mem_filter] at hpr
      show pr.1 ∈ ↑n.divisors
      rw [Nat.mem_divisors]
      exact ⟨⟨pr.2, hpr.2.symm⟩, hn0.ne'⟩
    · intro pr hpr pr' hpr' heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpr hpr'
      have h1 : pr.1 = pr'.1 := heq
      obtain ⟨hg1, -, -, -⟩ := hMfacts pr.1 hpr.1.1
      have h2 : pr.1 * pr.2 = pr.1 * pr'.2 := by
        calc pr.1 * pr.2 = n := hpr.2
          _ = pr'.1 * pr'.2 := hpr'.2.symm
          _ = pr.1 * pr'.2 := by rw [h1]
      have h3 : pr.2 = pr'.2 :=
        Nat.eq_of_mul_eq_mul_left (by omega) h2
      exact Prod.ext h1 h3
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  calc (((M ×ˢ M).filter (fun pr => pr.1 * pr.2 = n)).card : ℝ)
      * ((1 : ℝ) / (n : ℝ))
      ≤ (n.divisors.card : ℝ) * ((1 : ℝ) / (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcard
    _ = (n.divisors.card : ℝ) / n := by ring

end MoltResearch
