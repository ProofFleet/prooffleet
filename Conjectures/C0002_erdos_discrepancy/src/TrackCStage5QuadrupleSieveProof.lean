import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Assembly
import MoltResearch.Discrepancy.SingularMoment

/-!
# Track C: the quadruple sieve — `PrimeQuadrupleCountAssumption` discharged (Track S of #3004)

The Track-S campaign, assembled: the additive-quadruple count fibers over the
common sum,

  `Q(n₀) = ∑_{s ∈ (2n₀, 4n₀]} r(s)²`,

where `r(s) = blockRep n₀ s` is the number of ordered pairs of block primes
with sum `s`. Per even target `s`, the Selberg Λ² upper bound with the
primorial modulus at sift level `z = ⌊√√√√n₀⌋` (`card_sift_le_primorial_master`,
S8) combined with the `G`-floor (S6), the divisor-pairs square (S6), and the
coprime harmonic floor (S7) gives

  `r(s) ≤ 4096·n₀·σ(s)/log²n₀ + √n₀`,   `σ(s) = ∏_{p ∣ 2s} (1 − 1/p)⁻¹`,

(`blockRep_le_of_even`); odd targets contribute nothing. Summing the squares
via the singular-series second moment `∑ σ(s)² ≤ 12e³⁰·n₀` (S9) and the
elementary numerics `4·log⁴n ≤ n` beyond `2²⁸` yields

  `Q(n₀) ≤ 2⁴⁰·e³⁰ · n₀³ / log⁴n₀`  for `n₀ ≥ 2³²⁰`,

while the trivial bound `Q ≤ 2n₀³` disposes of the sub-threshold regime. The
file closes with `instance : PrimeQuadrupleCountAssumption` — the assumption
holds unconditionally, with standard axioms only.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The representation count: ordered pairs of block primes with sum `s`. -/
noncomputable def blockRep (n₀ s : ℕ) : ℕ :=
  ((primeBlock n₀ ×ˢ primeBlock n₀).filter (fun q => q.1 + q.2 = s)).card

/-- The block cardinality is at most `n₀` (the trivial interval bound). -/
theorem card_primeBlock_le_self (n₀ : ℕ) : (primeBlock n₀).card ≤ n₀ := by
  have hsub : primeBlock n₀ ⊆ Finset.Ioc n₀ (2 * n₀) := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_primeBlock hp
    exact Finset.mem_Ioc.mpr ⟨h1, h2⟩
  calc (primeBlock n₀).card ≤ (Finset.Ioc n₀ (2 * n₀)).card :=
      Finset.card_le_card hsub
    _ = n₀ := by rw [Nat.card_Ioc]; omega

/-- The representation count is at most the block size: the first coordinate
determines the pair. -/
theorem blockRep_le_card (n₀ s : ℕ) : blockRep n₀ s ≤ (primeBlock n₀).card := by
  classical
  rw [blockRep]
  have hinj : ∀ q ∈ (primeBlock n₀ ×ˢ primeBlock n₀).filter
      (fun q => q.1 + q.2 = s), Prod.fst q ∈ primeBlock n₀ := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    exact hq.1.1
  refine Finset.card_le_card_of_injOn Prod.fst hinj ?_
  intro q₁ hq₁ q₂ hq₂ hfst
  rw [Finset.mem_coe, Finset.mem_filter] at hq₁ hq₂
  have h1 := hq₁.2
  have h2 := hq₂.2
  ext
  · exact hfst
  · omega

/-- The trivial representation bound. -/
theorem blockRep_le (n₀ s : ℕ) : blockRep n₀ s ≤ n₀ :=
  le_trans (blockRep_le_card n₀ s) (card_primeBlock_le_self n₀)

/-- Sums of two block primes land in `(2n₀, 4n₀]`. -/
theorem blockRep_eq_zero_of_notMem {n₀ s : ℕ}
    (hs : s ∉ Finset.Ioc (2 * n₀) (4 * n₀)) : blockRep n₀ s = 0 := by
  classical
  rw [blockRep, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  rw [Finset.mem_product] at hq
  obtain ⟨h1, h2, h3⟩ := mem_primeBlock hq.1
  obtain ⟨h4, h5, h6⟩ := mem_primeBlock hq.2
  intro hsum
  exact hs (Finset.mem_Ioc.mpr (by omega))

/-- **The fibering identity**: the additive-quadruple count is the second
moment of the representation function over the dyadic sum window. -/
theorem card_quadruple_eq_sum_blockRep_sq (n₀ : ℕ) :
    (((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card
    = ∑ s ∈ Finset.Ioc (2 * n₀) (4 * n₀), blockRep n₀ s ^ 2 := by
  classical
  -- expand the filtered product as a double sum of indicators
  rw [Finset.card_filter, Finset.sum_product]
  -- the inner sum over the second pair is the representation count at the sum
  have hinner : ∀ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      (∑ y ∈ primeBlock n₀ ×ˢ primeBlock n₀,
        if x.1 + x.2 = y.1 + y.2 then 1 else 0) = blockRep n₀ (x.1 + x.2) := by
    intro x _
    rw [blockRep, Finset.card_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : y.1 + y.2 = x.1 + x.2
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hc => h hc.symm), if_neg h]
  rw [Finset.sum_congr rfl hinner]
  -- fiber the outer sum over the value of the pair sum
  have hmaps : ∀ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      x.1 + x.2 ∈ Finset.Ioc (2 * n₀) (4 * n₀) := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨-, h1, h2⟩ := mem_primeBlock hx.1
    obtain ⟨-, h3, h4⟩ := mem_primeBlock hx.2
    exact Finset.mem_Ioc.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => blockRep n₀ (x.1 + x.2))]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- on each fiber the summand is constant `blockRep n₀ s`, and the fiber has
  -- `blockRep n₀ s` elements
  have hconst : ∀ x ∈ (primeBlock n₀ ×ˢ primeBlock n₀).filter
      (fun x => x.1 + x.2 = s), blockRep n₀ (x.1 + x.2) = blockRep n₀ s := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, ← blockRep,
    smul_eq_mul, sq]

/-- **The trivial quadruple bound** `Q ≤ 2·n₀³`: disposes of any fixed
threshold regime by enlarging the constant, so the sieve only has to win for
large `n₀`. -/
theorem card_quadruple_le_cube (n₀ : ℕ) :
    (((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card ≤ 2 * n₀ ^ 3 := by
  classical
  rw [card_quadruple_eq_sum_blockRep_sq]
  have hcard : (Finset.Ioc (2 * n₀) (4 * n₀)).card = 2 * n₀ := by
    rw [Nat.card_Ioc]
    omega
  calc ∑ s ∈ Finset.Ioc (2 * n₀) (4 * n₀), blockRep n₀ s ^ 2
      ≤ ∑ _s ∈ Finset.Ioc (2 * n₀) (4 * n₀), n₀ ^ 2 := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact Nat.pow_le_pow_left (blockRep_le n₀ s) 2
    _ = (Finset.Ioc (2 * n₀) (4 * n₀)).card * n₀ ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * n₀ ^ 3 := by
        rw [hcard]
        ring

/-- Block primes are odd for `n₀ ≥ 2`. -/
theorem two_lt_of_mem_primeBlock {n₀ p : ℕ} (hn₀ : 2 ≤ n₀)
    (hp : p ∈ primeBlock n₀) : 2 < p := by
  obtain ⟨hpp, h1, h2⟩ := mem_primeBlock hp
  omega

/-- Odd targets have no block-pair representations. -/
theorem blockRep_eq_zero_of_odd {n₀ s : ℕ} (hn₀ : 2 ≤ n₀)
    (hs : ¬ 2 ∣ s) : blockRep n₀ s = 0 := by
  classical
  rw [blockRep, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  rw [Finset.mem_product] at hq
  obtain ⟨hpp₁, -, -⟩ := mem_primeBlock hq.1
  obtain ⟨hpp₂, -, -⟩ := mem_primeBlock hq.2
  have h₁ := two_lt_of_mem_primeBlock hn₀ hq.1
  have h₂ := two_lt_of_mem_primeBlock hn₀ hq.2
  have hodd₁ : ¬ 2 ∣ q.1 := fun hc =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp₁).mp hc)
      (by omega)
  have hodd₂ : ¬ 2 ∣ q.2 := fun hc =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp₂).mp hc)
      (by omega)
  intro hsum
  refine hs ?_
  rw [← hsum]
  omega

/-- **The sift domination**: block pairs summing to `s` inject into the
sifted window, provided the sift level sits below the block. -/
theorem blockRep_le_sift {n₀ s z : ℕ} (hz : z < n₀) :
    blockRep n₀ s
      ≤ ((Finset.Ioc n₀ (n₀ + n₀)).filter (fun n : ℕ =>
          ∀ p ∈ (primorial z).primeFactors,
            ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))))).card := by
  classical
  rw [blockRep]
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hq₁, hq₂⟩, hsum⟩ := hq
    obtain ⟨hpp₁, hlt₁, hle₁⟩ := mem_primeBlock hq₁
    obtain ⟨hpp₂, hlt₂, hle₂⟩ := mem_primeBlock hq₂
    show q.1 ∈ ↑((Finset.Ioc n₀ (n₀ + n₀)).filter (fun n : ℕ =>
      ∀ p ∈ (primorial z).primeFactors,
        ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))))
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hlt₁, by omega⟩, ?_⟩
    intro p hp hdvd
    rw [mem_primeFactors_primorial] at hp
    obtain ⟨hpp, hpz⟩ := hp
    -- the ℤ-product is the ℕ-product of the two block primes
    have hcast : (q.1 : ℤ) * ((s : ℤ) - (q.1 : ℤ)) = ((q.1 * q.2 : ℕ) : ℤ) := by
      have h1 : (s : ℤ) = (q.1 : ℤ) + (q.2 : ℤ) := by
        exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) hsum.symm
      rw [h1]
      push_cast
      ring
    rw [hcast, Int.natCast_dvd_natCast] at hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hpp hpp₁).mp h
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hpp hpp₂).mp h
      omega
  · intro q₁ hq₁ q₂ hq₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at hq₁ hq₂
    have h1 : q₁.1 = q₂.1 := heq
    have h2 : q₁.1 + q₁.2 = q₂.1 + q₂.2 := by
      rw [hq₁.2, hq₂.2]
    refine Prod.ext h1 (by omega)

/-- The logarithmic floor of the natural square root:
`log n / 2 − log 2 ≤ log ⌊√n⌋` for `n ≥ 4`. -/
theorem log_nat_sqrt_ge {n : ℕ} (hn : 4 ≤ n) :
    Real.log n / 2 - Real.log 2 ≤ Real.log (Nat.sqrt n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have h4 : (2 : ℝ) ≤ Real.sqrt n := by
    have h1 : ((4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
      rw [show (((4 : ℕ) : ℝ)) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  have hlt : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
    have h1 : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
      have h2 := Nat.lt_succ_sqrt n
      have h3 : (n : ℝ) < ((Nat.succ (Nat.sqrt n) : ℕ) : ℝ)
          * ((Nat.succ (Nat.sqrt n) : ℕ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h3
      nlinarith [h3]
    have h4' := Real.sqrt_lt_sqrt (Nat.cast_nonneg n) h1
    rwa [Real.sqrt_sq (by positivity)] at h4'
  have hs : Real.sqrt n / 2 ≤ ((Nat.sqrt n : ℕ) : ℝ) := by
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt n / 2 := by
    have := Real.sqrt_pos.mpr hn0
    linarith
  calc Real.log n / 2 - Real.log 2
      = Real.log (Real.sqrt n / 2) := by
        rw [Real.log_div (by positivity) (by norm_num),
          Real.log_sqrt (Nat.cast_nonneg n)]
    _ ≤ Real.log ((Nat.sqrt n : ℕ) : ℝ) :=
        Real.log_le_log hsq0 hs

/-- Crude but sufficient: `4·log⁴ n ≤ n` beyond `2²⁸`. -/
theorem four_log_pow_four_le {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    4 * Real.log n ^ 4 ≤ (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h0 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
    exact_mod_cast h0
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by norm_num) hn0).mpr (by nlinarith)
  have hs2 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt n) :=
    (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg n)).mpr (by nlinarith)
  have hlog4 : Real.log n = 4 * Real.log (Real.sqrt (Real.sqrt n)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg n), Real.log_sqrt hn0]
    ring
  have hbound : Real.log (Real.sqrt (Real.sqrt n))
      ≤ 2 * Real.sqrt (Real.sqrt (Real.sqrt n)) :=
    log_le_two_sqrt hs2
  have hlog8 : Real.log n ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt n)) := by
    rw [hlog4]
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  have hpow : Real.log n ^ 4
      ≤ (8 * Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 4 :=
    pow_le_pow_left₀ hlognn hlog8 4
  have hsss : (Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 4 = Real.sqrt n := by
    have h1 : (Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 2
        = Real.sqrt (Real.sqrt n) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (Real.sqrt n)) ^ 2 = Real.sqrt n :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    calc (Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 4
        = ((Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (Real.sqrt n)) ^ 2 := by rw [h1]
      _ = Real.sqrt n := h2
  have hexpand : (8 * Real.sqrt (Real.sqrt (Real.sqrt n))) ^ 4
      = 4096 * Real.sqrt n := by
    rw [mul_pow, hsss]
    norm_num
  have hsqrtn : (16384 : ℝ) ≤ Real.sqrt n := by
    refine (Real.le_sqrt (by norm_num) hn0).mpr ?_
    have h1 : ((2 ^ 28 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at h1
    nlinarith
  have hmulself : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt hn0
  have hfinal : 16384 * Real.sqrt n ≤ (n : ℝ) := by
    calc (16384 : ℝ) * Real.sqrt n
        ≤ Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_right hsqrtn (Real.sqrt_nonneg n)
      _ = (n : ℝ) := hmulself
  calc 4 * Real.log n ^ 4
      ≤ 4 * (4096 * Real.sqrt n) := by
        rw [← hexpand]
        linarith [hpow]
    _ = 16384 * Real.sqrt n := by ring
    _ ≤ (n : ℝ) := hfinal

/-- The five-fold square-root iterate keeps a `1/64` share of the logarithm
and stays above `2¹⁰`, beyond the threshold `2³²⁰`. -/
theorem log_iter_sqrt_bounds {n₀ : ℕ} (hn₀ : 2 ^ 320 ≤ n₀) :
    1024 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
    ∧ Real.log n₀ / 64
      ≤ Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))) := by
  have hstep : ∀ (m k : ℕ), 2 ^ (2 * k) ≤ m → 2 ^ k ≤ Nat.sqrt m := by
    intro m k h
    refine Nat.le_sqrt.mpr ?_
    have he : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
      rw [← pow_add, ← Nat.two_mul]
    rw [he]
    exact h
  have h1 : 2 ^ 160 ≤ Nat.sqrt n₀ := hstep n₀ 160 (by omega)
  have h2 : 2 ^ 80 ≤ Nat.sqrt (Nat.sqrt n₀) := hstep _ 80 (by
    calc 2 ^ (2 * 80) = 2 ^ 160 := by norm_num
      _ ≤ Nat.sqrt n₀ := h1)
  have h3 : 2 ^ 40 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)) := hstep _ 40 (by
    calc 2 ^ (2 * 40) = 2 ^ 80 := by norm_num
      _ ≤ Nat.sqrt (Nat.sqrt n₀) := h2)
  have h4 : 2 ^ 20 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) :=
    hstep _ 20 (by
      calc 2 ^ (2 * 20) = 2 ^ 40 := by norm_num
        _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)) := h3)
  have h5 : 2 ^ 10 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) :=
    hstep _ 10 (by
      calc 2 ^ (2 * 10) = 2 ^ 20 := by norm_num
        _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) := h4)
  refine ⟨by norm_num at h5 ⊢; omega, ?_⟩
  -- the log chain
  have hL1 := log_nat_sqrt_ge (n := n₀) (by omega)
  have hL2 := log_nat_sqrt_ge (n := Nat.sqrt n₀) (by
    have := h1
    omega)
  have hL3 := log_nat_sqrt_ge (n := Nat.sqrt (Nat.sqrt n₀)) (by
    have := h2
    omega)
  have hL4 := log_nat_sqrt_ge (n := Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) (by
    have := h3
    omega)
  have hL5 := log_nat_sqrt_ge
    (n := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) (by
    have := h4
    omega)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 320 * Real.log 2 ≤ Real.log n₀ := by
    have h6 : ((2 ^ 320 : ℕ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h7 := Real.log_le_log (by positivity) h6
    rw [show ((2 ^ 320 : ℕ) : ℝ) = (2 : ℝ) ^ 320 by push_cast; ring,
      Real.log_pow] at h7
    push_cast at h7
    linarith
  linarith

/-- **The per-target sieve bound**: beyond the threshold `2³²⁰`, every even
target's representation count is dominated by the singular factor times
`4096·n₀/log²n₀`, plus a square-root error. -/
theorem blockRep_le_of_even {n₀ s : ℕ} (hn₀ : 2 ^ 320 ≤ n₀)
    (hs : s ∈ Finset.Ioc (2 * n₀) (4 * n₀)) (heven : 2 ∣ s) :
    (blockRep n₀ s : ℝ)
      ≤ 4096 * (n₀ : ℝ)
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
          / Real.log n₀ ^ 2
        + (Nat.sqrt n₀ : ℝ) := by
  classical
  have hn₀2 : 2 ≤ n₀ := by omega
  have hsIoc := Finset.mem_Ioc.mp hs
  have hs0 : 2 * s ≠ 0 := by omega
  obtain ⟨hm₀1024, hm₀log⟩ := log_iter_sqrt_bounds hn₀
  -- the sift level sits strictly below the block
  have hz_lt : Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) < n₀ := by
    have h1 := Nat.sqrt_le_self (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))
    have h2 := Nat.sqrt_le_self (Nat.sqrt (Nat.sqrt n₀))
    have h3 := Nat.sqrt_le_self (Nat.sqrt n₀)
    have h4 : Nat.sqrt n₀ < n₀ := Nat.sqrt_lt_self (by omega)
    omega
  have hz1 : 1 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) := by
    have h1 := Nat.sqrt_le_self
      (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
    omega
  -- Step A: the block pairs inject into the sifted window
  have hA := blockRep_le_sift (s := s)
    (z := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) hz_lt
  -- Step B: the Selberg master bound with the primorial modulus
  have hB := card_sift_le_primorial_master (s := s)
    (z := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) (N := n₀) (a := n₀)
    heven hz1
  -- positivity facts
  have hprod_pos : 0 < ∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h3 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      linarith
    linarith
  have hlogm5_pos : (0 : ℝ)
      < Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))) := by
    refine Real.log_pos ?_
    have h1 : (1024 : ℕ) ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
        (Nat.sqrt n₀)))) := hm₀1024
    exact_mod_cast (by omega : (1 : ℕ)
      < Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
  have hlogn_pos : (0 : ℝ) < Real.log n₀ := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : (1 : ℕ) < n₀)
  -- Step C: the support collapse below the sift level
  have hfilter_eq : (Finset.Icc 1
        (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))).filter
        (fun m => Nat.Coprime m (2 * s)
          ∧ ∀ p ∈ m.primeFactors,
            p ∈ (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt
              (Nat.sqrt n₀))))).primeFactors)
      = (Finset.Icc 1
          (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))).filter
          (fun m => Nat.Coprime m (2 * s)) := by
    refine Finset.filter_congr fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    constructor
    · exact fun h => h.1
    · intro hcop
      refine ⟨hcop, fun p hp => ?_⟩
      rw [mem_primeFactors_primorial]
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      have hple : p ≤ m := Nat.le_of_dvd (by omega) hpm
      have hm₀z : Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
          ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) :=
        Nat.sqrt_le_self _
      exact ⟨hpp, by omega⟩
  -- the harmonic floor feeds the divisor-pairs square
  have hL_nonneg : (0 : ℝ)
      ≤ (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ)))
        * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
          (Nat.sqrt n₀))))) :=
    le_of_lt (mul_pos hprod_pos hlogm5_pos)
  have hL_le : (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ)))
      * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
      ≤ ∑ m ∈ (Finset.Icc 1
          (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))).filter
          (fun m => Nat.Coprime m (2 * s)
            ∧ ∀ p ∈ m.primeFactors,
              p ∈ (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt
                (Nat.sqrt n₀))))).primeFactors),
        (1 : ℝ) / m := by
    rw [hfilter_eq]
    exact log_le_sum_one_div_coprime hs0
  have hsq := sq_sum_one_div_le_sum_div (s := s)
    (P := primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
    (R := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
    (m₀ := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
    (Nat.sqrt_le _)
  have hGsum := selbergG_ge_sum_div
    (R := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
    (squarefree_primorial _)
    (sieveRootCard_lt_of_even
      (z := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) heven)
  have hGfloor : ((∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ)))
        * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
          (Nat.sqrt n₀)))))) ^ 2
      ≤ selbergG s (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
        (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) :=
    le_trans (pow_le_pow_left₀ hL_nonneg hL_le 2) (le_trans hsq hGsum)
  -- Step D: fold the G-floor into the main term
  have hσ_pos : (0 : ℝ)
      < ∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    exact inv_pos.mpr hprod_pos
  have hcancel : (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
      * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))) ^ 2 = 1 := by
    rw [Finset.prod_inv_distrib, ← mul_pow,
      inv_mul_cancel₀ (ne_of_gt hprod_pos), one_pow]
  have hG_pos : (0 : ℝ)
      < selbergG s (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
        (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) :=
    lt_of_lt_of_le (pow_pos (mul_pos hprod_pos hlogm5_pos) 2) hGfloor
  have hmain : (n₀ : ℝ)
      / selbergG s (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
        (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
      ≤ 4096 * (n₀ : ℝ)
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
          / Real.log n₀ ^ 2 := by
    rw [div_le_div_iff₀ hG_pos (pow_pos hlogn_pos 2)]
    have hstep : 4096 * (n₀ : ℝ)
        * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
        * ((∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ)))
          * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
            (Nat.sqrt n₀)))))) ^ 2
        ≤ 4096 * (n₀ : ℝ)
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
          * selbergG s
            (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
            (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) := by
      refine mul_le_mul_of_nonneg_left hGfloor ?_
      have h1 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
      nlinarith [hσ_pos]
    have hlogsq : (Real.log n₀ / 64) ^ 2
        ≤ Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
          (Nat.sqrt n₀))))) ^ 2 := by
      refine pow_le_pow_left₀ ?_ hm₀log 2
      positivity
    calc (n₀ : ℝ) * Real.log n₀ ^ 2
        = 4096 * (n₀ : ℝ) * (Real.log n₀ / 64) ^ 2 := by ring
      _ ≤ 4096 * (n₀ : ℝ)
          * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
            (Nat.sqrt n₀))))) ^ 2 := by
          refine mul_le_mul_of_nonneg_left hlogsq ?_
          positivity
      _ = 4096 * (n₀ : ℝ)
          * ((∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
            * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))) ^ 2)
          * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
            (Nat.sqrt n₀))))) ^ 2 := by
          rw [hcancel]
          ring
      _ = 4096 * (n₀ : ℝ)
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
          * ((∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ)))
            * Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt
              (Nat.sqrt n₀)))))) ^ 2 := by ring
      _ ≤ 4096 * (n₀ : ℝ)
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
          * selbergG s
            (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
            (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) := hstep
  -- Step E: the error term is below the square root
  have herr : (((Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) : ℝ)) ^ 4) ^ 2
      ≤ (Nat.sqrt n₀ : ℝ) := by
    have hz2 : Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))
        * Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))
        ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)) := Nat.sqrt_le _
    have hw₃2 : Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))
        * Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))
        ≤ Nat.sqrt (Nat.sqrt n₀) := Nat.sqrt_le _
    have hw₂2 : Nat.sqrt (Nat.sqrt n₀) * Nat.sqrt (Nat.sqrt n₀)
        ≤ Nat.sqrt n₀ := Nat.sqrt_le _
    have h8 : Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) ^ 8
        ≤ Nat.sqrt n₀ := by
      calc Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) ^ 8
          = (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))
            * Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) ^ 4 := by ring
        _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)) ^ 4 :=
            Nat.pow_le_pow_left hz2 4
        _ = (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))
            * Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) ^ 2 := by ring
        _ ≤ Nat.sqrt (Nat.sqrt n₀) ^ 2 := Nat.pow_le_pow_left hw₃2 2
        _ = Nat.sqrt (Nat.sqrt n₀) * Nat.sqrt (Nat.sqrt n₀) := by ring
        _ ≤ Nat.sqrt n₀ := hw₂2
    calc (((Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) : ℝ)) ^ 4) ^ 2
        = ((Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) ^ 8 : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ (Nat.sqrt n₀ : ℝ) := by exact_mod_cast h8
  -- assemble
  calc (blockRep n₀ s : ℝ)
      ≤ (((Finset.Ioc n₀ (n₀ + n₀)).filter (fun n : ℕ =>
          ∀ p ∈ (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt
            (Nat.sqrt n₀))))).primeFactors,
            ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))))).card : ℝ) := by
        exact_mod_cast hA
    _ ≤ (n₀ : ℝ)
        / selbergG s
          (primorial (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))))
          (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
        + (((Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) : ℝ)) ^ 4) ^ 2 :=
        hB
    _ ≤ 4096 * (n₀ : ℝ)
        * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
        / Real.log n₀ ^ 2
        + (Nat.sqrt n₀ : ℝ) := add_le_add hmain herr

/-- **The final count, beyond the threshold**: the additive-quadruple count
saves four logarithms. -/
theorem card_quadruple_le_final {n₀ : ℕ} (hn₀ : 2 ^ 320 ≤ n₀) :
    ((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
      ≤ 2 ^ 40 * Real.exp 30 * n₀ ^ 3 / Real.log n₀ ^ 4 := by
  classical
  have hn₀2 : 2 ≤ n₀ := by omega
  have hlogn_pos : (0 : ℝ) < Real.log n₀ :=
    Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < n₀))
  rw [card_quadruple_eq_sum_blockRep_sq]
  push_cast
  -- the pointwise square bound
  have hper : ∀ s ∈ Finset.Ioc (2 * n₀) (4 * n₀),
      (blockRep n₀ s : ℝ) ^ 2
      ≤ 2 * 4096 ^ 2 * (n₀ : ℝ) ^ 2 / Real.log n₀ ^ 4
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
        + 2 * (n₀ : ℝ) := by
    intro s hsI
    by_cases heven : 2 ∣ s
    · have hb := blockRep_le_of_even hn₀ hsI heven
      have hb0 : (0 : ℝ) ≤ (blockRep n₀ s : ℝ) := Nat.cast_nonneg _
      have hsqrt : ((Nat.sqrt n₀ : ℝ)) ^ 2 ≤ (n₀ : ℝ) := by
        have h1 : Nat.sqrt n₀ * Nat.sqrt n₀ ≤ n₀ := Nat.sqrt_le n₀
        have h2 : ((Nat.sqrt n₀ * Nat.sqrt n₀ : ℕ) : ℝ) ≤ (n₀ : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        nlinarith
      have hexpand : 2 * (4096 * (n₀ : ℝ)
            * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
            / Real.log n₀ ^ 2) ^ 2
          = 2 * 4096 ^ 2 * (n₀ : ℝ) ^ 2 / Real.log n₀ ^ 4
            * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4 := by
        field_simp
      nlinarith [hb, hb0, hsqrt, hexpand,
        sq_nonneg (4096 * (n₀ : ℝ)
          * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 2
          / Real.log n₀ ^ 2 - (Nat.sqrt n₀ : ℝ)),
        (Nat.cast_nonneg (Nat.sqrt n₀) : (0 : ℝ) ≤ (Nat.sqrt n₀ : ℝ))]
    · rw [blockRep_eq_zero_of_odd hn₀2 heven]
      have h1 : (0 : ℝ)
          ≤ 2 * 4096 ^ 2 * (n₀ : ℝ) ^ 2 / Real.log n₀ ^ 4
            * (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
            + 2 * (n₀ : ℝ) := by positivity
      simpa using h1
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  have hcard : (Finset.Ioc (2 * n₀) (4 * n₀)).card = 2 * n₀ := by
    rw [Nat.card_Ioc]
    omega
  rw [hcard]
  -- the singular-series second moment (S9)
  have hS9 := sum_singular_pow_four_le n₀
  have hcoef : (0 : ℝ) ≤ 2 * 4096 ^ 2 * (n₀ : ℝ) ^ 2 / Real.log n₀ ^ 4 := by
    positivity
  have hmain := mul_le_mul_of_nonneg_left hS9 hcoef
  -- the error piece: `4·n₀² ≤ n₀³/log⁴`
  have hfour := four_log_pow_four_le (n := n₀) (by omega)
  have herr : ((2 * n₀ : ℕ) : ℝ) * (2 * (n₀ : ℝ))
      ≤ (n₀ : ℝ) ^ 3 / Real.log n₀ ^ 4 := by
    rw [le_div_iff₀ (pow_pos hlogn_pos 4)]
    have h1 := mul_le_mul_of_nonneg_right hfour
      (show (0 : ℝ) ≤ (n₀ : ℝ) ^ 2 by positivity)
    push_cast
    nlinarith [h1]
  have he30 : (1 : ℝ) ≤ Real.exp 30 := by
    have h1 := Real.add_one_le_exp (30 : ℝ)
    linarith
  have hn₀3 : (0 : ℝ) ≤ (n₀ : ℝ) ^ 3 / Real.log n₀ ^ 4 := by positivity
  calc 2 * 4096 ^ 2 * (n₀ : ℝ) ^ 2 / Real.log n₀ ^ 4
        * ∑ s ∈ Finset.Ioc (2 * n₀) (4 * n₀),
            (∏ p ∈ (2 * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
      + ((2 * n₀ : ℕ) : ℝ) * (2 * (n₀ : ℝ))
      ≤ 2 * 4096 ^ 2 * (n₀ : ℝ) ^ 2 / Real.log n₀ ^ 4
          * (12 * Real.exp 30 * (n₀ : ℝ))
        + (n₀ : ℝ) ^ 3 / Real.log n₀ ^ 4 := add_le_add hmain herr
    _ = (24 * 4096 ^ 2 * Real.exp 30 + 1) * (n₀ : ℝ) ^ 3
        / Real.log n₀ ^ 4 := by
        field_simp
        ring
    _ ≤ 2 ^ 40 * Real.exp 30 * (n₀ : ℝ) ^ 3 / Real.log n₀ ^ 4 := by
        rw [div_le_div_iff₀ (pow_pos hlogn_pos 4) (pow_pos hlogn_pos 4)]
        have h2 : 24 * 4096 ^ 2 * Real.exp 30 + 1 ≤ 2 ^ 40 * Real.exp 30 := by
          nlinarith [he30]
        have h3 : (0 : ℝ) ≤ (n₀ : ℝ) ^ 3 * Real.log n₀ ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h2 h3]

/-- **The sub-threshold regime**: below `2³²⁰` the trivial cube bound
already saves four logarithms. -/
theorem card_quadruple_le_small {n₀ : ℕ} (hn₀2 : 2 ≤ n₀)
    (hn₀ : n₀ < 2 ^ 320) :
    ((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
      ≤ 2 ^ 40 * Real.exp 30 * n₀ ^ 3 / Real.log n₀ ^ 4 := by
  classical
  have hlogn_pos : (0 : ℝ) < Real.log n₀ :=
    Real.log_pos (by exact_mod_cast hn₀2)
  have hcube := card_quadruple_le_cube n₀
  have hcast : ((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
      ≤ 2 * (n₀ : ℝ) ^ 3 := by
    have h1 : ((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
          (primeBlock n₀ ×ˢ primeBlock n₀)).filter
        (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℕ) ≤ 2 * n₀ ^ 3 :=
      hcube
    exact_mod_cast h1
  refine le_trans hcast ?_
  rw [le_div_iff₀ (pow_pos hlogn_pos 4)]
  -- `log n₀ < 222` below the threshold
  have hlog_lt : Real.log n₀ ≤ 222 := by
    have h1 : (n₀ : ℝ) ≤ 2 ^ 320 := by
      have h2 : (n₀ : ℕ) ≤ 2 ^ 320 := by omega
      exact_mod_cast h2
    have h3 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h3
    have h4 := Real.log_two_lt_d9
    push_cast at h3
    nlinarith
  have hlog4 : Real.log n₀ ^ 4 ≤ 222 ^ 4 :=
    pow_le_pow_left₀ hlogn_pos.le hlog_lt 4
  have he30 : (1 : ℝ) ≤ Real.exp 30 := by
    have h1 := Real.add_one_le_exp (30 : ℝ)
    linarith
  have hn₀3 : (0 : ℝ) ≤ (n₀ : ℝ) ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hlog4 hn₀3,
    mul_le_mul_of_nonneg_right he30 (mul_nonneg hn₀3 hn₀3)]

/-- **The prime-quadruple count assumption holds unconditionally**: the
Selberg Λ² sieve discharges it with `C = 2⁴⁰·e³⁰`. -/
instance : PrimeQuadrupleCountAssumption := by
  refine ⟨⟨2 ^ 40 * Real.exp 30, by positivity, fun n₀ hn₀2 => ?_⟩⟩
  by_cases hth : 2 ^ 320 ≤ n₀
  · exact card_quadruple_le_final hth
  · exact card_quadruple_le_small hn₀2 (by omega)

end Tao2015

end MoltResearch
