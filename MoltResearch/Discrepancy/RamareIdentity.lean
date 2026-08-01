import MoltResearch.Discrepancy.TuranKubilius
import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Track C: the Ramaré double-count identity (Track R, C4e-1)

The exact combinatorial engine of the `𝒰`-decomposition: for any finsets
`A, P` and weight `g`,

  `∑_{p∈P} ∑_{n∈A, p∣n} g(n)/ω_P(n) = ∑_{n∈A, ω_P(n)≥1} g(n)`,

where `ω_P(n) = #{p ∈ P : p ∣ n}`. Each `n` with `ω_P(n) = k ≥ 1` lies
in exactly `k` fibres, each weighted `1/k`. This is the identity behind
the `[MR]`-style factorization `F = ∑_p f(p)p^{−s}·G_p + (collision
terms)`: the C4e assembly splits `n = p·m` in each fibre and pushes the
`p ∤ m` main terms through the dyadic MVT (`DyadicMVT.lean`) while the
`p² ∣ n` collisions are second order.

Same swap pattern as the Turán–Kubilius first moment
(`sum_card_dvd_div_eq`); no primality enters.
-/

open Finset

namespace MoltResearch

/-- **The Ramaré double-count identity** (C4e-1, exact form): summing the
weight `g(n)/ω_P(n)` over the divisibility fibres of every `p ∈ P`
reproduces exactly the sum of `g` over those `n` with `ω_P(n) ≥ 1`, where
`ω_P(n) = #{p ∈ P : p ∣ n}` — each such `n` appears in `ω_P(n)` fibres,
each carrying weight `1/ω_P(n)`. No primality enters. -/
theorem sum_div_card_dvd_eq_sum_filter (A P : Finset ℕ) (g : ℕ → ℂ) :
    ∑ p ∈ P, ∑ n ∈ A.filter (fun n => p ∣ n),
        g n / ((P.filter (· ∣ n)).card : ℂ)
      = ∑ n ∈ A.filter (fun n => 0 < (P.filter (· ∣ n)).card), g n := by
  classical
  have h1 : ∀ p ∈ P, ∑ n ∈ A.filter (fun n => p ∣ n),
      g n / ((P.filter (· ∣ n)).card : ℂ)
      = ∑ n ∈ A, if p ∣ n then g n / ((P.filter (· ∣ n)).card : ℂ) else 0 := by
    intro p _
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ n ∈ A,
      (∑ p ∈ P, if p ∣ n then g n / ((P.filter (· ∣ n)).card : ℂ) else 0)
      = if 0 < (P.filter (· ∣ n)).card then g n else 0 := by
    intro n _
    have hconst : (∑ p ∈ P, if p ∣ n then g n / ((P.filter (· ∣ n)).card : ℂ) else 0)
        = ((P.filter (· ∣ n)).card : ℂ) * (g n / ((P.filter (· ∣ n)).card : ℂ)) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    rcases Nat.eq_zero_or_pos (P.filter (· ∣ n)).card with h0 | h0
    · rw [h0, if_neg (by omega)]
      simp
    · rw [if_pos h0]
      have hne : ((P.filter (· ∣ n)).card : ℂ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp h0
      field_simp
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]

/-- **The fibre reindex** (C4e-2): the multiples of `p` in a range `(a, b]`
are exactly the dilates `p·m` for `m ∈ (a/p, b/p]` (floor division), so a
sum over the `p`-divisibility fibre is a sum over the dilated range. -/
theorem sum_Ioc_filter_dvd_eq_sum_Ioc_div {M : Type*} [AddCommMonoid M]
    (a b p : ℕ) (hp : 0 < p) (h : ℕ → M) :
    ∑ n ∈ (Finset.Ioc a b).filter (fun n => p ∣ n), h n
      = ∑ m ∈ Finset.Ioc (a / p) (b / p), h (p * m) := by
  classical
  refine Finset.sum_bij' (fun n _ => n / p) (fun m _ => p * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨han, hnb⟩, hdvd⟩ := hn
    obtain ⟨m, rfl⟩ := hdvd
    rw [Finset.mem_Ioc]
    dsimp only
    rw [Nat.mul_div_cancel_left m hp]
    constructor
    · exact (Nat.div_lt_iff_lt_mul hp).mpr (by rw [mul_comm]; exact han)
    · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [mul_comm]; exact hnb)
  · intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right p m⟩
    · have h1 := (Nat.div_lt_iff_lt_mul hp).mp hm.1
      rw [mul_comm] at h1
      exact h1
    · have h2 := (Nat.le_div_iff_mul_le hp).mp hm.2
      rw [mul_comm] at h2
      exact h2
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m hp
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]


/-- **The ω-shift** (C4e-3): adjoining a prime factor `p ∈ P` not dividing
`m` raises the `P`-factor count by exactly one:
`ω_P(p·m) = ω_P(m) + 1` for `P` a set of primes. The first
primality-consuming step of the `𝒰`-assembly: on the collision-free part
of each fibre the Ramaré weight `1/ω_P(p·m)` is `1/(ω_P(m)+1)` — the
`[MR]` `G`-weight. -/
theorem card_filter_dvd_mul_of_prime (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hp : p ∈ P) {m : ℕ} (hpm : ¬ p ∣ m) :
    (P.filter (· ∣ p * m)).card = (P.filter (· ∣ m)).card + 1 := by
  classical
  have hset : P.filter (· ∣ p * m) = insert p (P.filter (· ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hqP, hqdvd⟩
      rcases (Nat.Prime.dvd_mul (hP q hqP)).mp hqdvd with hqp | hqm
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (hP q hqP) (hP p hp)).mp hqp)
      · exact Or.inr ⟨hqP, hqm⟩
    · rintro (rfl | ⟨hqP, hqm⟩)
      · exact ⟨hp, dvd_mul_right q m⟩
      · exact ⟨hqP, hqm.mul_left p⟩
  rw [hset, Finset.card_insert_of_notMem]
  intro hmem
  rw [Finset.mem_filter] at hmem
  exact hpm hmem.2


/-- **The 𝒰-decomposition normal form** (C4e-4): the sum of `g` over the
`n ∈ (a,b]` with a factor in the prime set `P` splits into the main
Ramaré-weighted dilated sums (weight `1/(ω_P(m)+1)`, collision-free
fibres) plus the collision sums (`p ∣ m`). C4e-1 ∘ C4e-2 ∘ C4e-3. -/
theorem sum_filter_omega_pos_eq_main_add_collision (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (g : ℕ → ℂ) :
    ∑ n ∈ (Finset.Ioc a b).filter (fun n => 0 < (P.filter (· ∣ n)).card), g n
      = (∑ p ∈ P, ∑ m ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m => ¬ p ∣ m),
          g (p * m) / (((P.filter (· ∣ m)).card : ℂ) + 1))
        + ∑ p ∈ P, ∑ m ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m => p ∣ m),
            g (p * m) / (((P.filter (· ∣ p * m)).card : ℂ)) := by
  classical
  rw [← sum_div_card_dvd_eq_sum_filter (Finset.Ioc a b) P g]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (hP p hp).pos
  rw [sum_Ioc_filter_dvd_eq_sum_Ioc_div a b p hp0
    (fun n => g n / ((P.filter (· ∣ n)).card : ℂ))]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc (a/p) (b/p))
    (fun m => ¬ p ∣ m)]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    rw [card_filter_dvd_mul_of_prime P hP hp hm.2]
    push_cast
    ring
  · refine Finset.sum_congr ?_ fun m _ => rfl
    ext m
    simp only [Finset.mem_filter, not_not]


/-- **The collision bound** (C4e-5): the collision half of the
`𝒰`-decomposition is dominated in norm by the `p²`-refibred absolute
sums — each collision fibre `p ∣ m` is the `p²`-dilate of a shorter
range, so its total mass is second order in `1/p`. -/
theorem norm_sum_collision_le (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (g : ℕ → ℂ) :
    ‖∑ p ∈ P, ∑ m ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m => p ∣ m),
        g (p * m) / (((P.filter (· ∣ p * m)).card : ℂ))‖
      ≤ ∑ p ∈ P, ∑ k ∈ Finset.Ioc (a/(p*p)) (b/(p*p)), ‖g (p * (p * k))‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
  have hp0 : 0 < p := (hP p hp).pos
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ m ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m => p ∣ m),
      ‖g (p * m) / (((P.filter (· ∣ p * m)).card : ℂ))‖ ≤ ‖g (p * m)‖ := by
    intro m hm
    rw [norm_div, Complex.norm_natCast]
    have hω : 1 ≤ ((P.filter (· ∣ p * m)).card : ℝ) := by
      have hpos : 0 < (P.filter (· ∣ p * m)).card :=
        Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, dvd_mul_right p m⟩⟩
      exact_mod_cast hpos
    exact div_le_self (norm_nonneg _) hω
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [show a/(p*p) = (a/p)/p from (Nat.div_div_eq_div_mul a p p).symm,
    show b/(p*p) = (b/p)/p from (Nat.div_div_eq_div_mul b p p).symm]
  rw [← sum_Ioc_filter_dvd_eq_sum_Ioc_div (a/p) (b/p) p hp0
    (fun n => ‖g (p * n)‖)]


/-- **The CM-factor extraction** (C4e-6): on the collision-free main half
of the `𝒰`-decomposition, a completely multiplicative `g` factors each
fibre as `g(p)` times the `G`-weighted block sum — the literal
`F = ∑_p g(p)·G_p` shape of the `[MR]` 𝒯₁ treatment. The `0`-guards of
`CompletelyMultiplicativeC` are satisfied since `p` is prime and the
fibre elements are positive. -/
theorem main_half_eq_sum_mul (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) :
    ∑ p ∈ P, ∑ m ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m => ¬ p ∣ m),
        g (p * m) / (((P.filter (· ∣ m)).card : ℂ) + 1)
      = ∑ p ∈ P, g p *
          ∑ m ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m => ¬ p ∣ m),
            g m / (((P.filter (· ∣ m)).card : ℂ) + 1) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  have hm0 : m ≠ 0 := fun h => hm.2 (h ▸ dvd_zero p)
  rw [hcm p m (hP p hp).ne_zero hm0, mul_div_assoc]


open ArithmeticFunction in
/-- **The log convolution identity** (Track R, W2c-i): for completely
multiplicative `f`, the log-weighted harmonic sum factors through von
Mangoldt — `∑_{n≤x} f(n)log n/n = ∑_{d≤x} Λ(d)f(d)/d · T(x/d)` with
`T(y) = ∑_{m≤y} f(m)/m`. The engine of the elementary log-averaged
Halász iteration: the log side ties `T` to itself at smaller scales
through prime weights. -/
theorem sum_mul_log_div_eq_vonMangoldt_conv (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (x : ℕ) :
    ∑ n ∈ Finset.Ioc 0 x, f n * ((Real.log n : ℝ) : ℂ) / n
      = ∑ d ∈ Finset.Ioc 0 x, ((vonMangoldt d : ℝ) : ℂ) * f d / d
          * ∑ m ∈ Finset.Ioc 0 (x/d), f m / m := by
  classical
  have hstep1 : ∀ n ∈ Finset.Ioc 0 x,
      f n * ((Real.log n : ℝ) : ℂ) / n
        = ∑ d ∈ Finset.Ioc 0 x,
            if d ∣ n then ((vonMangoldt d : ℝ) : ℂ) * (f n / n) else 0 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hset : n.divisors = (Finset.Ioc 0 x).filter (· ∣ n) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨hdvd, hne⟩
        have h1 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have h2 : d ≤ n := Nat.le_of_dvd (by omega) hdvd
        exact ⟨⟨h1, by omega⟩, hdvd⟩
      · rintro ⟨-, hdvd⟩
        exact ⟨hdvd, by omega⟩
    have hlog : ((Real.log n : ℝ) : ℂ) = ∑ d ∈ n.divisors,
        ((vonMangoldt d : ℝ) : ℂ) := by
      rw [show ∑ d ∈ n.divisors, ((vonMangoldt d : ℝ) : ℂ)
          = ((∑ d ∈ n.divisors, vonMangoldt d : ℝ) : ℂ) from by push_cast; rfl]
      rw [vonMangoldt_sum]
    rw [hlog, hset, Finset.sum_filter, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ∣ n
    · rw [if_pos hd, if_pos hd]
      ring
    · rw [if_neg hd, if_neg hd]
      simp
  rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Ioc] at hd
  rw [← Finset.sum_filter]
  have hreindex := sum_Ioc_filter_dvd_eq_sum_Ioc_div 0 x d (by omega)
    (fun n => ((vonMangoldt d : ℝ) : ℂ) * (f n / n))
  rw [Nat.zero_div] at hreindex
  rw [hreindex]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Ioc] at hm
  have hfdm : f (d * m) = f d * f m := hcm d m (by omega) (by omega)
  have hdm0 : ((d * m : ℕ) : ℂ) ≠ 0 := by
    have h1 : d * m ≠ 0 := by
      have hd0 : d ≠ 0 := by omega
      have hm0 : m ≠ 0 := by omega
      exact Nat.mul_ne_zero hd0 hm0
    exact_mod_cast h1
  rw [hfdm]
  push_cast
  field_simp


/-- **The log-ratio summation by parts** (Track R, W2c-ii-a): the
`log(x/n)`-weighted harmonic sum is the telescoped average of the
partial sums `T(k) = ∑_{m≤k} f(m)/m` against the logarithmic mesh —
exact and discrete, no integral. With W2c-i this gives the Wirsing
identity `T(x)·log x = (mesh average of T) + (Λf-weighted average of
T at smaller scales)`. -/
theorem sum_mul_log_ratio_div_eq (f : ℕ → ℂ) (x : ℕ) :
    ∑ n ∈ Finset.Ioc 0 x, f n * (((Real.log x - Real.log n : ℝ)) : ℂ) / n
      = ∑ k ∈ Finset.Ioc 0 (x-1),
          (∑ m ∈ Finset.Ioc 0 k, f m / m)
            * (((Real.log (k+1) - Real.log k : ℝ)) : ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    simp
  -- expand the inner partial sums and swap
  have hswap : ∑ k ∈ Finset.Ioc 0 (x-1),
      (∑ m ∈ Finset.Ioc 0 k, f m / m)
        * (((Real.log (k+1) - Real.log k : ℝ)) : ℂ)
      = ∑ m ∈ Finset.Ioc 0 (x-1), (f m / m)
          * ∑ k ∈ Finset.Icc m (x-1),
              (((Real.log (k+1) - Real.log k : ℝ)) : ℂ) := by
    have h1 : ∀ k ∈ Finset.Ioc 0 (x-1),
        (∑ m ∈ Finset.Ioc 0 k, f m / m)
          * (((Real.log (k+1) - Real.log k : ℝ)) : ℂ)
        = ∑ m ∈ Finset.Ioc 0 (x-1),
            if m ≤ k then (f m / m) * (((Real.log (k+1) - Real.log k : ℝ)) : ℂ)
            else 0 := by
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [Finset.sum_mul]
      rw [show Finset.Ioc 0 k
          = (Finset.Ioc 0 (x-1)).filter (fun m => m ≤ k) from by
        ext m
        simp only [Finset.mem_Ioc, Finset.mem_filter]
        omega]
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mul_sum]
    rw [show Finset.Icc m (x-1)
        = (Finset.Ioc 0 (x-1)).filter (fun k => m ≤ k) from by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_filter]
      omega]
    rw [Finset.sum_filter]
  rw [hswap]
  -- telescope per m
  have htel : ∀ m ∈ Finset.Ioc 0 (x-1),
      ∑ k ∈ Finset.Icc m (x-1), (((Real.log (k+1) - Real.log k : ℝ)) : ℂ)
        = (((Real.log x - Real.log m : ℝ)) : ℂ) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hIccIco : Finset.Icc m (x-1) = Finset.Ico m x := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco]
    have hsum : ∑ k ∈ Finset.Ico m x, (Real.log ((k+1 : ℕ)) - Real.log (k : ℕ))
        = Real.log x - Real.log m := by
      have h1 := Finset.sum_Ico_eq_sub
        (fun k : ℕ => Real.log ((k+1 : ℕ)) - Real.log (k : ℕ))
        (show m ≤ x by omega)
      have h2 : ∀ y : ℕ, ∑ k ∈ Finset.range y,
          (Real.log ((k+1 : ℕ)) - Real.log (k : ℕ))
          = Real.log (y : ℕ) - Real.log (0 : ℕ) :=
        fun y => Finset.sum_range_sub (fun k : ℕ => Real.log k) y
      rw [h1, h2 x, h2 m]
      simp
    calc ∑ k ∈ Finset.Ico m x, (((Real.log (k+1) - Real.log k : ℝ)) : ℂ)
        = (((∑ k ∈ Finset.Ico m x,
            (Real.log ((k+1 : ℕ)) - Real.log (k : ℕ)) : ℝ)) : ℂ) := by
          push_cast
          rfl
      _ = (((Real.log x - Real.log m : ℝ)) : ℂ) := by
          rw [hsum]
  have hconv : ∑ m ∈ Finset.Ioc 0 (x-1), (f m / m)
      * ∑ k ∈ Finset.Icc m (x-1), (((Real.log (k+1) - Real.log k : ℝ)) : ℂ)
      = ∑ m ∈ Finset.Ioc 0 (x-1), (f m / m)
          * (((Real.log x - Real.log m : ℝ)) : ℂ) :=
    Finset.sum_congr rfl fun m hm => by rw [htel m hm]
  rw [hconv]
  -- extend the m-range to Ioc 0 x (the top term vanishes)
  rcases Nat.eq_or_lt_of_le hx with hx1 | hx1
  · rw [← hx1]
    simp
  have hext : Finset.Ioc 0 x = insert x (Finset.Ioc 0 (x-1)) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hext, Finset.sum_insert (by
    rw [Finset.mem_Ioc]
    omega)]
  have hzero : f x * (((Real.log x - Real.log x : ℝ)) : ℂ) / x = 0 := by
    simp
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring


open ArithmeticFunction in
/-- **The Wirsing identity** (Track R, W2c-ii-b): for completely
multiplicative `f`, the harmonic partial sum `T(x) = ∑_{m≤x} f(m)/m`
satisfies the exact scale recursion

  `T(x)·log x = ∑_{k<x} T(k)·Δlog(k) + ∑_{d≤x} Λ(d)f(d)/d · T(x/d)`

— W2c-i plus W2c-ii-a through `log x = log n + log(x/n)`. The
elementary log-averaged Halász iterates this identity. -/
theorem wirsing_identity (f : ℕ → ℂ) (hcm : CompletelyMultiplicativeC f)
    (x : ℕ) :
    (∑ m ∈ Finset.Ioc 0 x, f m / m) * ((Real.log x : ℝ) : ℂ)
      = (∑ k ∈ Finset.Ioc 0 (x-1),
          (∑ m ∈ Finset.Ioc 0 k, f m / m)
            * (((Real.log (k+1) - Real.log k : ℝ)) : ℂ))
        + ∑ d ∈ Finset.Ioc 0 x, ((vonMangoldt d : ℝ) : ℂ) * f d / d
            * ∑ m ∈ Finset.Ioc 0 (x/d), f m / m := by
  classical
  have hsplit : (∑ m ∈ Finset.Ioc 0 x, f m / m) * ((Real.log x : ℝ) : ℂ)
      = (∑ n ∈ Finset.Ioc 0 x, f n * ((Real.log n : ℝ) : ℂ) / n)
        + ∑ n ∈ Finset.Ioc 0 x, f n * (((Real.log x - Real.log n : ℝ)) : ℂ) / n := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    push_cast
    ring
  rw [hsplit, sum_mul_log_div_eq_vonMangoldt_conv f hcm x,
    sum_mul_log_ratio_div_eq f x]
  ring


end MoltResearch
