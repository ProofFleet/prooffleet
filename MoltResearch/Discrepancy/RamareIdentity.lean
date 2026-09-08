import MoltResearch.Discrepancy.TuranKubilius
import MoltResearch.Discrepancy.MultiplicativeC
import MoltResearch.Discrepancy.LargeValues
import MoltResearch.Discrepancy.DyadicMVT
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


/-- **The sifted-interval count** (Track R, W2c-iv-a): the number of
integers in `(a, b]` with no prime factor in the finite prime set `P`
is at most `φ(Q)·((b−a)/Q + 1)` with `Q = ∏ P` — coprimality to the
squarefree modulus, counted by periodicity. The non-`𝒰` density bound
of the Ramaré decomposition: at fixed `P = P(ε)` and interval length
`→ ∞` this is `∏(1−1/p) + o(1)`, Mertens-small. -/
theorem card_filter_not_dvd_le (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ((Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card
      ≤ (∏ p ∈ P, p).totient * ((b - a)/(∏ p ∈ P, p) + 1) := by
  classical
  have hQ0 : (∏ p ∈ P, p) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact (hP p hp).ne_zero
  -- the condition is coprimality to the product
  have hcond : ∀ m : ℕ, (∀ p ∈ P, ¬ p ∣ m) ↔ (∏ p ∈ P, p).Coprime m := by
    intro m
    rw [Nat.coprime_prod_left_iff]
    constructor
    · intro h p hp
      exact ((hP p hp).coprime_iff_not_dvd).mpr (h p hp)
    · intro h p hp
      exact ((hP p hp).coprime_iff_not_dvd).mp (h p hp)
  have hfilter : (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)
      = (Finset.Ioc a b).filter (fun m => (∏ p ∈ P, p).Coprime m) := by
    refine Finset.filter_congr fun m _ => ?_
    simp only [hcond m]
  rw [hfilter]
  rcases Nat.lt_or_ge b a with hba | hab
  · have : Finset.Ioc a b = ∅ := by
      rw [Finset.Ioc_eq_empty]
      omega
    rw [this]
    simp
  -- convert to the Ico window and apply the periodic count
  have hIoc : Finset.Ioc a b = Finset.Ico (a+1) ((a+1) + (b-a)) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc]
  exact Nat.Ico_filter_coprime_le (a+1) (b-a) hQ0


/-- **The sifted density** (Track R, W2c-iv-b): the totient of a
squarefree prime product is exponentially damped by the prime
reciprocal mass — `φ(∏P) ≤ (∏P)·e^{−∑1/p}`. With the Mertens floor
this makes the sifted-interval density `∏(1−1/p)` as small as desired
by widening the prime window. -/
theorem totient_prod_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (((∏ p ∈ P, p).totient : ℕ) : ℝ)
      ≤ (((∏ p ∈ P, p) : ℕ) : ℝ) * Real.exp (-(∑ p ∈ P, (1:ℝ)/p)) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert p P' hpnot ih =>
    have hpp : p.Prime := hP p (Finset.mem_insert_self p P')
    have hP' : ∀ q ∈ P', q.Prime := fun q hq =>
      hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ P', q) := by
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      refine (Nat.coprime_primes hpp (hP' q hq)).mpr ?_
      intro heq
      exact hpnot (heq ▸ hq)
    rw [Finset.prod_insert hpnot, Finset.sum_insert hpnot,
      Nat.totient_mul hcop, Nat.totient_prime hpp]
    have hih := ih hP'
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hfac : ((p - 1 : ℕ) : ℝ) ≤ (p:ℝ) * Real.exp (-(1/(p:ℝ))) := by
      have h1 : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
        have := hpp.one_lt
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
        ring
      rw [h1]
      have h2 : 1 - 1/(p:ℝ) ≤ Real.exp (-(1/(p:ℝ))) := by
        have := Real.add_one_le_exp (-(1/(p:ℝ)))
        linarith
      calc (p:ℝ) - 1 = (p:ℝ) * (1 - 1/(p:ℝ)) := by field_simp
        _ ≤ (p:ℝ) * Real.exp (-(1/(p:ℝ))) :=
            mul_le_mul_of_nonneg_left h2 hp0.le
    calc (((p - 1) * (∏ q ∈ P', q).totient : ℕ) : ℝ)
        = ((p - 1 : ℕ) : ℝ) * (((∏ q ∈ P', q).totient : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ ((p:ℝ) * Real.exp (-(1/(p:ℝ))))
          * ((((∏ q ∈ P', q) : ℕ) : ℝ) * Real.exp (-(∑ q ∈ P', (1:ℝ)/q))) := by
          refine mul_le_mul hfac hih (by positivity) (by positivity)
      _ = (((p * ∏ q ∈ P', q : ℕ)) : ℝ)
          * Real.exp (-(1/(p:ℝ) + ∑ q ∈ P', (1:ℝ)/q)) := by
          push_cast
          rw [neg_add, Real.exp_add]
          ring


/-- **The 𝒰-split** (Track R, W2c-v-i): restricting a `1`-bounded sum
over an interval to the integers with a factor in the prime set `P`
costs at most the sifted count `φ(Q)((b−a)/Q + 1)` — and the
restricted sum is exactly the `ω_P ≥ 1` set that the Ramaré
decomposition (C4e-4/5/6) factors through the prime fibres. -/
theorem norm_sum_sub_sift_le (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) :
    ‖(∑ m ∈ Finset.Ioc a b, g m)
        - ∑ m ∈ (Finset.Ioc a b).filter
            (fun m => 0 < (P.filter (· ∣ m)).card), g m‖
      ≤ (((∏ p ∈ P, p).totient : ℕ) : ℝ) * (((b - a)/(∏ p ∈ P, p) + 1 : ℕ) : ℝ) := by
  classical
  have hsplit : (∑ m ∈ Finset.Ioc a b, g m)
      - ∑ m ∈ (Finset.Ioc a b).filter
          (fun m => 0 < (P.filter (· ∣ m)).card), g m
      = ∑ m ∈ (Finset.Ioc a b).filter
          (fun m => ¬ 0 < (P.filter (· ∣ m)).card), g m := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc a b)
      (fun m => 0 < (P.filter (· ∣ m)).card) g]
    ring
  rw [hsplit]
  have hchar : (Finset.Ioc a b).filter
      (fun m => ¬ 0 < (P.filter (· ∣ m)).card)
      = (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m) := by
    refine Finset.filter_congr fun m _ => ?_
    simp only [Nat.pos_iff_ne_zero, not_not, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
  rw [hchar]
  calc ‖∑ m ∈ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m), g m‖
      ≤ ∑ m ∈ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m), ‖g m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ) :=
        Finset.sum_le_sum fun m _ => hg m
    _ = (((Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (((∏ p ∈ P, p).totient : ℕ) : ℝ)
          * (((b - a)/(∏ p ∈ P, p) + 1 : ℕ) : ℝ) := by
        have h1 := card_filter_not_dvd_le a b P hP
        have h2 : (((Finset.Ioc a b).filter
            (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ)
            ≤ (((∏ p ∈ P, p).totient * ((b - a)/(∏ p ∈ P, p) + 1) : ℕ) : ℝ) := by
          exact_mod_cast h1
        calc (((Finset.Ioc a b).filter
            (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ)
            ≤ (((∏ p ∈ P, p).totient * ((b - a)/(∏ p ∈ P, p) + 1) : ℕ) : ℝ) := h2
          _ = (((∏ p ∈ P, p).totient : ℕ) : ℝ)
              * (((b - a)/(∏ p ∈ P, p) + 1 : ℕ) : ℝ) := by
              push_cast
              ring


/-- Phase multiplicativity at a product index: `e(−log(pm)·ξ) =
e(−log p·ξ)·e(−log m·ξ)` for nonzero `p, m`. -/
theorem char_log_mul (p m : ℕ) (hp : p ≠ 0) (hm : m ≠ 0) (ξ : ℝ) :
    ((Real.fourierChar (-(Real.log ((p*m : ℕ)) * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply,
    ← Complex.exp_add]
  congr 1
  have hlog : Real.log ((p*m : ℕ)) = Real.log p + Real.log m := by
    push_cast
    exact Real.log_mul (by exact_mod_cast hp) (by exact_mod_cast hm)
  rw [hlog]
  push_cast
  ring

/-- **The 𝒰-phase decomposition** (Track R, W2c-vi-a1): at any frequency,
the `ω_P ≥ 1`-restricted `1/m`-weighted phase sum splits as the
prime-fibre main terms — each a `char(p)/p`-weighted block phase sum in
the harness currency — plus the collision terms. C4e-4 at the
phase-carrying weights plus phase multiplicativity. -/
theorem usum_phase_eq_main_add_coll (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (c : ℕ → ℂ) (ξ : ℝ) :
    ∑ m ∈ (Finset.Ioc a b).filter (fun m => 0 < (P.filter (· ∣ m)).card),
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = (∑ p ∈ P, (((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
          * ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'),
              ((c (p*m')/(((P.filter (· ∣ m')).card : ℂ) + 1))/(m':ℂ))
                * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ))
        + ∑ p ∈ P, ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
            ((c (p*m')/((p*m' : ℕ) : ℂ))
                * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
              / (((P.filter (· ∣ (p*m'))).card : ℂ)) := by
  classical
  have hmain := sum_filter_omega_pos_eq_main_add_collision a b P hP
    (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
  rw [hmain]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := (hP p hp).two_le
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    have hm'0 : m' ≠ 0 := fun h => hm'.2 (h ▸ dvd_zero p)
    rw [char_log_mul p m' (by omega) hm'0 ξ]
    have hpm'c : ((p*m' : ℕ) : ℂ) = (p:ℂ)*(m':ℂ) := by push_cast; ring
    field_simp
    push_cast
    ring


open ExpSums in
set_option maxHeartbeats 1600000 in
/-- **The one-level 𝒰-energy** (Track R, W2c-vi-b): the window energy of
the `ω_P ≥ 1`-restricted `1/m`-weighted phase sum over a near-dyadic
range is at most twice the prime-window mass times the weighted
per-fibre MVT bounds, plus a second-order collision term — the
recursion step of the `J`-level `𝒰`-iteration. -/
theorem intervalIntegral_norm_sq_usum_le (a b : ℕ) (ha1 : 1 ≤ a)
    (hab : b ≤ 2*a) (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (c : ℕ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) (K : ℝ) (hK : 0 ≤ K) :
    ∫ ξ in (-K)..K, ‖∑ m ∈ (Finset.Ioc a b).filter
        (fun m => 0 < (P.filter (· ∣ m)).card),
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ 2*((∑ p ∈ P, (1:ℝ)/p) * ∑ p ∈ P, (1:ℝ)/p *
            (2*K*(∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'),
                (1:ℝ)/(m':ℝ)^2)
              + (Real.log ((a/p+1 : ℕ)) + 1)
                * (∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'),
                    (1:ℝ)/m')))
        + 2*(2*K*(∑ p ∈ P, (1:ℝ)/p *
            ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
              (1:ℝ)/m')^2) := by
  classical
  set main : ℝ → ℂ := fun ξ => ∑ p ∈ P,
      (((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
        * ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'),
            ((c (p*m')/(((P.filter (· ∣ m')).card : ℂ) + 1))/(m':ℂ))
              * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ)
    with hmain_def
  set coll : ℝ → ℂ := fun ξ => ∑ p ∈ P,
      ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
        ((c (p*m')/((p*m' : ℕ) : ℂ))
            * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
          / (((P.filter (· ∣ (p*m'))).card : ℂ))
    with hcoll_def
  have hcont_char : ∀ u : ℕ, Continuous (fun ξ : ℝ =>
      ((Real.fourierChar (-(Real.log u * ξ)) : Circle) : ℂ)) := by
    intro u
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  have hcont_main : Continuous main := by
    rw [hmain_def]
    refine continuous_finset_sum _ fun p _ => ?_
    refine Continuous.mul ((hcont_char p).div_const _) ?_
    exact continuous_finset_sum _ fun m' _ =>
      continuous_const.mul (hcont_char m')
  have hcont_coll : Continuous coll := by
    rw [hcoll_def]
    refine continuous_finset_sum _ fun p _ => ?_
    refine continuous_finset_sum _ fun m' _ => ?_
    exact (continuous_const.mul (hcont_char _)).div_const _
  have hdecomp : ∀ ξ : ℝ, ∑ m ∈ (Finset.Ioc a b).filter
      (fun m => 0 < (P.filter (· ∣ m)).card),
      (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = main ξ + coll ξ := by
    intro ξ
    rw [hmain_def, hcoll_def]
    exact usum_phase_eq_main_add_coll a b P hP c ξ
  rw [intervalIntegral.integral_congr (g := fun ξ => ‖main ξ + coll ξ‖^2)
    (fun ξ _ => by rw [hdecomp ξ])]
  -- split the square
  have hIadd : ∫ ξ in (-K)..K, ‖main ξ + coll ξ‖^2
      ≤ 2*(∫ ξ in (-K)..K, ‖main ξ‖^2) + 2*∫ ξ in (-K)..K, ‖coll ξ‖^2 := by
    have hstep : ∫ ξ in (-K)..K, ‖main ξ + coll ξ‖^2
        ≤ ∫ ξ in (-K)..K, (2*‖main ξ‖^2 + 2*‖coll ξ‖^2) := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
      · exact ((hcont_main.add hcont_coll).norm.pow 2).intervalIntegrable _ _
      · exact ((continuous_const.mul (hcont_main.norm.pow 2)).add
          (continuous_const.mul (hcont_coll.norm.pow 2))).intervalIntegrable _ _
      · intro ξ _
        have h1 := norm_add_le (main ξ) (coll ξ)
        have h2 : (0:ℝ) ≤ ‖main ξ‖ := norm_nonneg _
        have h3 : (0:ℝ) ≤ ‖coll ξ‖ := norm_nonneg _
        have h4 : ‖main ξ + coll ξ‖^2 ≤ (‖main ξ‖ + ‖coll ξ‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [h4, sq_nonneg (‖main ξ‖ - ‖coll ξ‖)]
    rw [intervalIntegral.integral_add
      (f := fun ξ => 2 * ‖main ξ‖^2)
      (g := fun ξ => 2 * ‖coll ξ‖^2)
      ((continuous_const.mul (hcont_main.norm.pow 2)).intervalIntegrable _ _)
      ((continuous_const.mul (hcont_coll.norm.pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      at hstep
    exact hstep
  refine le_trans hIadd ?_
  -- the main-half via the frequency-weighted energy
  have hmain_bound : ∫ ξ in (-K)..K, ‖main ξ‖^2
      ≤ (∑ p ∈ P, (1:ℝ)/p) * ∑ p ∈ P, (1:ℝ)/p *
          (2*K*(∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'),
              (1:ℝ)/(m':ℝ)^2)
            + (Real.log ((a/p+1 : ℕ)) + 1)
              * (∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'),
                  (1:ℝ)/m')) := by
    have happ := intervalIntegral_norm_sq_freq_weighted_blocks_le P
      (fun p ξ => ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
      (fun p => (1:ℝ)/p)
      (by
        intro p ξ
        rw [norm_div, Complex.norm_natCast]
        have h1 : ‖((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖ = 1 := by
          exact norm_eq_of_mem_sphere _
        rw [h1])
      (fun p => (hcont_char p).div_const _)
      (fun p => (Finset.Ioc (a/p) (b/p)).filter (fun m' => ¬ p ∣ m'))
      (fun p => a/p + 1)
      (fun p m' => c (p*m')/(((P.filter (· ∣ m')).card : ℂ) + 1))
      (fun p _ => Nat.succ_le_succ (Nat.zero_le _))
      (by
        intro p _ m' hm'
        rw [Finset.mem_filter, Finset.mem_Ioc] at hm'
        exact hm'.1.1)
      (by
        intro p hp m' hm'
        rw [Finset.mem_filter, Finset.mem_Ioc] at hm'
        have hp0 : 0 < p := (hP p hp).pos
        have hdiv2 : b/p ≤ 2*(a/p) + 1 := by
          have h1 : b/p ≤ (2*a)/p := Nat.div_le_div_right hab
          have h2 : (2*a)/p < 2*(a/p) + 2 := by
            rw [Nat.div_lt_iff_lt_mul hp0]
            have h3 := Nat.div_add_mod a p
            have h4 := Nat.mod_lt a hp0
            nlinarith [h3, h4]
          omega
        dsimp only
        omega)
      (by
        intro p m'
        rw [norm_div]
        have hden : ‖(((P.filter (· ∣ m')).card : ℂ) + 1)‖
            = ((P.filter (· ∣ m')).card : ℝ) + 1 := by
          rw [show (((P.filter (· ∣ m')).card : ℂ) + 1)
              = (((P.filter (· ∣ m')).card + 1 : ℕ) : ℂ) from by push_cast; ring,
            Complex.norm_natCast]
          push_cast
          ring
        rw [hden]
        have h1 : ((P.filter (· ∣ m')).card : ℝ) + 1 ≥ 1 := by
          have : (0:ℝ) ≤ ((P.filter (· ∣ m')).card : ℝ) := Nat.cast_nonneg _
          linarith
        rw [div_le_one (by linarith)]
        exact le_trans (hc _) h1)
      K hK
    exact happ
  -- the collision-half: trivial sup then integrate
  have hcoll_sup : ∀ ξ : ℝ, ‖coll ξ‖
      ≤ ∑ p ∈ P, (1:ℝ)/p *
          ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
            (1:ℝ)/m' := by
    intro ξ
    rw [hcoll_def]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
    have hp0 : 0 < p := (hP p hp).pos
    rw [Finset.mul_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m' hm' => ?_)
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm'
    have hm'0 : 0 < m' := lt_of_le_of_lt (Nat.zero_le _) hm'.1.1
    have hω : (1:ℝ) ≤ (((P.filter (· ∣ (p*m'))).card : ℕ) : ℝ) := by
      have hpos : 0 < (P.filter (· ∣ (p*m'))).card :=
        Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, dvd_mul_right p m'⟩⟩
      exact_mod_cast hpos
    rw [norm_div, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    have hchar1 : ‖((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ)‖ = 1 :=
      norm_eq_of_mem_sphere _
    rw [hchar1, mul_one]
    have hpm0 : (0:ℝ) < ((p*m' : ℕ) : ℝ) := by
      have : 0 < p*m' := by positivity
      exact_mod_cast this
    calc ‖c (p*m')‖/((p*m' : ℕ) : ℝ)/(((P.filter (· ∣ (p*m'))).card : ℕ) : ℝ)
        ≤ 1/((p*m' : ℕ) : ℝ)/1 := by
          gcongr
          exact hc _
      _ = 1/((p*m' : ℕ) : ℝ) := by ring
      _ = (1:ℝ)/p * (1/(m':ℝ)) := by
          push_cast
          field_simp
      _ ≤ (1:ℝ)/p * ((1:ℝ)/m') := le_of_eq (by ring)
  have hcoll_bound : ∫ ξ in (-K)..K, ‖coll ξ‖^2
      ≤ 2*K*(∑ p ∈ P, (1:ℝ)/p *
          ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
            (1:ℝ)/m')^2 := by
    have hCnn : (0:ℝ) ≤ ∑ p ∈ P, (1:ℝ)/p *
        ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'), (1:ℝ)/m' := by
      refine Finset.sum_nonneg fun p _ => ?_
      refine mul_nonneg (by positivity) ?_
      exact Finset.sum_nonneg fun m' _ => by positivity
    calc ∫ ξ in (-K)..K, ‖coll ξ‖^2
        ≤ ∫ ξ in (-K)..K, (∑ p ∈ P, (1:ℝ)/p *
            ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
              (1:ℝ)/m')^2 := by
          refine intervalIntegral.integral_mono_on (by linarith) ?_
            intervalIntegrable_const ?_
          · exact (hcont_coll.norm.pow 2).intervalIntegrable _ _
          · intro ξ _
            have h1 := hcoll_sup ξ
            have h2 : (0:ℝ) ≤ ‖coll ξ‖ := norm_nonneg _
            nlinarith [h1, h2]
      _ = 2*K*(∑ p ∈ P, (1:ℝ)/p *
            ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
              (1:ℝ)/m')^2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  linarith [hmain_bound, hcoll_bound]


/-- **The subset fibre reindex** (Track R, W2c-vii-b1): the `p`-fibre of
an arbitrary finset is the dilation of its floor-quotient image — the
`C4e-2` bijection without interval structure, as the `J`-recursion's
subset-invariant requires. -/
theorem sum_filter_dvd_eq_sum_image {M : Type*} [AddCommMonoid M]
    (S : Finset ℕ) {p : ℕ} (hp : 0 < p) (h : ℕ → M) :
    ∑ n ∈ S.filter (fun n => p ∣ n), h n
      = ∑ m ∈ (S.filter (fun n => p ∣ n)).image (· / p), h (p * m) := by
  classical
  have hinj : Set.InjOn (· / p) ↑(S.filter (fun n => p ∣ n)) := by
    intro n₁ h₁ n₂ h₂ he
    have hd₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have hd₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    simp only at he
    calc n₁ = p * (n₁ / p) := (Nat.mul_div_cancel' hd₁).symm
      _ = p * (n₂ / p) := by rw [he]
      _ = n₂ := Nat.mul_div_cancel' hd₂
  rw [Finset.sum_image (f := fun m => h (p * m)) hinj]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hd := (Finset.mem_filter.mp hn).2
  rw [Nat.mul_div_cancel' hd]

/-- The quotient image of a fibre inside `(a, b]` lands in `(a/p, b/p]`. -/
theorem image_div_fibre_subset (a b : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc a b) {p : ℕ} (hp : 0 < p) :
    (S.filter (fun n => p ∣ n)).image (· / p)
      ⊆ Finset.Ioc (a/p) (b/p) := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hmem := hS (Finset.mem_filter.mp hn).1
  have hd := (Finset.mem_filter.mp hn).2
  rw [Finset.mem_Ioc] at hmem ⊢
  obtain ⟨m', rfl⟩ := hd
  rw [Nat.mul_div_cancel_left m' hp]
  constructor
  · exact (Nat.div_lt_iff_lt_mul hp).mpr (by
      rw [mul_comm]
      exact hmem.1)
  · exact (Nat.le_div_iff_mul_le hp).mpr (by
      rw [mul_comm]
      exact hmem.2)


/-- **The fibre count in a window** (Track R, A2-III, III-2c): a set
inside `(a, b]` has at most `b/d - a/d` elements divisible by `d`.  This
is the counting half of `sum_filter_dvd_eq_sum_image`: the quotient map
`n ↦ n/d` is injective on the `d`-fibre (a multiple is recovered from its
quotient) and lands in `(a/d, b/d]`, so the fibre is no larger than that
interval.  Exact for `S = Finset.Ioc a b`. -/
theorem card_filter_dvd_le_sub (a b : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc a b) {d : ℕ} (hd : 0 < d) :
    (S.filter (fun n => d ∣ n)).card ≤ b/d - a/d := by
  classical
  have hinj : Set.InjOn (· / d) ↑(S.filter (fun n => d ∣ n)) := by
    intro n₁ h₁ n₂ h₂ he
    have hd₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have hd₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    simp only at he
    calc n₁ = d * (n₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (n₂ / d) := by rw [he]
      _ = n₂ := Nat.mul_div_cancel' hd₂
  calc (S.filter (fun n => d ∣ n)).card
      = ((S.filter (fun n => d ∣ n)).image (· / d)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Ioc (a/d) (b/d)).card :=
        Finset.card_le_card (image_div_fibre_subset a b S hS hd)
    _ = b/d - a/d := Nat.card_Ioc _ _

/-- **The fibre count in a window, as a real bound** (Track R, A2-III,
III-2c): the `d`-multiples of a subset of `(a, b]` number at most
`b/d` — real division, so no floor survives to be carried around.

This is the step that converts a divisor-pair double count
`∑_{n} g(n)² ≤ ∑_{r,r'} #{n : [r,r'] ∣ n}` into a harmonic mass
`∑_{r,r'} 1/[r,r']`, which is what the Euler product
(`one_add_div_one_sub_sq_le_exp`) then sums. -/
theorem card_filter_dvd_le_div (a b : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc a b) {d : ℕ} (hd : 0 < d) :
    ((S.filter (fun n => d ∣ n)).card : ℝ) ≤ (b:ℝ)/d := by
  have h1 : (S.filter (fun n => d ∣ n)).card ≤ b/d :=
    le_trans (card_filter_dvd_le_sub a b S hS hd) (Nat.sub_le _ _)
  calc ((S.filter (fun n => d ∣ n)).card : ℝ) ≤ ((b/d : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (b:ℝ)/d := Nat.cast_div_le

/-- **The subset 𝒰-decomposition** (Track R, W2c-vii-b2a): the C4e-4
normal form at an arbitrary finset, with the prime fibres given by the
quotient images — the shape every level of the `J`-recursion produces
and consumes. -/
theorem subset_sum_omega_pos_eq_main_add_coll (S : Finset ℕ)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (g : ℕ → ℂ) :
    ∑ m ∈ S.filter (fun m => 0 < (P.filter (· ∣ m)).card), g m
      = (∑ p ∈ P, ∑ m' ∈ ((S.filter (fun n => p ∣ n)).image (· / p)).filter
            (fun m' => ¬ p ∣ m'),
          g (p*m') / (((P.filter (· ∣ m')).card : ℂ) + 1))
        + ∑ p ∈ P, ∑ m' ∈ ((S.filter (fun n => p ∣ n)).image (· / p)).filter
            (fun m' => p ∣ m'),
            g (p*m') / (((P.filter (· ∣ (p*m'))).card : ℂ)) := by
  classical
  rw [← sum_div_card_dvd_eq_sum_filter S P g]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (hP p hp).pos
  rw [sum_filter_dvd_eq_sum_image S hp0
    (fun n => g n / ((P.filter (· ∣ n)).card : ℂ))]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((S.filter (fun n => p ∣ n)).image (· / p)) (fun m' => ¬ p ∣ m')]
  congr 1
  · refine Finset.sum_congr rfl fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    rw [card_filter_dvd_mul_of_prime P hP hp hm'.2]
    push_cast
    ring
  · refine Finset.sum_congr ?_ fun m' _ => rfl
    ext m'
    simp only [Finset.mem_filter, not_not]


/-- The recursive `J`-level energy bound: the base is the dyadic MVT
mass (with the top-element slack for the `b ≤ 2a+1` recursion-stable
window), and each level pays the weighted fibre bounds one scale down
plus its collision and sift masses. -/
noncomputable def uBound (K : ℝ) : List (Finset ℕ) → ℕ → ℕ → ℝ
  | [], a, b => 2*(2*K*(∑ m ∈ Finset.Ioc a b, (1:ℝ)/(m:ℝ)^2)
        + (Real.log a + 1) * (∑ m ∈ Finset.Ioc a b, (1:ℝ)/m))
      + 4*K/(a:ℝ)^2
  | (P :: rest), a, b =>
      4*((∑ p ∈ P, (1:ℝ)/p) * ∑ p ∈ P, (1:ℝ)/p * uBound K rest (a/p) (b/p))
      + 4*(2*K*(∑ p ∈ P, (1:ℝ)/p *
          ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
            (1:ℝ)/m')^2)
      + 2*(2*K*(∑ m ∈ (Finset.Ioc a b).filter
          (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m)^2)

set_option maxHeartbeats 1600000 in
open ExpSums in
/-- **The J-level 𝒰-energy** (Track R, W2c-vii-b2b): for any level list
of prime sets, any subset of the recursion-stable window `(a, 2a+1]`,
and any `1`-bounded coefficients, the window energy is at most the
recursive bound — the MVT log is paid once, at the bottom scale. -/
theorem intervalIntegral_norm_sq_subset_le (K : ℝ) (hK : 0 ≤ K)
    (levels : List (Finset ℕ))
    (hlv : ∀ P ∈ levels, ∀ q ∈ P, q.Prime) :
    ∀ (a b : ℕ), b ≤ 2*a+1 →
    ∀ (S : Finset ℕ), S ⊆ Finset.Ioc a b →
    ∀ (c : ℕ → ℂ), (∀ m, ‖c m‖ ≤ 1) →
    ∫ ξ in (-K)..K, ‖∑ m ∈ S, (c m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ uBound K levels a b := by
  induction levels with
  | nil =>
    intro a b hab S hS c hc
    classical
    have hcont : ∀ (T : Finset ℕ), Continuous (fun ξ : ℝ => ∑ m ∈ T,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
      intro T
      refine continuous_finset_sum _ fun m _ => ?_
      refine Continuous.mul continuous_const ?_
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))
    rcases Nat.eq_zero_or_pos a with ha0 | ha1
    · -- degenerate window: S ⊆ {1} (or empty), direct sup bound
      subst ha0
      have hSsub : S ⊆ {1} := by
        intro m hm
        have := hS hm
        rw [Finset.mem_Ioc] at this
        rw [Finset.mem_singleton]
        omega
      have hsup : ∀ ξ : ℝ, ‖∑ m ∈ S, (c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ 1 := by
        intro ξ
        refine le_trans (norm_sum_le _ _) ?_
        have hpt : ∀ m ∈ S, ‖(c m/(m:ℂ))
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ 1 := by
          intro m hm
          have hmem := hSsub hm
          rw [Finset.mem_singleton] at hmem
          subst hmem
          rw [norm_mul, norm_div, Complex.norm_natCast]
          have hchar : ‖((Real.fourierChar (-(Real.log (1:ℕ) * ξ)) : Circle) : ℂ)‖ = 1 :=
            norm_eq_of_mem_sphere _
          rw [hchar, mul_one]
          norm_num
          exact hc 1
        calc ∑ m ∈ S, ‖(c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
            ≤ ∑ _m ∈ S, (1:ℝ) := Finset.sum_le_sum hpt
          _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ 1 := by
              have : S.card ≤ 1 := by
                calc S.card ≤ ({1} : Finset ℕ).card := Finset.card_le_card hSsub
                  _ = 1 := Finset.card_singleton _
              exact_mod_cast this
      have hint : ∫ ξ in (-K)..K, ‖∑ m ∈ S, (c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 ≤ 2*K := by
        calc ∫ ξ in (-K)..K, ‖∑ m ∈ S, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
            ≤ ∫ ξ in (-K)..K, (1:ℝ) := by
              refine intervalIntegral.integral_mono_on (by linarith) ?_
                intervalIntegrable_const ?_
              · exact ((hcont S).norm.pow 2).intervalIntegrable _ _
              · intro ξ _
                have h1 := hsup ξ
                have h2 : (0:ℝ) ≤ ‖∑ m ∈ S, (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ :=
                  norm_nonneg _
                nlinarith [h1, h2]
          _ = 2*K := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              ring
      interval_cases b
      · -- b = 0: S is empty, both sides zero-ish
        have hSempty : S = ∅ := by
          rw [← Finset.subset_empty]
          intro m hm
          have h1 := hS hm
          rw [Finset.mem_Ioc] at h1
          omega
        rw [hSempty]
        simp [uBound]
      · -- b = 1: the sup bound against the degenerate value
        refine le_trans hint ?_
        show (2:ℝ)*K ≤ 2*(2*K*(∑ m ∈ Finset.Ioc (0:ℕ) 1, (1:ℝ)/(m:ℝ)^2)
            + (Real.log (0:ℕ) + 1) * (∑ m ∈ Finset.Ioc (0:ℕ) 1, (1:ℝ)/m))
          + 4*K/((0:ℕ):ℝ)^2
        have hM : (∑ m ∈ Finset.Ioc (0:ℕ) 1, (1:ℝ)/(m:ℝ)^2) = 1 := by
          rw [show Finset.Ioc (0:ℕ) 1 = {1} from rfl]
          norm_num
        have hM1 : (∑ m ∈ Finset.Ioc (0:ℕ) 1, (1:ℝ)/m) = 1 := by
          rw [show Finset.Ioc (0:ℕ) 1 = {1} from rfl]
          norm_num
        have hlog0 : Real.log ((0:ℕ):ℝ) = 0 := by norm_num
        have hdiv0 : (4:ℝ)*K/((0:ℕ):ℝ)^2 = 0 := by norm_num
        rw [hM, hM1, hlog0, hdiv0]
        linarith
    set S₀ := S.filter (fun m => m ≤ 2*a) with hS₀_def
    set S₁ := S.filter (fun m => ¬ m ≤ 2*a) with hS₁_def
    have hsplit : ∀ ξ : ℝ, ∑ m ∈ S,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
        = (∑ m ∈ S₀,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          + ∑ m ∈ S₁,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      intro ξ
      rw [hS₀_def, hS₁_def]
      exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
    rw [intervalIntegral.integral_congr (g := fun ξ =>
      ‖(∑ m ∈ S₀,
          (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        + ∑ m ∈ S₁,
          (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
      (fun ξ _ => by rw [hsplit ξ])]
    have h2 : ∫ ξ in (-K)..K,
        ‖(∑ m ∈ S₀,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          + ∑ m ∈ S₁,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ 2*(∫ ξ in (-K)..K, ‖∑ m ∈ S₀,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
          + 2*∫ ξ in (-K)..K, ‖∑ m ∈ S₁,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
      have hstep : ∫ ξ in (-K)..K,
          ‖(∑ m ∈ S₀, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
            + ∑ m ∈ S₁, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
          ≤ ∫ ξ in (-K)..K,
          (2*‖∑ m ∈ S₀, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
            + 2*‖∑ m ∈ S₁, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2) := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
        · exact (((hcont S₀).add (hcont S₁)).norm.pow 2).intervalIntegrable _ _
        · exact ((continuous_const.mul ((hcont S₀).norm.pow 2)).add
            (continuous_const.mul ((hcont S₁).norm.pow 2))).intervalIntegrable _ _
        · intro ξ _
          have h1 := norm_add_le
            (∑ m ∈ S₀, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
            (∑ m ∈ S₁, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          have h4 : ‖(∑ m ∈ S₀, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
              + ∑ m ∈ S₁, (c m/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
              ≤ (‖∑ m ∈ S₀, (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
                + ‖∑ m ∈ S₁, (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
          nlinarith [h4, sq_nonneg (‖∑ m ∈ S₀, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
            - ‖∑ m ∈ S₁, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖)]
      rw [intervalIntegral.integral_add
        (f := fun ξ => 2*‖∑ m ∈ S₀, (c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
        (g := fun ξ => 2*‖∑ m ∈ S₁, (c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
        ((continuous_const.mul ((hcont S₀).norm.pow 2)).intervalIntegrable _ _)
        ((continuous_const.mul ((hcont S₁).norm.pow 2)).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hstep
      exact hstep
    refine le_trans h2 ?_
    -- the S₀-part via the MVT, masses extended to the window
    have hMVT := ExpSums.intervalIntegral_norm_sq_dyadic_poly_le a ha1 S₀
      (by
        intro m hm
        rw [hS₀_def, Finset.mem_filter] at hm
        have := hS hm.1
        rw [Finset.mem_Ioc] at this
        omega)
      (by
        intro m hm
        rw [hS₀_def, Finset.mem_filter] at hm
        exact hm.2)
      c hc K hK
    have hmono₀ : 2*K*(∑ m ∈ S₀, (1:ℝ)/(m:ℝ)^2)
        + (Real.log a + 1) * (∑ m ∈ S₀, (1:ℝ)/m)
        ≤ 2*K*(∑ m ∈ Finset.Ioc a b, (1:ℝ)/(m:ℝ)^2)
          + (Real.log a + 1) * (∑ m ∈ Finset.Ioc a b, (1:ℝ)/m) := by
      have hsub : S₀ ⊆ Finset.Ioc a b := by
        rw [hS₀_def]
        exact subset_trans (Finset.filter_subset _ _) hS
      have hm1 : (∑ m ∈ S₀, (1:ℝ)/(m:ℝ)^2)
          ≤ ∑ m ∈ Finset.Ioc a b, (1:ℝ)/(m:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
      have hm2 : (∑ m ∈ S₀, (1:ℝ)/m) ≤ ∑ m ∈ Finset.Ioc a b, (1:ℝ)/m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
      have hlog0 : (0:ℝ) ≤ Real.log a + 1 := by
        have := Real.log_nonneg (by exact_mod_cast ha1 : (1:ℝ) ≤ a)
        linarith
      nlinarith [hm1, hm2, hlog0, hK]
    -- the S₁-part: at most one element, above 2a
    have hS₁sub : S₁ ⊆ {2*a+1} := by
      intro m hm
      rw [hS₁_def, Finset.mem_filter] at hm
      have := hS hm.1
      rw [Finset.mem_Ioc] at this
      rw [Finset.mem_singleton]
      omega
    have hsup₁ : ∀ ξ : ℝ, ‖∑ m ∈ S₁,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
        ≤ 1/(a:ℝ) := by
      intro ξ
      refine le_trans (norm_sum_le _ _) ?_
      have hpt : ∀ m ∈ S₁, ‖(c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ 1/(a:ℝ) := by
        intro m hm
        have hmem := hS₁sub hm
        rw [Finset.mem_singleton] at hmem
        subst hmem
        rw [norm_mul, norm_div, Complex.norm_natCast]
        have hchar : ‖((Real.fourierChar (-(Real.log ((2*a+1 : ℕ)) * ξ)) : Circle) : ℂ)‖ = 1 :=
          norm_eq_of_mem_sphere _
        rw [hchar, mul_one]
        have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
        have h2a : (a:ℝ) ≤ ((2*a+1 : ℕ) : ℝ) := by push_cast; linarith
        have hden : (0:ℝ) < ((2*a+1 : ℕ) : ℝ) := by push_cast; linarith
        calc ‖c (2*a+1)‖/((2*a+1 : ℕ) : ℝ) ≤ 1/((2*a+1 : ℕ) : ℝ) := by
              gcongr
              exact hc _
          _ ≤ 1/(a:ℝ) := one_div_le_one_div_of_le ha0 h2a
      calc ∑ m ∈ S₁, ‖(c m/(m:ℂ))
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
          ≤ ∑ _m ∈ S₁, 1/(a:ℝ) := Finset.sum_le_sum hpt
        _ = (S₁.card : ℝ) * (1/(a:ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * (1/(a:ℝ)) := by
            have hcard : S₁.card ≤ 1 := by
              calc S₁.card ≤ ({2*a+1} : Finset ℕ).card :=
                    Finset.card_le_card hS₁sub
                _ = 1 := Finset.card_singleton _
            have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
            have hcr : (S₁.card : ℝ) ≤ 1 := by exact_mod_cast hcard
            exact mul_le_mul_of_nonneg_right hcr (by positivity)
        _ = 1/(a:ℝ) := one_mul _
    have hint₁ : ∫ ξ in (-K)..K, ‖∑ m ∈ S₁,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ 2*K/(a:ℝ)^2 := by
      have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
      calc ∫ ξ in (-K)..K, ‖∑ m ∈ S₁,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
          ≤ ∫ ξ in (-K)..K, (1/(a:ℝ))^2 := by
            refine intervalIntegral.integral_mono_on (by linarith) ?_
              intervalIntegrable_const ?_
            · exact ((hcont S₁).norm.pow 2).intervalIntegrable _ _
            · intro ξ _
              have h1 := hsup₁ ξ
              have h2 : (0:ℝ) ≤ ‖∑ m ∈ S₁, (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ :=
                norm_nonneg _
              nlinarith [h1, h2]
        _ = 2*K/(a:ℝ)^2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            field_simp
            ring
    show _ ≤ 2*(2*K*(∑ m ∈ Finset.Ioc a b, (1:ℝ)/(m:ℝ)^2)
        + (Real.log a + 1) * (∑ m ∈ Finset.Ioc a b, (1:ℝ)/m)) + 4*K/(a:ℝ)^2
    have hbridge : 4*K/(a:ℝ)^2 = 2*(2*K/(a:ℝ)^2) := by ring
    linarith [hMVT, hmono₀, hint₁, hbridge]
  | cons P rest ih =>
    intro a b hab S hS c hc
    classical
    have hP : ∀ q ∈ P, q.Prime := hlv P (by simp)
    have hrest : ∀ Q ∈ rest, ∀ q ∈ Q, q.Prime :=
      fun Q hQ => hlv Q (List.mem_cons_of_mem P hQ)
    have hcont : ∀ (T : Finset ℕ) (d : ℕ → ℂ), Continuous (fun ξ : ℝ => ∑ m ∈ T,
        (d m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
      intro T d
      refine continuous_finset_sum _ fun m _ => ?_
      refine Continuous.mul continuous_const ?_
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))
    have hcont_char : ∀ u : ℕ, Continuous (fun ξ : ℝ =>
        ((Real.fourierChar (-(Real.log u * ξ)) : Circle) : ℂ)) := by
      intro u
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))
    -- named objects
    set U := S.filter (fun m => 0 < (P.filter (· ∣ m)).card) with hU_def
    set V := S.filter (fun m => ¬ 0 < (P.filter (· ∣ m)).card) with hV_def
    set Fm : ℕ → Finset ℕ := fun p =>
      ((S.filter (fun n => p ∣ n)).image (· / p)).filter (fun m' => ¬ p ∣ m')
      with hFm_def
    set Fc : ℕ → Finset ℕ := fun p =>
      ((S.filter (fun n => p ∣ n)).image (· / p)).filter (fun m' => p ∣ m')
      with hFc_def
    set cP : ℕ → ℕ → ℂ := fun p m' =>
      c (p*m') / (((P.filter (· ∣ m')).card : ℂ) + 1) with hcP_def
    -- (1) the 𝒰-split and square split
    have hsplitS : ∀ ξ : ℝ, ∑ m ∈ S,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
        = (∑ m ∈ U,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          + ∑ m ∈ V,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      intro ξ
      rw [hU_def, hV_def]
      exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
    rw [intervalIntegral.integral_congr (g := fun ξ =>
      ‖(∑ m ∈ U,
          (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        + ∑ m ∈ V,
          (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
      (fun ξ _ => by rw [hsplitS ξ])]
    have hsq2 : ∀ (f g : ℝ → ℂ), Continuous f → Continuous g →
        (∫ ξ in (-K)..K, ‖f ξ + g ξ‖^2)
          ≤ 2*(∫ ξ in (-K)..K, ‖f ξ‖^2) + 2*∫ ξ in (-K)..K, ‖g ξ‖^2 := by
      intro f g hf hg
      have hstep : ∫ ξ in (-K)..K, ‖f ξ + g ξ‖^2
          ≤ ∫ ξ in (-K)..K, (2*‖f ξ‖^2 + 2*‖g ξ‖^2) := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
        · exact ((hf.add hg).norm.pow 2).intervalIntegrable _ _
        · exact ((continuous_const.mul (hf.norm.pow 2)).add
            (continuous_const.mul (hg.norm.pow 2))).intervalIntegrable _ _
        · intro ξ _
          have h1 := norm_add_le (f ξ) (g ξ)
          have h4 : ‖f ξ + g ξ‖^2 ≤ (‖f ξ‖ + ‖g ξ‖)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
          nlinarith [h4, sq_nonneg (‖f ξ‖ - ‖g ξ‖)]
      rw [intervalIntegral.integral_add
        (f := fun ξ => 2 * ‖f ξ‖^2)
        (g := fun ξ => 2 * ‖g ξ‖^2)
        ((continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _)
        ((continuous_const.mul (hg.norm.pow 2)).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hstep
      exact hstep
    refine le_trans (hsq2 _ _ (hcont U c) (hcont V c)) ?_
    -- (2) the sift part
    have hsift : ∫ ξ in (-K)..K, ‖∑ m ∈ V,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ 2*K*(∑ m ∈ (Finset.Ioc a b).filter
            (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m)^2 := by
      have hVsub : V ⊆ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m) := by
        intro m hm
        rw [hV_def, Finset.mem_filter] at hm
        rw [Finset.mem_filter]
        refine ⟨hS hm.1, ?_⟩
        intro p hp
        have h0 := hm.2
        simp only [Nat.pos_iff_ne_zero, not_not, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff] at h0
        exact h0 hp
      have hsup : ∀ ξ : ℝ, ‖∑ m ∈ V,
          (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
          ≤ ∑ m ∈ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m := by
        intro ξ
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_sum (fun m hm => ?_))
          (Finset.sum_le_sum_of_subset_of_nonneg hVsub (fun m _ _ => by positivity))
        rw [norm_mul, norm_div, Complex.norm_natCast]
        have hchar : ‖((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ = 1 :=
          norm_eq_of_mem_sphere _
        rw [hchar, mul_one]
        gcongr
        exact hc m
      have hMnn : (0:ℝ) ≤ ∑ m ∈ (Finset.Ioc a b).filter
          (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m :=
        Finset.sum_nonneg fun m _ => by positivity
      calc ∫ ξ in (-K)..K, ‖∑ m ∈ V,
            (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
          ≤ ∫ ξ in (-K)..K, (∑ m ∈ (Finset.Ioc a b).filter
              (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m)^2 := by
            refine intervalIntegral.integral_mono_on (by linarith) ?_
              intervalIntegrable_const ?_
            · exact ((hcont V c).norm.pow 2).intervalIntegrable _ _
            · intro ξ _
              have h1 := hsup ξ
              have h2 : (0:ℝ) ≤ ‖∑ m ∈ V, (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ :=
                norm_nonneg _
              nlinarith [h1, h2]
        _ = 2*K*(∑ m ∈ (Finset.Ioc a b).filter
              (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m)^2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
    -- (3) the 𝒰-part decomposition
    have hdecomp : ∀ ξ : ℝ, ∑ m ∈ U,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
        = (∑ p ∈ P, (((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
            * ∑ m' ∈ Fm p, (cP p m'/(m':ℂ))
              * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ))
          + ∑ p ∈ P, ∑ m' ∈ Fc p,
              ((c (p*m')/((p*m' : ℕ) : ℂ))
                * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
                / (((P.filter (· ∣ (p*m'))).card : ℂ)) := by
      intro ξ
      rw [hU_def]
      have hb2a := subset_sum_omega_pos_eq_main_add_coll S P hP
        (fun m => (c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
      rw [hb2a]
      congr 1
      · refine Finset.sum_congr rfl fun p hp => ?_
        rw [hFm_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [Finset.mem_filter] at hm'
        have hm'0 : m' ≠ 0 := fun h => hm'.2 (h ▸ dvd_zero p)
        have hp2 := (hP p hp).two_le
        rw [char_log_mul p m' (by omega) hm'0 ξ]
        rw [hcP_def]
        dsimp only
        push_cast
        ring
    rw [show (2:ℝ)*(∫ ξ in (-K)..K, ‖∑ m ∈ U,
        (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
        = 2*(∫ ξ in (-K)..K, ‖(∑ p ∈ P,
            (((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
              * ∑ m' ∈ Fm p, (cP p m'/(m':ℂ))
                * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ))
          + ∑ p ∈ P, ∑ m' ∈ Fc p,
              ((c (p*m')/((p*m' : ℕ) : ℂ))
                * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
                / (((P.filter (· ∣ (p*m'))).card : ℂ))‖^2) from by
      congr 1
      exact intervalIntegral.integral_congr (fun ξ _ => by rw [hdecomp ξ])]
    -- continuity of the two decomposition halves
    have hcont_main : Continuous (fun ξ : ℝ => ∑ p ∈ P,
        (((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
          * ∑ m' ∈ Fm p, (cP p m'/(m':ℂ))
            * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ)) := by
      refine continuous_finset_sum _ fun p _ => ?_
      refine Continuous.mul ((hcont_char p).div_const _) ?_
      exact continuous_finset_sum _ fun m' _ =>
        continuous_const.mul (hcont_char m')
    have hcont_coll : Continuous (fun ξ : ℝ => ∑ p ∈ P, ∑ m' ∈ Fc p,
        ((c (p*m')/((p*m' : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
          / (((P.filter (· ∣ (p*m'))).card : ℂ))) := by
      refine continuous_finset_sum _ fun p _ => ?_
      refine continuous_finset_sum _ fun m' _ => ?_
      exact (continuous_const.mul (hcont_char _)).div_const _
    have h2U := hsq2 _ _ hcont_main hcont_coll
    -- (4) the collision part
    have hcoll : ∫ ξ in (-K)..K, ‖∑ p ∈ P, ∑ m' ∈ Fc p,
        ((c (p*m')/((p*m' : ℕ) : ℂ))
          * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
          / (((P.filter (· ∣ (p*m'))).card : ℂ))‖^2
        ≤ 2*K*(∑ p ∈ P, (1:ℝ)/p *
            ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
              (1:ℝ)/m')^2 := by
      have hsupc : ∀ ξ : ℝ, ‖∑ p ∈ P, ∑ m' ∈ Fc p,
          ((c (p*m')/((p*m' : ℕ) : ℂ))
            * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
            / (((P.filter (· ∣ (p*m'))).card : ℂ))‖
          ≤ ∑ p ∈ P, (1:ℝ)/p *
              ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
                (1:ℝ)/m' := by
        intro ξ
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
        have hp0 : 0 < p := (hP p hp).pos
        have hFcsub : Fc p ⊆ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m') := by
          rw [hFc_def]
          intro m' hm'
          rw [Finset.mem_filter] at hm'
          rw [Finset.mem_filter]
          refine ⟨?_, hm'.2⟩
          exact image_div_fibre_subset a b S hS hp0 hm'.1
        rw [Finset.mul_sum]
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_sum (fun m' hm' => ?_))
          (Finset.sum_le_sum_of_subset_of_nonneg hFcsub (fun m' _ _ => by positivity))
        have hm'mem := hFcsub hm'
        rw [Finset.mem_filter, Finset.mem_Ioc] at hm'mem
        have hm'0 : 0 < m' := lt_of_le_of_lt (Nat.zero_le _) hm'mem.1.1
        have hω : (1:ℝ) ≤ (((P.filter (· ∣ (p*m'))).card : ℕ) : ℝ) := by
          have hpos : 0 < (P.filter (· ∣ (p*m'))).card :=
            Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, dvd_mul_right p m'⟩⟩
          exact_mod_cast hpos
        rw [norm_div, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
        have hchar1 : ‖((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ)‖ = 1 :=
          norm_eq_of_mem_sphere _
        rw [hchar1, mul_one]
        have hpm0 : (0:ℝ) < ((p*m' : ℕ) : ℝ) := by
          have h1 : 0 < p*m' := by positivity
          exact_mod_cast h1
        calc ‖c (p*m')‖/((p*m' : ℕ) : ℝ)/(((P.filter (· ∣ (p*m'))).card : ℕ) : ℝ)
            ≤ 1/((p*m' : ℕ) : ℝ)/1 := by
              gcongr
              exact hc _
          _ = 1/((p*m' : ℕ) : ℝ) := by ring
          _ = (1:ℝ)/p * (1/(m':ℝ)) := by
              push_cast
              field_simp
          _ ≤ (1:ℝ)/p * ((1:ℝ)/m') := le_of_eq (by ring)
      have hCnn : (0:ℝ) ≤ ∑ p ∈ P, (1:ℝ)/p *
          ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'), (1:ℝ)/m' := by
        refine Finset.sum_nonneg fun p _ => ?_
        refine mul_nonneg (by positivity) ?_
        exact Finset.sum_nonneg fun m' _ => by positivity
      calc ∫ ξ in (-K)..K, ‖∑ p ∈ P, ∑ m' ∈ Fc p,
            ((c (p*m')/((p*m' : ℕ) : ℂ))
              * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
              / (((P.filter (· ∣ (p*m'))).card : ℂ))‖^2
          ≤ ∫ ξ in (-K)..K, (∑ p ∈ P, (1:ℝ)/p *
              ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
                (1:ℝ)/m')^2 := by
            refine intervalIntegral.integral_mono_on (by linarith) ?_
              intervalIntegrable_const ?_
            · exact (hcont_coll.norm.pow 2).intervalIntegrable _ _
            · intro ξ _
              have h1 := hsupc ξ
              have h2 : (0:ℝ) ≤ ‖∑ p ∈ P, ∑ m' ∈ Fc p,
                  ((c (p*m')/((p*m' : ℕ) : ℂ))
                    * ((Real.fourierChar (-(Real.log ((p*m' : ℕ)) * ξ)) : Circle) : ℂ))
                    / (((P.filter (· ∣ (p*m'))).card : ℂ))‖ := norm_nonneg _
              nlinarith [h1, h2]
        _ = 2*K*(∑ p ∈ P, (1:ℝ)/p *
              ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
                (1:ℝ)/m')^2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
    -- (5) the main part: CS then the induction hypothesis per fibre
    have hmain : ∫ ξ in (-K)..K, ‖∑ p ∈ P,
        (((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
          * ∑ m' ∈ Fm p, (cP p m'/(m':ℂ))
            * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ)‖^2
        ≤ (∑ p ∈ P, (1:ℝ)/p) * ∑ p ∈ P, (1:ℝ)/p * uBound K rest (a/p) (b/p) := by
      have hCS := ExpSums.intervalIntegral_norm_sq_freq_weighted_sum_le P
        (fun p ξ => ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)/(p:ℂ))
        (fun p => (1:ℝ)/p)
        (by
          intro p ξ
          rw [norm_div, Complex.norm_natCast]
          have h1 : ‖((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖ = 1 :=
            norm_eq_of_mem_sphere _
          rw [h1])
        (fun p => (hcont_char p).div_const _)
        (fun p ξ => ∑ m' ∈ Fm p, (cP p m'/(m':ℂ))
          * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ))
        (fun p => hcont (Fm p) (cP p))
        K hK
      refine le_trans hCS ?_
      refine mul_le_mul_of_nonneg_left ?_
        (Finset.sum_nonneg fun p _ => by positivity)
      refine Finset.sum_le_sum fun p hp => ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- the induction hypothesis at the fibre window
      have hp0 : 0 < p := (hP p hp).pos
      have hFmsub : Fm p ⊆ Finset.Ioc (a/p) (b/p) := by
        rw [hFm_def]
        intro m' hm'
        rw [Finset.mem_filter] at hm'
        exact image_div_fibre_subset a b S hS hp0 hm'.1
      have hdd : b/p ≤ 2*(a/p)+1 := by
        have h1 : b/p ≤ (2*a+1)/p := Nat.div_le_div_right hab
        have h2 : (2*a+1)/p < 2*(a/p) + 2 := by
          rw [Nat.div_lt_iff_lt_mul hp0]
          have h3 := Nat.div_add_mod a p
          have h4 := Nat.mod_lt a hp0
          nlinarith [h3, h4]
        omega
      have hcP1 : ∀ m', ‖cP p m'‖ ≤ 1 := by
        intro m'
        rw [hcP_def]
        dsimp only
        rw [norm_div]
        have hden : ‖(((P.filter (· ∣ m')).card : ℂ) + 1)‖
            = ((P.filter (· ∣ m')).card : ℝ) + 1 := by
          rw [show (((P.filter (· ∣ m')).card : ℂ) + 1)
              = (((P.filter (· ∣ m')).card + 1 : ℕ) : ℂ) from by push_cast; ring,
            Complex.norm_natCast]
          push_cast
          ring
        rw [hden]
        have h1 : ((P.filter (· ∣ m')).card : ℝ) + 1 ≥ 1 := by
          have h2 : (0:ℝ) ≤ ((P.filter (· ∣ m')).card : ℝ) := Nat.cast_nonneg _
          linarith
        rw [div_le_one (by linarith)]
        exact le_trans (hc _) h1
      exact ih hrest (a/p) (b/p) hdd (Fm p) hFmsub (cP p) hcP1
    -- assemble
    show _ ≤ 4*((∑ p ∈ P, (1:ℝ)/p) * ∑ p ∈ P, (1:ℝ)/p * uBound K rest (a/p) (b/p))
        + 4*(2*K*(∑ p ∈ P, (1:ℝ)/p *
            ∑ m' ∈ (Finset.Ioc (a/p) (b/p)).filter (fun m' => p ∣ m'),
              (1:ℝ)/m')^2)
        + 2*(2*K*(∑ m ∈ (Finset.Ioc a b).filter
            (fun m => ∀ p ∈ P, ¬ p ∣ m), (1:ℝ)/m)^2)
    linarith [h2U, hmain, hcoll, hsift]


open ArithmeticFunction in
/-- **The Wirsing iteration inequality** (Track R, W2c-iii-a): the normed
scale recursion — `|T(x)|·log x` is at most the log-mesh average of
`|T|` plus the `Λ/d`-weighted averages of `|T|` at smaller scales. The
distance decay extraction iterates this inequality; the `Λf`-weights'
cancellation enters through the second sum. -/
theorem norm_T_mul_log_le (f : ℕ → ℂ) (hcm : CompletelyMultiplicativeC f)
    (hf : ∀ m, ‖f m‖ ≤ 1) (x : ℕ) :
    ‖∑ m ∈ Finset.Ioc 0 x, f m / m‖ * Real.log x
      ≤ (∑ k ∈ Finset.Ioc 0 (x-1),
          ‖∑ m ∈ Finset.Ioc 0 k, f m / m‖ * (Real.log (k+1) - Real.log k))
        + ∑ d ∈ Finset.Ioc 0 x, (vonMangoldt d) / d
            * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m / m‖ := by
  classical
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    simp
  have hid := wirsing_identity f hcm x
  have hlhs : ‖∑ m ∈ Finset.Ioc 0 x, f m / m‖ * Real.log x
      = ‖(∑ m ∈ Finset.Ioc 0 x, f m / m) * ((Real.log x : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hx))]
  rw [hlhs, hid]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
    rw [Finset.mem_Ioc] at hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hΔ : (0:ℝ) ≤ Real.log (k+1) - Real.log k := by
      have h1 : Real.log k ≤ Real.log (k+1) := by
        refine Real.log_le_log ?_ ?_
        · exact_mod_cast hk.1
        · push_cast
          linarith
      linarith
    rw [abs_of_nonneg hΔ]
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun d hd => ?_)
    rw [Finset.mem_Ioc] at hd
    have hΛ0 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd.1
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΛ0, Complex.norm_natCast]
    calc vonMangoldt d * ‖f d‖ / (d:ℝ)
          * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m / m‖
        ≤ vonMangoldt d * 1 / (d:ℝ)
            * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m / m‖ := by
          gcongr
          exact hf d
      _ = vonMangoldt d / d * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m / m‖ := by
          ring


open ArithmeticFunction in
/-- **The Cesàro von Mangoldt convolution** (Track R, M1-a): the
log-weighted Cesàro sum is the `Λf`-weighted average of the plain
Cesàro sums at divided scales — the unweighted mirror of
`sum_mul_log_div_eq_vonMangoldt_conv`. -/
theorem cesaro_mul_log_eq_vonMangoldt_conv (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (x : ℕ) :
    ∑ n ∈ Finset.Ioc 0 x, f n * ((Real.log n : ℝ) : ℂ)
      = ∑ d ∈ Finset.Ioc 0 x, ((vonMangoldt d : ℝ) : ℂ) * f d
          * ∑ m ∈ Finset.Ioc 0 (x/d), f m := by
  classical
  have hstep1 : ∀ n ∈ Finset.Ioc 0 x,
      f n * ((Real.log n : ℝ) : ℂ)
        = ∑ d ∈ Finset.Ioc 0 x,
            if d ∣ n then ((vonMangoldt d : ℝ) : ℂ) * f n else 0 := by
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
    rw [hlog, hset, Finset.sum_filter, Finset.mul_sum]
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
    (fun n => ((vonMangoldt d : ℝ) : ℂ) * f n)
  rw [Nat.zero_div] at hreindex
  rw [hreindex]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Ioc] at hm
  have hfdm : f (d * m) = f d * f m := hcm d m (by omega) (by omega)
  rw [hfdm]
  ring

/-- **The log-ratio mesh bound** (Track R, M1-b): the Cesàro log mesh
is at most `N − 1` — Stirling by bare induction, one `log(1+1/N)`
per step. -/
theorem sum_log_ratio_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, (Real.log N - Real.log n) ≤ (N : ℝ) - 1 := by
  induction N with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [Finset.sum_Ioc_succ_top (le_refl 0)]
      simp
    · push_cast
      have hstep : ∑ n ∈ Finset.Ioc 0 (k+1), (Real.log ((k:ℝ)+1) - Real.log n)
          = (∑ n ∈ Finset.Ioc 0 k, (Real.log k - Real.log n))
            + (k : ℝ) * (Real.log ((k:ℝ)+1) - Real.log k) := by
        rw [Finset.sum_Ioc_succ_top (Nat.zero_le k)]
        push_cast
        rw [show (∑ n ∈ Finset.Ioc 0 k, (Real.log ((k:ℝ)+1) - Real.log n))
            = ∑ n ∈ Finset.Ioc 0 k, ((Real.log k - Real.log n)
                + (Real.log ((k:ℝ)+1) - Real.log k)) from
          Finset.sum_congr rfl fun n _ => by ring]
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioc]
        push_cast [Nat.sub_zero]
        ring
      rw [hstep]
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk
      have hlog1 : Real.log ((k:ℝ)+1) - Real.log k ≤ 1 / (k : ℝ) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have hdiv : ((k:ℝ)+1) / k = 1 + 1/(k:ℝ) := by field_simp
        rw [hdiv]
        have := Real.log_le_sub_one_of_pos
          (by positivity : (0:ℝ) < 1 + 1/(k:ℝ))
        linarith
      have hmul : (k : ℝ) * (Real.log ((k:ℝ)+1) - Real.log k) ≤ 1 := by
        calc (k : ℝ) * (Real.log ((k:ℝ)+1) - Real.log k)
            ≤ (k : ℝ) * (1/(k:ℝ)) :=
              mul_le_mul_of_nonneg_left hlog1 hk0.le
          _ = 1 := by field_simp
      have hih := ih hk
      linarith

open ArithmeticFunction in
/-- **The Cesàro Wirsing inequality** (Track R, M1-c): the Halász
elementary preamble — `|A(x)|·log x ≤ x + ∑_{d≤x} Λ(d)·|A(x/d)|`
for completely multiplicative `1`-bounded `f`. The Cesàro mirror of
`norm_T_mul_log_le`; the analytic content of Halász enters by bounding
the `Λ`-averaged smaller-scale Cesàro sums. -/
theorem norm_cesaro_mul_log_le (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (hf : ∀ m, ‖f m‖ ≤ 1) (x : ℕ) :
    ‖∑ n ∈ Finset.Ioc 0 x, f n‖ * Real.log x
      ≤ (x : ℝ)
        + ∑ d ∈ Finset.Ioc 0 x, (vonMangoldt d)
            * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m‖ := by
  classical
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    simp
  have hsplit : (∑ n ∈ Finset.Ioc 0 x, f n) * ((Real.log x : ℝ) : ℂ)
      = (∑ n ∈ Finset.Ioc 0 x, f n * (((Real.log x - Real.log n : ℝ)) : ℂ))
        + ∑ n ∈ Finset.Ioc 0 x, f n * ((Real.log n : ℝ) : ℂ) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have hlhs : ‖∑ n ∈ Finset.Ioc 0 x, f n‖ * Real.log x
      = ‖(∑ n ∈ Finset.Ioc 0 x, f n) * ((Real.log x : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hx))]
  rw [hlhs, hsplit, cesaro_mul_log_eq_vonMangoldt_conv f hcm x]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    have hbd : ∀ n ∈ Finset.Ioc 0 x,
        ‖f n * (((Real.log x - Real.log n : ℝ)) : ℂ)‖
          ≤ Real.log x - Real.log n := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hΔ : (0:ℝ) ≤ Real.log x - Real.log n := by
        have := Real.log_le_log (by exact_mod_cast hn.1 : (0:ℝ) < n)
          (by exact_mod_cast hn.2 : (n:ℝ) ≤ x)
        linarith
      rw [abs_of_nonneg hΔ]
      calc ‖f n‖ * (Real.log x - Real.log n)
          ≤ 1 * (Real.log x - Real.log n) :=
            mul_le_mul_of_nonneg_right (hf n) hΔ
        _ = Real.log x - Real.log n := one_mul _
    refine le_trans (Finset.sum_le_sum hbd) ?_
    have := sum_log_ratio_le x hx
    linarith
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun d hd => ?_)
    rw [Finset.mem_Ioc] at hd
    have hΛ0 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΛ0]
    calc vonMangoldt d * ‖f d‖ * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m‖
        ≤ vonMangoldt d * 1 * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m‖ := by
          gcongr
          exact hf d
      _ = vonMangoldt d * ‖∑ m ∈ Finset.Ioc 0 (x/d), f m‖ := by ring


end MoltResearch
