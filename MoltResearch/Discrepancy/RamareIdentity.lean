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


end MoltResearch
