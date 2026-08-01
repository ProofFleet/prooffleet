import MoltResearch.Discrepancy.TuranKubilius
import MoltResearch.Discrepancy.MultiplicativeC

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


end MoltResearch
