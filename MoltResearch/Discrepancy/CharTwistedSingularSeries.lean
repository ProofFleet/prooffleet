import MoltResearch.Discrepancy.LFunctionBounds
import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# Discrepancy: the character-twisted singular series is subexponentially small

Nucleus-track module for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871, PR E2): the **non-principal character sum
bound**.  For a non-principal Dirichlet character `χ mod N` and a completely multiplicative
unimodular `h` that pretends to be `1` at scale `X`
(`pretentiousDistSq h 1 (⌊X⌋₊+1) ≤ B₀`), the `χ`-twisted singular series

`𝔖_χ = ∑'_n χ(n)·h(n)/n^{1+1/log X}`

satisfies `‖𝔖_χ‖ ≤ C(χ)·exp(√(2B₀)·√(4·log log X + 17))` — subexponentially small compared
to the `≍ log X` size of the untwisted series (paper §4, the displayed chain for the
non-principal characters ending in `≪_{q,k} exp(O_ε((log log X)^{1/2}))`; our crude
constants land `√(4·log log X + 17)` in place of the paper's `O_ε((log log X)^{1/2})`).

Proof architecture (all constants crude and explicit, mirroring
`exp_neg_mul_log_le_norm_zetaWeightedSum` and `exists_re_tsum_primes_char_le`):
- Euler product: `‖𝔖_χ‖ = exp(Re T)` with `T = ∑'_p −log(1 − χ(p)h(p)/p^σ)`, and `T`
  linearizes to the prime sum `F = ∑'_p χ(p)h(p)/p^σ` up to `1`
  (`norm_tsum_neg_log_euler_sub_le`).
- Split `χ(p)h(p) = χ(p) + χ(p)(h(p) − 1)` per prime: the pure character sum has
  `Re ≤ C'` uniformly in `X ≥ 3` (`exists_re_tsum_primes_char_le`, the analytic
  `L(s, χ)`-continuation input); the correction is `≤ ∑'_p ‖h(p) − 1‖/p^σ` in norm.
- The correction below scale `X` is controlled by **Cauchy–Schwarz**
  (`∑_{p<X} ‖h(p)−1‖/p ≤ √(∑ ‖h(p)−1‖²/p)·√(∑ 1/p)`), with the circle identity
  `‖z − 1‖² = 2(1 − Re z)` converting the first factor into `√(2·𝔻²) ≤ √(2B₀)` and the
  crude Mertens bound `sum_primesBelow_one_div_le` giving the second factor
  `√(4·log log X + 17)`; the Chebyshev tail (`sum_primes_Ioc_one_div_rpow_le`) handles
  primes above `X` (contribution `≤ 16`).
-/

namespace MoltResearch

open Finset

/-- The pointwise product of two guarded completely multiplicative sequences is guarded
completely multiplicative (the `a ≠ 0`, `b ≠ 0` guards transfer verbatim). -/
theorem CompletelyMultiplicativeC.mul {g₁ g₂ : ℕ → ℂ} (hg₁ : CompletelyMultiplicativeC g₁)
    (hg₂ : CompletelyMultiplicativeC g₂) :
    CompletelyMultiplicativeC fun n => g₁ n * g₂ n := by
  intro a b ha hb
  dsimp only
  rw [hg₁ a b ha hb, hg₂ a b ha hb]
  ring

/-- **Circle identity** (Tao 2015 §4, the Cauchy–Schwarz pivot): on the unit circle,
`‖z − 1‖² = 2·(1 − Re z)` — the squared chord length is twice the pretense summand. -/
theorem norm_sub_one_sq_eq_two_mul_one_sub_re {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  have h1 : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz, one_pow] at h
    exact h
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  linear_combination h1

private lemma one_lt_log_of_three_le {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- Against the constant-`1` comparison, `pretentiousDistSq` is the plain pretense sum. -/
private lemma pretentiousDistSq_one_eq (g : ℕ → ℂ) (N : ℕ) :
    pretentiousDistSq g (fun _ => 1) N = ∑ p ∈ N.primesBelow, (1 - (g p).re) / p := by
  unfold pretentiousDistSq
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

/-- Norm of the prime zeta-weight denominator: `‖p^σ‖ = p^σ` for a real exponent. -/
private lemma norm_prime_cpow (p : Nat.Primes) (σ : ℝ) :
    ‖((p : ℕ) : ℂ) ^ (σ : ℂ)‖ = ((p : ℕ) : ℝ) ^ σ := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.ofReal_re]

/-- Per-prime norm bound for the `χ`-twisted correction term:
`‖χ(p)(h(p) − 1)/p^σ‖ ≤ ‖h(p) − 1‖/p^σ` (characters are 1-bounded). -/
private lemma norm_char_correction_le {N : ℕ} (χ : DirichletCharacter ℂ N)
    (h : ℕ → ℂ) (σ : ℝ) (p : Nat.Primes) :
    ‖χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1) / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖
      ≤ ‖h (p : ℕ) - 1‖ / ((p : ℕ) : ℝ) ^ σ := by
  rw [norm_div, norm_mul, norm_prime_cpow]
  refine div_le_div_of_nonneg_right ?_
    (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

/-- **Cauchy–Schwarz for the pretense sum** (Tao 2015 §4): for unimodular `h`,

`∑_{p < M} ‖h(p) − 1‖/p ≤ √(2·𝔻(h,1;M)²) · √(∑_{p < M} 1/p)`,

via the per-prime factorization `‖h(p)−1‖/p = √(‖h(p)−1‖²/p)·√(1/p)` and the circle
identity `‖z−1‖² = 2(1 − Re z)`. -/
private lemma sum_norm_sub_one_div_le {h : ℕ → ℂ} (huni : Unimodular h) (M : ℕ) :
    ∑ p ∈ M.primesBelow, ‖h p - 1‖ / p
      ≤ Real.sqrt (2 * pretentiousDistSq h (fun _ => 1) M)
        * Real.sqrt (∑ p ∈ M.primesBelow, (1 : ℝ) / p) := by
  have hpt : ∀ p ∈ M.primesBelow, ‖h p - 1‖ / (p : ℝ)
      = Real.sqrt (‖h p - 1‖ ^ 2 / p) * Real.sqrt (1 / p) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos
    rw [Real.sqrt_div (sq_nonneg ‖h p - 1‖) (p : ℝ), Real.sqrt_sq (norm_nonneg (h p - 1)),
      Real.sqrt_div zero_le_one (p : ℝ), Real.sqrt_one, div_mul_div_comm, mul_one,
      Real.mul_self_sqrt hp0.le]
  have hCS : ∑ p ∈ M.primesBelow, Real.sqrt (‖h p - 1‖ ^ 2 / p) * Real.sqrt (1 / p)
      ≤ Real.sqrt (∑ p ∈ M.primesBelow, ‖h p - 1‖ ^ 2 / p)
        * Real.sqrt (∑ p ∈ M.primesBelow, (1 : ℝ) / p) :=
    Real.sum_sqrt_mul_sqrt_le (f := fun p : ℕ => ‖h p - 1‖ ^ 2 / p)
      (g := fun p : ℕ => (1 : ℝ) / p) M.primesBelow
      (fun p => div_nonneg (sq_nonneg _) (Nat.cast_nonneg p))
      (fun p => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have heq : (∑ p ∈ M.primesBelow, ‖h p - 1‖ ^ 2 / (p : ℝ))
      = 2 * pretentiousDistSq h (fun _ => 1) M := by
    rw [pretentiousDistSq_one_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_sub_one_sq_eq_two_mul_one_sub_re (huni p)]
    ring
  calc ∑ p ∈ M.primesBelow, ‖h p - 1‖ / (p : ℝ)
      = ∑ p ∈ M.primesBelow, Real.sqrt (‖h p - 1‖ ^ 2 / p) * Real.sqrt (1 / p) :=
        Finset.sum_congr rfl hpt
    _ ≤ Real.sqrt (∑ p ∈ M.primesBelow, ‖h p - 1‖ ^ 2 / p)
        * Real.sqrt (∑ p ∈ M.primesBelow, (1 : ℝ) / p) := hCS
    _ = Real.sqrt (2 * pretentiousDistSq h (fun _ => 1) M)
        * Real.sqrt (∑ p ∈ M.primesBelow, (1 : ℝ) / p) := by rw [heq]

/-- Floor absorption for the doubly-logarithmic Mertens bound:
`log log (⌊X⌋₊ + 1) ≤ log log X + 1` for `X ≥ 3` (via `⌊X⌋₊ + 1 ≤ 2X` and `log 2 ≤ 1`). -/
private lemma log_log_floor_succ_le {X : ℝ} (hX : 3 ≤ X) :
    Real.log (Real.log ((⌊X⌋₊ + 1 : ℕ) : ℝ)) ≤ Real.log (Real.log X) + 1 := by
  have hlog1 : 1 < Real.log X := one_lt_log_of_three_le hX
  have hfl : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * X := by
    push_cast
    have h1 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  have hfl4 : (4 : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by
    have h3 : 3 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
    have h4 : (4 : ℕ) ≤ ⌊X⌋₊ + 1 := by omega
    exact_mod_cast h4
  have hlog2 : Real.log 2 ≤ 1 := by
    calc Real.log 2 ≤ Real.log (Real.exp 1) :=
          Real.log_le_log (by norm_num) Real.exp_one_gt_two.le
      _ = 1 := Real.log_exp 1
  have hstep1 : Real.log ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log X := by
    calc Real.log ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (2 * X) :=
          Real.log_le_log (by linarith) hfl
      _ = Real.log 2 + Real.log X :=
          Real.log_mul (by norm_num) (show (0 : ℝ) < X by linarith).ne'
      _ ≤ 2 * Real.log X := by linarith
  have hlogfl0 : 0 < Real.log ((⌊X⌋₊ + 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
  calc Real.log (Real.log ((⌊X⌋₊ + 1 : ℕ) : ℝ))
      ≤ Real.log (2 * Real.log X) := Real.log_le_log hlogfl0 hstep1
    _ = Real.log 2 + Real.log (Real.log X) :=
        Real.log_mul (by norm_num) (show (0 : ℝ) < Real.log X by linarith).ne'
    _ ≤ Real.log (Real.log X) + 1 := by linarith

/-- **The non-principal character-twisted singular series is subexponentially small**
(Tao 2015 §4, arXiv:1509.05363, the non-principal character sum bound — the displayed
chain ending in `≪_{q,k} exp(O_ε((log log X)^{1/2}))`): for a non-principal Dirichlet
character `χ mod N` there is a constant `C = C(χ)` such that for every completely
multiplicative unimodular `h` with `h(1) = 1` pretending to be `1` at scale `X ≥ 3`
(`𝔻(h, 1; ⌊X⌋₊+1)² ≤ B₀`), the `χ`-twisted singular series at the zeta weight
`σ = 1 + 1/log X` satisfies

`‖∑'_n χ(n)h(n)/n^σ‖ ≤ C·exp(√(2B₀)·√(4·log log X + 17))`.

Compare with the untwisted lower bound `exp(−(20+B₀))·log X ≤ ‖𝔖‖`
(`exp_neg_mul_log_le_norm_zetaWeightedSum`): the twist by a non-principal character
destroys the `log X` growth. -/
theorem exists_norm_zetaWeightedSum_char_mul_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ h : ℕ → ℂ, CompletelyMultiplicativeC h → h 1 = 1 → Unimodular h →
      ∀ X : ℝ, 3 ≤ X → ∀ B₀ : ℝ,
        pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1) ≤ B₀ →
        ‖zetaWeightedSum (fun n : ℕ => χ (n : ZMod N) * h n) (1 + 1 / Real.log X)‖
          ≤ C * Real.exp (Real.sqrt (2 * B₀)
              * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
  classical
  obtain ⟨C', hC'⟩ := exists_re_tsum_primes_char_le hχ
  refine ⟨Real.exp (C' + 18), ?_⟩
  intro h hmul h1 huni X hX B₀ hpret
  have hlog1 : 1 < Real.log X := one_lt_log_of_three_le hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have h0 : 0 < 1 / Real.log X := by positivity
    linarith
  have hfloor3 : 3 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  -- the twisted sequence `g = χ·h` is completely multiplicative, normalized, 1-bounded
  set g : ℕ → ℂ := fun n : ℕ => χ (n : ZMod N) * h n with hgdef
  have hχCM : CompletelyMultiplicativeC fun n : ℕ => χ (n : ZMod N) := by
    intro a b _ _
    dsimp only
    rw [Nat.cast_mul, map_mul]
  have hgmul : CompletelyMultiplicativeC g := by
    rw [hgdef]
    exact hχCM.mul hmul
  have hg1 : g 1 = 1 := by
    rw [hgdef]
    dsimp only
    rw [Nat.cast_one, map_one, h1, mul_one]
  have hgb : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    rw [hgdef]
    dsimp only
    rw [norm_mul, huni n, mul_one]
    exact χ.norm_le_one _
  -- Euler product: `‖𝔖_χ‖ = exp (Re T)`
  have hnorm := summable_norm_zetaWeight hgb hσ
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := hgmul.zetaWeightHom hg1 (by linarith)) hnorm
  set T : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) with hTdef
  set F : ℂ := ∑' p : Nat.Primes,
    g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) with hFdef
  have hexpT : Real.exp T.re = ‖zetaWeightedSum g (1 + 1 / Real.log X)‖ := by
    rw [← Complex.norm_exp, hTdef]
    exact congrArg norm hE
  have habs : |T.re - F.re| ≤ 1 := by
    calc |T.re - F.re| = |(T - F).re| := by rw [Complex.sub_re]
      _ ≤ ‖T - F‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := norm_tsum_neg_log_euler_sub_le hgb hσ
  -- summability of the split pieces
  have hSa : Summable fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) :=
    (Real.summable_one_div_nat_rpow.mpr hσ).subtype {p | Nat.Prime p}
  have hsumFχ : Summable fun p : Nat.Primes =>
      χ ((p : ℕ) : ZMod N) / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) :=
    (summable_norm_zetaWeight (g := fun n : ℕ => χ (n : ZMod N))
      (fun n => χ.norm_le_one _) hσ).of_norm.subtype {p | Nat.Prime p}
  have hsumW : Summable fun p : Nat.Primes =>
      ‖h (p : ℕ) - 1‖ / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hSa.mul_left 2)
    rw [mul_one_div]
    refine div_le_div_of_nonneg_right ?_
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
    calc ‖h (p : ℕ) - 1‖ ≤ ‖h (p : ℕ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [huni (p : ℕ), norm_one]; norm_num
  have hsumEnorm : Summable fun p : Nat.Primes =>
      ‖χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1)
        / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_char_correction_le χ h (1 + 1 / Real.log X) p) hsumW
  have hsumE : Summable fun p : Nat.Primes =>
      χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1)
        / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) :=
    hsumEnorm.of_norm
  -- split `F = Fχ + E` via the per-prime identity `χ(p)h(p) = χ(p) + χ(p)(h(p) − 1)`
  have hFsplit : F = (∑' p : Nat.Primes,
        χ ((p : ℕ) : ZMod N) / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ))
      + ∑' p : Nat.Primes,
          χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1)
            / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) := by
    rw [hFdef, ← Summable.tsum_add hsumFχ hsumE]
    refine tsum_congr fun p => ?_
    rw [hgdef]
    dsimp only
    ring
  -- the pure character sum is bounded (the `L(s, χ)` input)
  have hFχre : (∑' p : Nat.Primes,
      χ ((p : ℕ) : ZMod N) / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re ≤ C' :=
    hC' X hX
  -- the correction is dominated by the real pretense-weighted prime sum
  have hEnorm : ‖∑' p : Nat.Primes,
      χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1)
        / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)‖
      ≤ ∑' p : Nat.Primes, ‖h (p : ℕ) - 1‖ / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) :=
    (norm_tsum_le_tsum_norm hsumEnorm).trans
      (hsumEnorm.tsum_le_tsum
        (fun p => norm_char_correction_le χ h (1 + 1 / Real.log X) p) hsumW)
  have hFre : F.re ≤ C'
      + ∑' p : Nat.Primes, ‖h (p : ℕ) - 1‖ / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
    rw [hFsplit, Complex.add_re]
    have hre2 : (∑' p : Nat.Primes,
        χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1)
          / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re
        ≤ ‖∑' p : Nat.Primes,
            χ ((p : ℕ) : ZMod N) * (h (p : ℕ) - 1)
              / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)‖ :=
      Complex.re_le_norm _
    linarith [hFχre, hEnorm]
  -- the pretense-weighted prime sum: Cauchy–Schwarz below `X`, Chebyshev tail above
  have hW : (∑' p : Nat.Primes, ‖h (p : ℕ) - 1‖ / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X))
      ≤ Real.sqrt (2 * B₀) * Real.sqrt (4 * Real.log (Real.log X) + 17) + 16 := by
    refine Real.tsum_le_of_sum_le (fun p => ?_) fun s => ?_
    · exact div_nonneg (norm_nonneg _)
        (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
    · set t : Finset ℕ := s.image (fun p : Nat.Primes => (p : ℕ)) with htdef
      have hprime_t : ∀ n ∈ t, Nat.Prime n := by
        intro n hn
        rw [htdef] at hn
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        exact p.prop
      have himg : ∑ p ∈ s, ‖h (p : ℕ) - 1‖ / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X)
          = ∑ n ∈ t, ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X) := by
        rw [htdef, Finset.sum_image]
        intro a _ b _ hab
        exact Subtype.ext hab
      rw [himg, ← Finset.sum_filter_add_sum_filter_not t (fun n => n ≤ ⌊X⌋₊)]
      have hhead : ∑ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊),
          ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X)
          ≤ Real.sqrt (2 * B₀) * Real.sqrt (4 * Real.log (Real.log X) + 17) := by
        have hpt : ∀ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊),
            ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ ‖h n - 1‖ / n := by
          intro n hn
          rw [Finset.mem_filter] at hn
          have hp := hprime_t n hn.1
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_lt.le
          have hle : (n : ℝ) ≤ (n : ℝ) ^ (1 + 1 / Real.log X) := by
            calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (n : ℝ) ^ (1 + 1 / Real.log X) :=
                Real.rpow_le_rpow_of_exponent_le hn1 hσ.le
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) hle
        have hsub1 : t.filter (fun n => n ≤ ⌊X⌋₊) ⊆ (⌊X⌋₊ + 1).primesBelow := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [Nat.mem_primesBelow]
          exact ⟨Nat.lt_succ_of_le hn.2, hprime_t n hn.1⟩
        have hmert : ∑ p ∈ (⌊X⌋₊ + 1).primesBelow, (1 : ℝ) / p
            ≤ 4 * Real.log (Real.log X) + 17 := by
          have hp13 := sum_primesBelow_one_div_le (N := ⌊X⌋₊ + 1) (by omega)
          have hll := log_log_floor_succ_le hX
          linarith
        calc ∑ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊),
              ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ ∑ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊), ‖h n - 1‖ / n := sum_le_sum hpt
          _ ≤ ∑ p ∈ (⌊X⌋₊ + 1).primesBelow, ‖h p - 1‖ / p := by
              refine sum_le_sum_of_subset_of_nonneg hsub1 fun p _ _ => by positivity
          _ ≤ Real.sqrt (2 * pretentiousDistSq h (fun _ => 1) (⌊X⌋₊ + 1))
              * Real.sqrt (∑ p ∈ (⌊X⌋₊ + 1).primesBelow, (1 : ℝ) / p) :=
              sum_norm_sub_one_div_le huni (⌊X⌋₊ + 1)
          _ ≤ Real.sqrt (2 * B₀) * Real.sqrt (4 * Real.log (Real.log X) + 17) :=
              mul_le_mul (Real.sqrt_le_sqrt (by linarith [hpret]))
                (Real.sqrt_le_sqrt hmert) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have htail : ∑ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
          ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 16 := by
        obtain ⟨B, hB⟩ := t.exists_nat_subset_range
        have hsub2 : t.filter (fun n => ¬ n ≤ ⌊X⌋₊)
            ⊆ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨by omega, ?_⟩, hprime_t n hn.1⟩
          have := hB hn.1
          rw [Finset.mem_range] at this
          exact this.le
        have hpt2 : ∀ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
            ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X)
              ≤ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          intro n hn
          rw [Finset.mem_filter] at hn
          have hp := hprime_t n hn.1
          rw [mul_one_div]
          refine div_le_div_of_nonneg_right ?_
            (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).le
          calc ‖h n - 1‖ ≤ ‖h n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [huni n, norm_one]; norm_num
        calc ∑ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
              ‖h n - 1‖ / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ ∑ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
                2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := sum_le_sum hpt2
          _ ≤ ∑ n ∈ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime,
                2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
              refine sum_le_sum_of_subset_of_nonneg hsub2 fun n _ _ => by positivity
          _ = 2 * ∑ n ∈ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime,
                1 / (n : ℝ) ^ (1 + 1 / Real.log X) := by rw [mul_sum]
          _ ≤ 2 * 8 := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact sum_primes_Ioc_one_div_rpow_le hX B
          _ = 16 := by norm_num
      exact add_le_add hhead htail
  -- assemble: `T.re ≤ C' + 18 + √(2B₀)·√(4 log log X + 17)` and exponentiate
  have hTre : T.re ≤ C' + 18
      + Real.sqrt (2 * B₀) * Real.sqrt (4 * Real.log (Real.log X) + 17) := by
    have h2' := (abs_le.mp habs).2
    linarith [hFre, hW]
  calc ‖zetaWeightedSum g (1 + 1 / Real.log X)‖
      = Real.exp T.re := hexpT.symm
    _ ≤ Real.exp (C' + 18
          + Real.sqrt (2 * B₀) * Real.sqrt (4 * Real.log (Real.log X) + 17)) :=
        Real.exp_le_exp.mpr hTre
    _ = Real.exp (C' + 18)
          * Real.exp (Real.sqrt (2 * B₀) * Real.sqrt (4 * Real.log (Real.log X) + 17)) := by
        rw [← Real.exp_add]

end MoltResearch
