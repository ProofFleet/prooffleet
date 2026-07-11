import MoltResearch.Discrepancy.ZetaWeighted
import MoltResearch.Discrepancy.PrimeSumBounds
import MoltResearch.Discrepancy.PretentiousDist
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Discrepancy: the singular series `𝔖` is `≍ log X` under pretense

Nucleus module for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`, issue
#2871, PR D3): the two-sided bound (paper eq. (1s))

`exp(−(20+B₀))·log X ≤ ‖𝔖‖ ≤ 2 + log X`,  `𝔖 = zetaWeightedSum g (1 + 1/log X)`,

for completely multiplicative 1-bounded `g` that pretends to be `1` at scale `X`
(`∑_{p ≤ X} (1 − Re g(p))/p ≤ B₀`, i.e. `pretentiousDistSq g 1 (⌊X⌋₊ + 1) ≤ B₀`).

Proof architecture (Mertens-free):
- `EulerProduct.exp_tsum_primes_log_eq_tsum` writes `𝔖 = exp T` with
  `T = ∑'_p −log(1 − g(p)/p^σ)`, so `‖𝔖‖ = exp (Re T)` (`Complex.norm_exp`).
- The **log-linearization** `‖T − ∑'_p g(p)/p^σ‖ ≤ 1`: per prime
  `‖−log(1−z) − z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1/2` (`norm_log_one_sub_inv_sub_self_le`), summed
  against `∑'_p 1/p² ≤ 1` (telescoping, as in `PrimeSumBounds`).
- The prime mass `∑'_p 1/p^σ ≥ log(log X / 3) − 1` comes **from the zeta mass through the
  Euler product itself**: apply the linearization to the constant-1 function, whose `𝔖` is
  the full zeta mass `≥ log X/3` (`log_div_three_le_tsum_one_div_rpow`) — no Mertens
  theorem needed.
- Pretense transfer: `∑'_p (1 − Re g(p))/p^σ ≤ B₀ + 16` — primes `≤ X` via the hypothesis
  (`p^σ ≥ p`), primes `> X` via the Chebyshev tail (`sum_primes_Ioc_one_div_rpow_le`).
-/

namespace MoltResearch

open Finset

/-- Per-prime log linearization: `‖−log(1−z) − z‖ ≤ ‖z‖²` on the half-disc `‖z‖ ≤ 1/2`. -/
private lemma norm_neg_log_one_sub_sub_self {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hlog : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := by
    refine Complex.log_inv _ (Complex.slitPlane_arg_ne_pi ?_)
    rw [sub_eq_add_neg]
    exact Complex.mem_slitPlane_of_norm_lt_one (by rwa [norm_neg])
  have h := Complex.norm_log_one_sub_inv_sub_self_le hz1
  rw [hlog] at h
  refine h.trans ?_
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hsq : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
  calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by
        refine div_le_div_of_nonneg_right ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hinv hsq
    _ = ‖z‖ ^ 2 := by ring

/-- Finite telescoping bound: `∑_{2 ≤ n < B} 1/n² ≤ 1`. -/
private lemma sum_Ico_one_div_sq_le (B : ℕ) : ∑ n ∈ Ico 2 B, (1 / (n : ℝ)) ^ 2 ≤ 1 := by
  have hpt : ∀ n ∈ Ico 2 B, (1 / (n : ℝ)) ^ 2
      ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    rw [div_sub_div 1 1 (by linarith) (by linarith), one_mul, mul_one,
      show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring, div_pow, one_pow,
      div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  calc ∑ n ∈ Ico 2 B, (1 / (n : ℝ)) ^ 2
      ≤ ∑ n ∈ Ico 2 B, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := sum_le_sum hpt
    _ ≤ 1 := by
        have hre : ∑ n ∈ Ico 2 B, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))
            = ∑ i ∈ range (B - 2), (1 / (((i + 1) : ℕ) : ℝ) - 1 / (((i + 1 + 1) : ℕ) : ℝ)) := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine sum_congr rfl fun i _ => ?_
          have h1 : ((2 + i : ℕ) : ℝ) - 1 = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
          have h2 : ((2 + i : ℕ) : ℝ) = ((i + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
          rw [h1, h2]
        have htel := Finset.sum_range_sub'
          (f := fun i => 1 / (((i + 1) : ℕ) : ℝ)) (n := B - 2)
        rw [hre, htel]
        have h01 : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [h01]
        have hlast : 0 ≤ 1 / (((B - 2 + 1 : ℕ)) : ℝ) := by positivity
        norm_num
        linarith

/-- The prime square mass is at most `1`: `∑'_p 1/p² ≤ 1`. -/
theorem tsum_primes_one_div_sq_le :
    ∑' p : Nat.Primes, (1 / ((p : ℕ) : ℝ)) ^ 2 ≤ 1 := by
  classical
  refine Real.tsum_le_of_sum_le (fun p => by positivity) fun s => ?_
  set t : Finset ℕ := s.image (fun p : Nat.Primes => (p : ℕ)) with htdef
  have himg : ∑ p ∈ s, (1 / ((p : ℕ) : ℝ)) ^ 2 = ∑ n ∈ t, (1 / (n : ℝ)) ^ 2 := by
    rw [htdef, Finset.sum_image]
    intro a _ b _ h
    exact Subtype.ext h
  rw [himg]
  obtain ⟨B, hB⟩ := t.exists_nat_subset_range
  have hsub : t ⊆ Ico 2 B := by
    intro n hn
    rw [mem_Ico]
    constructor
    · rw [htdef] at hn
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
      exact p.prop.two_le
    · have := hB hn
      rwa [Finset.mem_range] at this
  calc ∑ n ∈ t, (1 / (n : ℝ)) ^ 2
      ≤ ∑ n ∈ Ico 2 B, (1 / (n : ℝ)) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ 1 := sum_Ico_one_div_sq_le B

section LogLinearization

variable {g : ℕ → ℂ}

/-- Real part of the zeta weight: `Re (g(n)/n^σ) = Re g(n) / n^σ`. -/
private lemma re_zetaWeight (g : ℕ → ℂ) {σ : ℝ} (n : ℕ) :
    (g n / (n : ℂ) ^ (σ : ℂ)).re = (g n).re / (n : ℝ) ^ σ := by
  rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.div_ofReal_re]

/-- The zeta weight of a 1-bounded sequence lies in the half-disc at primes:
`‖g(p)/p^σ‖ ≤ 1/p ≤ 1/2` for `σ ≥ 1`. -/
private lemma norm_zetaWeight_prime_le (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    (p : Nat.Primes) :
    ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤ 1 / ((p : ℕ) : ℝ) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  refine (norm_zetaWeight_le hb (by linarith) (p : ℕ)).trans ?_
  refine one_div_le_one_div_of_le hp0 ?_
  calc ((p : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ ((p : ℕ) : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.le

/-- **Log-linearization of the Euler product**: for completely multiplicative 1-bounded `g`
with `g 1 = 1` and `σ > 1`, the log of the Euler product differs from the naive prime sum
by at most `1`:

`‖∑'_p −log(1 − g(p)/p^σ) − ∑'_p g(p)/p^σ‖ ≤ 1`. -/
theorem norm_tsum_neg_log_euler_sub_le (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    ‖(∑' p : Nat.Primes, -Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)))
        - ∑' p : Nat.Primes, g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤ 1 := by
  have hsumℕ : Summable fun n : ℕ => g n / (n : ℂ) ^ (σ : ℂ) :=
    (summable_norm_zetaWeight hb hσ).of_norm
  have hsumP : Summable fun p : Nat.Primes => g p / ((p : ℕ) : ℂ) ^ (σ : ℂ) :=
    hsumℕ.subtype {p | Nat.Prime p}
  have hsumlog : Summable fun p : Nat.Primes =>
      -Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)) :=
    (hsumP.clog_one_sub).neg
  have hhalf : ∀ p : Nat.Primes, ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤ 1 / 2 := by
    intro p
    refine (norm_zetaWeight_prime_le hb hσ p).trans ?_
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
    exact one_div_le_one_div_of_le (by norm_num) hp2
  rw [← Summable.tsum_sub hsumlog hsumP]
  have hnormsum : Summable fun p : Nat.Primes =>
      ‖-Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)) - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ :=
    (hsumlog.sub hsumP).norm
  refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
  have hptbound : ∀ p : Nat.Primes,
      ‖-Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)) - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖
        ≤ (1 / ((p : ℕ) : ℝ)) ^ 2 := by
    intro p
    refine (norm_neg_log_one_sub_sub_self (hhalf p)).trans ?_
    have h1 : ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ ≤ 1 / ((p : ℕ) : ℝ) :=
      norm_zetaWeight_prime_le hb hσ p
    have h0 : (0 : ℝ) ≤ ‖g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  have hsq : Summable fun p : Nat.Primes => (1 / ((p : ℕ) : ℝ)) ^ 2 := by
    have : Summable fun n : ℕ => (1 / (n : ℝ)) ^ 2 := by
      have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ) :=
        Real.summable_one_div_nat_rpow.mpr (by norm_num)
      refine h2.congr fun n => ?_
      rw [div_pow, one_pow, Real.rpow_two]
    exact this.subtype {p | Nat.Prime p}
  calc ∑' p : Nat.Primes,
        ‖-Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)) - g p / ((p : ℕ) : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' p : Nat.Primes, (1 / ((p : ℕ) : ℝ)) ^ 2 :=
        hnormsum.tsum_le_tsum hptbound hsq
    _ ≤ 1 := tsum_primes_one_div_sq_le

private lemma one_lt_log' {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- **Singular-series upper bound** (Tao 2015 §4, eq. (1s), easy half): the zeta-weighted
sum of any 1-bounded sequence has norm at most the full zeta mass, `≤ 2 + log X`. -/
theorem norm_zetaWeightedSum_le (hb : ∀ n, ‖g n‖ ≤ 1) {X : ℝ} (hX : 3 ≤ X) :
    ‖zetaWeightedSum g (1 + 1 / Real.log X)‖ ≤ 2 + Real.log X := by
  have hlog1 : 1 < Real.log X := one_lt_log' hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  have hnorm : Summable fun n : ℕ => ‖g n / (n : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)‖ :=
    summable_norm_zetaWeight hb hσ
  have hzeta : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Real.summable_one_div_nat_rpow.mpr hσ
  calc ‖zetaWeightedSum g (1 + 1 / Real.log X)‖
      ≤ ∑' n : ℕ, ‖g n / (n : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
        hnorm.tsum_le_tsum (fun n => norm_zetaWeight_le hb (by linarith) n) hzeta
    _ ≤ 2 + Real.log X := tsum_one_div_rpow_le_two_add_log hX

/-- **Prime mass from the zeta mass** (Mertens-free): at `σ = 1 + 1/log X`,
`∑'_p 1/p^σ ≥ log(log X / 3) − 1` — the Euler product of the constant-1 function converts
the zeta-mass lower bound into a prime-sum lower bound through the log-linearization. -/
theorem log_log_le_tsum_primes_one_div_rpow {X : ℝ} (hX : 3 ≤ X) :
    Real.log (Real.log X / 3) - 1
      ≤ ∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
  have hlog1 : 1 < Real.log X := one_lt_log' hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  set g₀ : ℕ → ℂ := fun _ => 1 with hg₀def
  have hmul₀ : CompletelyMultiplicativeC g₀ := fun _ _ _ _ => (one_mul 1).symm
  have h1₀ : g₀ 1 = 1 := rfl
  have hb₀ : ∀ n, ‖g₀ n‖ ≤ 1 := fun _ => by rw [hg₀def]; simp
  have hnorm₀ := summable_norm_zetaWeight hb₀ hσ
  -- `𝔖₀ = exp T₀` and `Re 𝔖₀` is the real zeta mass
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := hmul₀.zetaWeightHom h1₀ (by linarith)) hnorm₀
  have hre𝔖 : (zetaWeightedSum g₀ (1 + 1 / Real.log X)).re
      = ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) := by
    rw [zetaWeightedSum]
    rw [show (∑' n : ℕ, g₀ n / (n : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re
        = Complex.reCLM (∑' n : ℕ, g₀ n / (n : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) from rfl,
      Complex.reCLM.map_tsum hnorm₀.of_norm]
    refine tsum_congr fun n => ?_
    show (g₀ n / (n : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re = _
    have := re_zetaWeight g₀ (σ := 1 + 1 / Real.log X) n
    simpa [hg₀def] using this
  have h𝔖lower : Real.log X / 3 ≤ ‖zetaWeightedSum g₀ (1 + 1 / Real.log X)‖ := by
    calc Real.log X / 3 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
          log_div_three_le_tsum_one_div_rpow hX
      _ = (zetaWeightedSum g₀ (1 + 1 / Real.log X)).re := hre𝔖.symm
      _ ≤ ‖zetaWeightedSum g₀ (1 + 1 / Real.log X)‖ := Complex.re_le_norm _
  -- so `T₀.re ≥ log (log X / 3)`
  set T₀ : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) with hT₀def
  have hexpT : Real.exp T₀.re = ‖zetaWeightedSum g₀ (1 + 1 / Real.log X)‖ := by
    rw [← Complex.norm_exp, hT₀def]
    exact congrArg norm hE
  have hT₀re : Real.log (Real.log X / 3) ≤ T₀.re := by
    have hpos : (0 : ℝ) < Real.log X / 3 := by linarith
    calc Real.log (Real.log X / 3)
        ≤ Real.log (Real.exp T₀.re) := by
          refine Real.log_le_log hpos ?_
          rw [hexpT]
          exact h𝔖lower
      _ = T₀.re := Real.log_exp _
  -- linearize: `T₀.re ≤ ∑'_p 1/p^σ + 1`
  have hsumP₀ : Summable fun p : Nat.Primes =>
      g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) :=
    hnorm₀.of_norm.subtype {p | Nat.Prime p}
  have hlin := norm_tsum_neg_log_euler_sub_le hb₀ hσ
  set F₀ : ℂ := ∑' p : Nat.Primes,
    g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) with hF₀def
  have hreF₀ : F₀.re = ∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
    rw [hF₀def]
    rw [show (∑' p : Nat.Primes,
          g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re
        = Complex.reCLM (∑' p : Nat.Primes,
            g₀ p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) from rfl,
      Complex.reCLM.map_tsum hsumP₀]
    refine tsum_congr fun p => ?_
    show (g₀ (p : ℕ) / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re = _
    have := re_zetaWeight g₀ (σ := 1 + 1 / Real.log X) (p : ℕ)
    simpa [hg₀def] using this
  have habs : |T₀.re - F₀.re| ≤ 1 := by
    calc |T₀.re - F₀.re| = |(T₀ - F₀).re| := by rw [Complex.sub_re]
      _ ≤ ‖T₀ - F₀‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := hlin
  have := abs_le.mp habs
  linarith [hT₀re, hreF₀ ▸ this.2]

/-- Against the constant-1 comparison, `pretentiousDistSq` is the plain pretense sum. -/
private lemma pretentiousDistSq_one (g : ℕ → ℂ) (N : ℕ) :
    pretentiousDistSq g (fun _ => 1) N = ∑ p ∈ N.primesBelow, (1 - (g p).re) / p := by
  unfold pretentiousDistSq
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

/-- **Singular-series lower bound** (Tao 2015 §4, eq. (1s), main half): a completely
multiplicative 1-bounded `g` that pretends to be `1` at scale `X`
(`pretentiousDistSq g 1 (⌊X⌋₊+1) ≤ B₀`) has `‖𝔖‖ ≥ exp(−(20+B₀))·log X` at the zeta
weight `σ = 1 + 1/log X`.

Proof: `𝔖 = exp T` (Euler product), `T` linearizes to the prime sum up to `1`
(`norm_tsum_neg_log_euler_sub_le`), whose main term is `≥ log(log X/3) − 1`
(`log_log_le_tsum_primes_one_div_rpow`) and whose pretense correction is
`≤ B₀ + 16` (hypothesis below scale `X`, Chebyshev tail above). -/
theorem exp_neg_mul_log_le_norm_zetaWeightedSum
    (hg : CompletelyMultiplicativeC g) (hg1 : g 1 = 1) (hb : ∀ n, ‖g n‖ ≤ 1)
    {X : ℝ} (hX : 3 ≤ X) {B₀ : ℝ}
    (hpret : pretentiousDistSq g (fun _ => 1) (⌊X⌋₊ + 1) ≤ B₀) :
    Real.exp (-(20 + B₀)) * Real.log X ≤ ‖zetaWeightedSum g (1 + 1 / Real.log X)‖ := by
  classical
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog1 : 1 < Real.log X := one_lt_log' hX
  have hσ : 1 < 1 + 1 / Real.log X := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  have hnorm := summable_norm_zetaWeight hb hσ
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := hg.zetaWeightHom hg1 (by linarith)) hnorm
  set T : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) with hTdef
  set F : ℂ := ∑' p : Nat.Primes,
    g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) with hFdef
  have hsumP : Summable fun p : Nat.Primes =>
      g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) :=
    hnorm.of_norm.subtype {p | Nat.Prime p}
  have hexpT : Real.exp T.re = ‖zetaWeightedSum g (1 + 1 / Real.log X)‖ := by
    rw [← Complex.norm_exp, hTdef]
    exact congrArg norm hE
  have habs : |T.re - F.re| ≤ 1 := by
    calc |T.re - F.re| = |(T - F).re| := by rw [Complex.sub_re]
      _ ≤ ‖T - F‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := norm_tsum_neg_log_euler_sub_le hb hσ
  have hreF : F.re = ∑' p : Nat.Primes, (g p).re / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
    rw [hFdef]
    rw [show (∑' p : Nat.Primes,
          g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re
        = Complex.reCLM (∑' p : Nat.Primes,
            g p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) from rfl,
      Complex.reCLM.map_tsum hsumP]
    exact tsum_congr fun p => re_zetaWeight g (σ := 1 + 1 / Real.log X) (p : ℕ)
  -- summabilities of the split
  have hSa : Summable fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) :=
    (Real.summable_one_div_nat_rpow.mpr hσ).subtype {p | Nat.Prime p}
  have hre_le : ∀ n : ℕ, (g n).re ≤ 1 := fun n => le_trans (Complex.re_le_norm _) (hb n)
  have hre_ge : ∀ n : ℕ, -1 ≤ (g n).re := fun n => by
    have h1 := Complex.abs_re_le_norm (g n)
    have h2 := hb n
    have := abs_le.mp (le_trans h1 h2)
    exact this.1
  have hSw : Summable fun p : Nat.Primes =>
      (1 - (g p).re) / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hSa.mul_left 2)
    · refine div_nonneg (by linarith [hre_le (p : ℕ)]) ?_
      exact (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
    · rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ ?_
      · linarith [hre_ge (p : ℕ)]
      · exact (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
  have hdecF : F.re = (∑' p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X))
      - ∑' p : Nat.Primes, (1 - (g p).re) / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) := by
    rw [hreF, ← Summable.tsum_sub hSa hSw]
    refine tsum_congr fun p => ?_
    rw [div_sub_div_same]
    ring_nf
  -- the pretense correction: below scale `X` via the hypothesis, above via the tail
  have hW : ∑' p : Nat.Primes, (1 - (g p).re) / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X)
      ≤ B₀ + 16 := by
    refine Real.tsum_le_of_sum_le (fun p => ?_) fun s => ?_
    · refine div_nonneg (by linarith [hre_le (p : ℕ)]) ?_
      exact (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
    · set t : Finset ℕ := s.image (fun p : Nat.Primes => (p : ℕ)) with htdef
      have hprime_t : ∀ n ∈ t, Nat.Prime n := by
        intro n hn
        rw [htdef] at hn
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        exact p.prop
      have himg : ∑ p ∈ s, (1 - (g (p : ℕ)).re) / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X)
          = ∑ n ∈ t, (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X) := by
        rw [htdef, Finset.sum_image]
        intro a _ b _ h
        exact Subtype.ext h
      rw [himg, ← Finset.sum_filter_add_sum_filter_not t (fun n => n ≤ ⌊X⌋₊)]
      have h1 : ∑ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊),
          (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ B₀ := by
        have hpt : ∀ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊),
            (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ (1 - (g n).re) / n := by
          intro n hn
          rw [Finset.mem_filter] at hn
          have hp := hprime_t n hn.1
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_lt.le
          have hle : (n : ℝ) ≤ (n : ℝ) ^ (1 + 1 / Real.log X) := by
            calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (n : ℝ) ^ (1 + 1 / Real.log X) :=
                Real.rpow_le_rpow_of_exponent_le hn1 hσ.le
          exact div_le_div_of_nonneg_left (by linarith [hre_le n]) (by linarith) hle
        have hsub1 : t.filter (fun n => n ≤ ⌊X⌋₊) ⊆ (⌊X⌋₊ + 1).primesBelow := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [Nat.mem_primesBelow]
          exact ⟨Nat.lt_succ_of_le hn.2, hprime_t n hn.1⟩
        calc ∑ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊),
              (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X)
            ≤ ∑ n ∈ t.filter (fun n => n ≤ ⌊X⌋₊), (1 - (g n).re) / n := sum_le_sum hpt
          _ ≤ ∑ p ∈ (⌊X⌋₊ + 1).primesBelow, (1 - (g p).re) / p := by
              refine sum_le_sum_of_subset_of_nonneg hsub1 fun p hp _ => ?_
              have hpp := (Nat.mem_primesBelow.mp hp).2
              refine div_nonneg (by linarith [hre_le p]) (Nat.cast_nonneg p)
          _ = pretentiousDistSq g (fun _ => 1) (⌊X⌋₊ + 1) := (pretentiousDistSq_one g _).symm
          _ ≤ B₀ := hpret
      have h2 : ∑ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
          (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 16 := by
        obtain ⟨B, hB⟩ := t.exists_nat_subset_range
        have hsub2 : t.filter (fun n => ¬ n ≤ ⌊X⌋₊) ⊆ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨by omega, ?_⟩, hprime_t n hn.1⟩
          have := hB hn.1
          rw [Finset.mem_range] at this
          exact this.le
        have hpt2 : ∀ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
            (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X)
              ≤ 2 * (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
          intro n hn
          rw [Finset.mem_filter] at hn
          have hp := hprime_t n hn.1
          rw [mul_one_div]
          refine div_le_div_of_nonneg_right (by linarith [hre_ge n]) ?_
          exact (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).le
        calc ∑ n ∈ t.filter (fun n => ¬ n ≤ ⌊X⌋₊),
              (1 - (g n).re) / (n : ℝ) ^ (1 + 1 / Real.log X)
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
      linarith
  -- assemble
  have hprime := log_log_le_tsum_primes_one_div_rpow hX
  have hTre : Real.log (Real.log X / 3) - 18 - B₀ ≤ T.re := by
    have hF : Real.log (Real.log X / 3) - 17 - B₀ ≤ F.re := by
      rw [hdecF]
      linarith
    have h2 := (abs_le.mp habs).1
    linarith
  have hlogpos : (0 : ℝ) < Real.log X / 3 := by linarith
  have hexp2 : Real.exp (-2 : ℝ) ≤ 1 / 3 := by
    rw [Real.exp_neg, ← one_div]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  calc Real.exp (-(20 + B₀)) * Real.log X
      = Real.exp (-(18 + B₀)) * (Real.exp (-2) * Real.log X) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(18 + B₀)) * (Real.log X / 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        calc Real.exp (-2) * Real.log X ≤ 1 / 3 * Real.log X := by
              refine mul_le_mul_of_nonneg_right hexp2 (by linarith)
          _ = Real.log X / 3 := by ring
    _ = Real.exp (-(18 + B₀)) * Real.exp (Real.log (Real.log X / 3)) := by
        rw [Real.exp_log hlogpos]
    _ = Real.exp (Real.log (Real.log X / 3) - 18 - B₀) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp T.re := Real.exp_le_exp.mpr hTre
    _ = ‖zetaWeightedSum g (1 + 1 / Real.log X)‖ := hexpT

end LogLinearization

end MoltResearch
