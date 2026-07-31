import MoltResearch.DiscrepancyAnalytic

/-!
# Normal-form regression examples: the analytic layer

Compile-time checks for the Track L/R analytic substrate (`LogDifferences`,
`ZetaBound`, `LandauLemma`), split from `NormalFormExamples` so that
analytic-layer changes rebuild only this file and the analytic consumers —
not the whole Track C stage tree.  Same conventions as `NormalFormExamples`:
this module imports the analytic surface and is imported by nothing.
-/

namespace MoltResearch

-- Track L Littlewood campaign (issue #3020, L4): the two-sided sandwich
-- for iterated unit differences of log — factorially exact constants.
example (k n : ℕ) (hn : 1 ≤ n) :
    (k.factorial : ℝ) / ((n : ℝ) + k + 1) ^ (k + 1)
      ≤ (-1) ^ k * ExpSums.dIter (k + 1) (fun j : ℕ => Real.log j) n :=
  (ExpSums.dIter_log_sandwich k n hn).1

-- Track L Littlewood campaign (issue #3020, cascade): the abstract k-th
-- derivative test in power form — sandwiched (j+2)-differences give the
-- recursive cascade bound, all natural powers.
example {ψ : ℕ → ℝ} {j M N H : ℕ} {μ ν : ℝ}
    (hμ : 0 < μ) (hμν : μ ≤ ν) (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N)
    (hsand : ∀ n, M ≤ n → n ≤ N + j * H →
      μ ≤ ExpSums.dIter (j + 2) ψ n ∧ ExpSums.dIter (j + 2) ψ n ≤ ν) :
    ‖∑ n ∈ Finset.Ico M (N + 1), ExpSums.e (ψ n)‖ ^ (2 ^ j)
      ≤ ExpSums.cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H : ℝ) μ ν :=
  ExpSums.vdck_pow j ψ M N H μ ν hμ hμν hH hHM hMN hsand

-- Track L Littlewood campaign (issue #3020, log phase): the cascade on
-- the zeta phase — factorial sandwich in, explicit block bound out.
example (j M N H : ℕ) (t : ℝ)
    (ht : 0 < t) (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N)
    (hwin : N + j * H + j + 2 ≤ 4 * M) :
    ‖∑ n ∈ Finset.Ico M (N + 1),
        ExpSums.e (-(t / (2 * Real.pi) * Real.log n))‖ ^ (2 ^ j)
      ≤ ExpSums.cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H : ℝ)
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((4 * M : ℕ) : ℝ) ^ (j + 2))
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) :=
  ExpSums.log_phase_block_bound j M N H t ht hH hHM hMN hwin

-- Track R strip substrate (issue #3044, phase P): the schedule head bound and
-- the crude middle bound extend left of the 1-line at the cost of the trivial
-- size `(2^{d+1})^{1-σ}`, here at the critical-strip midpoint `σ = 1/2`.
example (t : ℝ) (d K : ℕ) (ht1 : (2:ℝ)^d ≤ |t|) (ht2 : |t| ≤ 2^(d+1)) :
    ‖∑ n ∈ Finset.Ico 1 (2^(d+1)),
        ((n:ℕ):ℂ) ^ (-(((1/2 : ℝ):ℂ) - Complex.I * t))‖
      ≤ ((2:ℝ)^(d+1)) ^ (1-(1/2:ℝ))
        * (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) :=
  ExpSums.norm_sum_cpow_head_le_strip (1/2) t d K (by norm_num) (by norm_num)
    ht1 ht2

example (t : ℝ) (d : ℕ) :
    ‖∑ n ∈ Finset.Ico (2^(d+1)) (2^(d+3)),
        ((n:ℕ):ℂ) ^ (-(((1/2 : ℝ):ℂ) - Complex.I * t))‖
      ≤ 3 * ((2:ℝ)^(d+1)) ^ (1-(1/2:ℝ)) :=
  ExpSums.norm_sum_cpow_middle_le_strip (1/2) t d (by norm_num)

-- Track R strip substrate (issue #3044, phase P): the approximate functional
-- equation holds throughout the strip `re ≥ 1/2, |im| ≥ 2` — `riemannZeta`
-- itself is the finite partial sum plus the potential plus the absolutely
-- convergent telescope tail, once `N` dominates `4‖s-1‖`.
example (s : ℂ) (hσ : 1/2 ≤ s.re) (him : 2 ≤ |s.im|) (N : ℕ)
    (hN : 4 * ‖s - 1‖ ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + ExpSums.zPot s N
        + ExpSums.zTail s N :=
  ExpSums.zeta_afe_strip s N hσ him hN

-- Track R strip substrate (issue #3044, phase P): the assembled strip bound —
-- `‖ζ(σ-it)‖` is controlled by the schedule head, the crude block, the
-- potential, and the telescope tail, throughout `1/2 ≤ σ ≤ 1`,
-- `|t| ∈ [2^d, 2^{d+1}]`, `d ≥ 1`.
example (σ t : ℝ) (d K : ℕ) (hσl : 1/2 ≤ σ) (hσu : σ ≤ 1) (hd : 1 ≤ d)
    (ht1 : (2:ℝ)^d ≤ |t|) (ht2 : |t| ≤ 2^(d+1)) :
    ‖riemannZeta ((σ:ℂ) - Complex.I * t)‖
      ≤ ((2:ℝ)^(d+1)) ^ (1-σ) * (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ)
        + 7 * (2:ℝ)^(d+1) * ((2:ℝ)^(d+1)) ^ (-σ)
        + ((2^(d+4) : ℕ):ℝ) ^ (1-σ) / ‖((σ:ℂ) - Complex.I * t) - 1‖
        + 2 * ‖((σ:ℂ) - Complex.I * t) - 1‖
          * (((2^(d+4) : ℕ):ℝ) - 1) ^ (-σ) / σ :=
  ExpSums.zeta_strip_bound σ t d K hσl hσu hd ht1 ht2

-- Track R zero-free region (issue #3044, phase P6): the de la Vallée Poussin
-- region, machine-checked — there is a uniform `c₀ > 0` such that every zero
-- `β + it` of `ζ` with `|t| ≥ 8` has `β ≤ 1 - c₀/log|t|`.
example : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ β t : ℝ, 8 ≤ |t| →
    riemannZeta ((β:ℂ) + Complex.I * t) = 0 →
    β ≤ 1 - c₀ / Real.log |t| :=
  ExpSums.zeta_zero_free_region

-- Track R cheap-frame C2 (issue #3044): the Plancherel harness — the square
-- of a finite weighted translate sum factorizes into the phase sum against
-- `‖𝓕F‖²`; this is `‖F ∗ μ‖² = ∫|μ̂|²|𝓕F|²` for finitely supported `μ`.
open scoped FourierTransform ContDiff in
example (F : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (S : Finset ℕ) (w : ℕ → ℂ) (s : ℕ → ℝ) :
    ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2
      = ∫ ξ, ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
          * ‖𝓕 F ξ‖^2 :=
  ExpSums.integral_norm_sq_sum_translates F hFc hFs S w s

-- Track R cheap-frame C2-iii (issue #3044): the high-frequency regime kill —
-- derivative Plancherel plus the K⁻²-tail bound.
open scoped FourierTransform in
open LineDeriv in
example (f : SchwartzMap ℝ ℂ) :
    (4*Real.pi^2) * ∫ ξ, ξ^2 * ‖𝓕 f ξ‖^2 = ∫ y, ‖(∂_{(1:ℝ)} f) y‖^2 :=
  ExpSums.integral_sq_mul_norm_fourier_sq f

open scoped FourierTransform in
example (f : SchwartzMap ℝ ℂ) (K : ℝ) (hK : 0 < K) :
    ∫ ξ in {ξ : ℝ | K ≤ |ξ|}, ‖𝓕 f ξ‖^2
      ≤ (1/K^2) * ∫ ξ, ξ^2 * ‖𝓕 f ξ‖^2 :=
  ExpSums.setIntegral_norm_fourier_sq_le f K hK

-- Track R cheap-frame C2-i (issue #3044): the smoothed logarithmic sum is
-- uniformly bounded — the O(1)-bound with no exponentials in the proof.
example (T : ℝ) (hT : 1 ≤ T) (η : ℝ → ℝ)
    (hηsupp : ∀ u : ℝ, η u ≠ 0 → |u| ≤ 2) (B : ℝ) (hηbd : ∀ u, |η u| ≤ B)
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (S : Finset ℕ) (M₁ : ℕ)
    (hS : ∀ m ∈ S, M₁ ≤ m) (hM₁ : 1 ≤ M₁) (hTM : T ≤ M₁) (y : ℝ) :
    ‖(T:ℂ) * ∑ m ∈ S, (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ)‖
      ≤ 5 * B :=
  ExpSums.norm_smoothed_sum_le T hT η hηsupp B hηbd a ha S M₁ hS hM₁ hTM y

-- Track R cheap-frame C2-i-b (issue #3044): the smoothed logarithmic sum is
-- a smooth compactly supported function — the Schwartz-layer entry ticket.
open scoped ContDiff in
example (T : ℝ) (hT : 0 < T) (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (a : ℕ → ℂ) (S : Finset ℕ) :
    ContDiff ℝ ∞ (ExpSums.smoothedLogSum T η a S)
      ∧ HasCompactSupport (ExpSums.smoothedLogSum T η a S) :=
  ⟨ExpSums.smoothedLogSum_contDiff T η hηs a S,
   ExpSums.smoothedLogSum_hasCompactSupport T hT η hηc a S⟩

-- Track R cheap-frame C2-vi (issue #3044): the three-regime frequency split —
-- low kept explicit for C4, middle by the phase-sum sup, high by the
-- derivative energy. The C2 phase closes here.
open scoped FourierTransform ContDiff in
example (F : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (S : Finset ℕ) (w : ℕ → ℂ) (s : ℕ → ℝ)
    (K L Mmid Mtot : ℝ) (hL : 0 < L) (hMmid0 : 0 ≤ Mmid)
    (hmid : ∀ ξ : ℝ, K ≤ |ξ| → |ξ| ≤ L →
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mmid)
    (htot : ∀ ξ : ℝ,
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mtot) :
    ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2
      ≤ (∫ ξ in {ξ : ℝ | |ξ| < K},
            ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
              * ‖𝓕 F ξ‖^2)
        + Mmid^2 * (∫ ξ, ‖𝓕 F ξ‖^2)
        + Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2) :=
  ExpSums.integral_norm_sq_sum_translates_regime_split
    F hFc hFs S w s K L Mmid Mtot hL hMmid0 hmid htot

-- Track R C4a (issue #3044): the oscillation kernel — the off-diagonal decay
-- of the window-energy expansion.
example (s : ℝ) (hs : s ≠ 0) (L : ℝ) :
    ‖∫ ξ in (-L)..L, ((Real.fourierChar (-(s * ξ)) : Circle) : ℂ)‖
      ≤ 1/(Real.pi * |s|) :=
  ExpSums.norm_intervalIntegral_char_le hs L

end MoltResearch
