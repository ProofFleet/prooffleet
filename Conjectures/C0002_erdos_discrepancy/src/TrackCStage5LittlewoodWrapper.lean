import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Littlewood
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5FourierProof

/-!
# Track C: Stage 5 — VinogradovKorobov from the Littlewood L-bound (W4 of issue #2935)

**`VinogradovKorobovAssumption` is discharged from `LittlewoodLBoundAssumption`**: the
bespoke pretentious-distance interface of the §4 branch now rests on a standard
textbook L-function bound. The chain (all in `MoltResearch/Discrepancy/`):

  dist²(1, χ·n^{is}; y) = ∑_{p<y} 1/p − ∑_{p<y} Re(χ(p)p^{is})/p
    ≥ [log log y − 1]                             (Mertens floor, W1)
    − [log ‖L(χ, 1+1/log y − is)‖ + 13]           (truncated Euler bridge, W2a–W2d)
    ≥ c·log log X − O_{δ,Q,T}(1)                  (Littlewood bound, W3)

with `y = ⌊X^δ⌋₊`, which exceeds any `M` for `X` large. After this file, Theorem 1.8
rests on exactly `{LogElliottNonasymptoticAssumption, LittlewoodLBoundAssumption}`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The pretense sum against `log log`, under the Littlewood bound: the constants
`c, C` of the interface control every character twist uniformly. -/
private theorem pretense_le {c C : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hC1 : 1 ≤ C)
    (hbound : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ),
      3 ≤ y → 1 ≤ q → 1 ≤ |t| →
      ‖LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
        ≤ C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c))
    {q : ℕ} (χ : DirichletCharacter ℂ q) {y : ℕ} (hy : 3 ≤ y) {t : ℝ}
    (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
      ≤ Real.log C + (1 - c) * Real.log (Real.log ((q : ℝ) * (|t| + 2))) + 13 := by
  have hbase : (1 : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h3 : (3 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
    linarith [Real.exp_one_lt_d9]
  have hlogsplit : Real.log (C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c))
      = Real.log C + (1 - c) * Real.log (Real.log ((q : ℝ) * (|t| + 2))) := by
    rw [Real.log_mul (by linarith) (by positivity),
      Real.log_rpow (by linarith)]
  refine le_trans (sum_re_twist_div_le_log_norm_LSeries χ hy t) ?_
  have hL := hbound q χ t y hy hq ht
  rcases eq_or_lt_of_le (norm_nonneg
    (LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t))) with h0 | h0
  · rw [← h0, Real.log_zero]
    have hr1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c) :=
      calc (1 : ℝ) = Real.log ((q : ℝ) * (|t| + 2)) ^ (0 : ℝ) :=
            (Real.rpow_zero _).symm
        _ ≤ Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c) :=
            Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hlog0 : 0 ≤ Real.log (C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c)) :=
      Real.log_nonneg (by nlinarith)
    rw [hlogsplit] at hlog0
    linarith
  · have := Real.log_le_log h0 hL
    rw [hlogsplit] at this
    linarith

set_option maxHeartbeats 1600000 in
/-- **The Vinogradov–Korobov interface, discharged from the Littlewood L-bound**
(issue #2935, W4): every character twist in the critical frequency range is
pretentiously far from `1` at scale `⌊X^δ⌋₊`, eventually in `X`. -/
instance (priority := 100) vinogradovKorobov_of_littlewoodLBound
    [LittlewoodLBoundAssumption] : VinogradovKorobovAssumption where
  twist_far := by
    intro Q T M hQ hT δ hδ0 hδ1
    obtain ⟨c, C, hc0, hc1, hC1, hbound⟩ := littlewood_LBound
    -- the eventual threshold
    set K : ℝ := Real.log (δ / 2) - 14 - Real.log C - (1 - c) * Real.log 2 with hK
    refine ⟨max (max ((3 : ℝ) ^ (1 / δ)) (Real.exp ((2 / δ) * Real.log 2)))
      (max (Q * (T + 2)) (max (Real.exp (Real.exp 1))
        (Real.exp (Real.exp ((M - K) / c))))), fun X hX q χ hq hqQ s hs hsT => ?_⟩
    -- unpack the threshold
    have hXa : (3 : ℝ) ^ (1 / δ) ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
    have hXc : Real.exp ((2 / δ) * Real.log 2) ≤ X :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
    have hXd : Q * (T + 2) ≤ X :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
    have hXe : Real.exp (Real.exp 1) ≤ X :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hX))
    have hXf : Real.exp (Real.exp ((M - K) / c)) ≤ X :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hX))
    -- basic positivity
    have hX1 : (1 : ℝ) < X := lt_of_lt_of_le
      (by nlinarith [Real.add_one_le_exp (Real.exp 1), Real.exp_pos 1]) hXe
    have hX0 : (0 : ℝ) < X := by linarith
    have hlogX : (1 : ℝ) ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hX0]
      calc Real.exp 1 ≤ Real.exp (Real.exp 1) :=
            Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (1 : ℝ)])
        _ ≤ X := hXe
    have hloglogX : Real.exp 1 ≤ Real.log X := by
      rw [show Real.exp 1 = Real.log (Real.exp (Real.exp 1)) from
        (Real.log_exp _).symm]
      exact Real.log_le_log (Real.exp_pos _) hXe
    -- (a): X^δ ≥ 3, hence y ≥ 3 and |s| ≥ 1
    have hXd3 : (3 : ℝ) ≤ X ^ δ := by
      calc (3 : ℝ) = ((3 : ℝ) ^ (1 / δ)) ^ δ := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), one_div,
              inv_mul_cancel₀ (ne_of_gt hδ0), Real.rpow_one]
        _ ≤ X ^ δ := Real.rpow_le_rpow (by positivity) hXa hδ0.le
    set y : ℕ := ⌊X ^ δ⌋₊ with hy_def
    have hy3 : 3 ≤ y := by
      rw [hy_def]
      exact Nat.le_floor (by exact_mod_cast hXd3)
    have hs1 : (1 : ℝ) ≤ |s| := le_trans (by linarith) hs
    -- (c): log y ≥ (δ/2)·log X
    have hyX : (X ^ δ) - 1 ≤ y := by
      rw [hy_def]
      have := Nat.sub_one_lt_floor (X ^ δ)
      linarith
    have hXd2 : (2 : ℝ) ≤ X ^ δ := by linarith
    have hy_half : X ^ δ / 2 ≤ y := by
      have : X ^ δ / 2 ≤ X ^ δ - 1 := by linarith
      linarith
    have hlogy : (δ / 2) * Real.log X ≤ Real.log y := by
      have h1 : Real.log (X ^ δ / 2) ≤ Real.log y :=
        Real.log_le_log (by positivity) hy_half
      have h2 : Real.log (X ^ δ / 2) = δ * Real.log X - Real.log 2 := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hX0]
      have h3 : Real.log 2 ≤ (δ / 2) * Real.log X := by
        have h4 : (2 / δ) * Real.log 2 ≤ Real.log X := by
          rw [Real.le_log_iff_exp_le hX0]
          exact hXc
        have hδ2 : (0 : ℝ) < δ / 2 := by linarith
        calc Real.log 2 = (δ / 2) * ((2 / δ) * Real.log 2) := by
              field_simp
            _ ≤ (δ / 2) * Real.log X := by nlinarith
      linarith
    have hlogy0 : (0 : ℝ) < Real.log y := by
      have : (0 : ℝ) < (δ / 2) * Real.log X := by positivity
      linarith
    have hloglogy : Real.log (δ / 2) + Real.log (Real.log X) ≤ Real.log (Real.log y) := by
      have h1 : Real.log ((δ / 2) * Real.log X) ≤ Real.log (Real.log y) :=
        Real.log_le_log (by positivity) hlogy
      rw [Real.log_mul (by positivity) (by positivity)] at h1
      exact h1
    -- (d): log log(q(|s|+2)) ≤ log 2 + log log X
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have harg_le : (q : ℝ) * (|s| + 2) ≤ Q * (T + 2) * X := by
      have h1 : |s| + 2 ≤ T * X + 2 := by linarith
      have h2 : T * X + 2 ≤ (T + 2) * X := by nlinarith
      have h3 : (0 : ℝ) < |s| + 2 := by positivity
      nlinarith
    have harg3 : (3 : ℝ) ≤ (q : ℝ) * (|s| + 2) := by nlinarith [abs_nonneg s]
    have hll_le : Real.log (Real.log ((q : ℝ) * (|s| + 2)))
        ≤ Real.log 2 + Real.log (Real.log X) := by
      have h1 : Real.log ((q : ℝ) * (|s| + 2)) ≤ Real.log (Q * (T + 2) * X) :=
        Real.log_le_log (by linarith) harg_le
      have h2 : Real.log (Q * (T + 2) * X) = Real.log (Q * (T + 2)) + Real.log X := by
        rw [Real.log_mul (by positivity) (ne_of_gt hX0)]
      have h3 : Real.log (Q * (T + 2)) ≤ Real.log X := by
        refine Real.log_le_log (by positivity) hXd
      have h4 : Real.log ((q : ℝ) * (|s| + 2)) ≤ 2 * Real.log X := by linarith
      have h5 : (0 : ℝ) < Real.log ((q : ℝ) * (|s| + 2)) := by
        have := Real.log_le_log (show (0:ℝ) < 3 by norm_num) harg3
        have h6 : (1 : ℝ) < Real.log 3 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num)]
          linarith [Real.exp_one_lt_d9]
        calc (0 : ℝ) < Real.log 3 := by linarith
          _ ≤ Real.log ((q : ℝ) * (|s| + 2)) := this
      calc Real.log (Real.log ((q : ℝ) * (|s| + 2)))
          ≤ Real.log (2 * Real.log X) := Real.log_le_log h5 h4
        _ = Real.log 2 + Real.log (Real.log X) := by
            rw [Real.log_mul (by norm_num) (by linarith)]
    -- the pretense bound
    have hpret := pretense_le hc0 hc1 hC1 hbound χ hy3 hq hs1
    -- the Mertens floor
    have hfloor := log_log_le_sum_one_div_primesBelow (y := y) (by omega)
    -- the distance identity
    have hdist : pretentiousDistSq (fun _ => 1) (charTwist q χ s) y
        = (∑ p ∈ y.primesBelow, (1 : ℝ) / p)
          - ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * s)).re / p := by
      rw [pretentiousDistSq, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [charTwist, one_mul]
      rw [Complex.conj_re]
      ring
    rw [hdist]
    -- final arithmetic
    have hM : M ≤ c * Real.log (Real.log X) + K := by
      have h2 : Real.exp ((M - K) / c) ≤ Real.log X := by
        rw [show Real.exp ((M - K) / c)
            = Real.log (Real.exp (Real.exp ((M - K) / c))) from
          (Real.log_exp _).symm]
        exact Real.log_le_log (Real.exp_pos _) hXf
      have h1 : (M - K) / c ≤ Real.log (Real.log X) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        exact h2
      have hMc : M - K ≤ c * Real.log (Real.log X) := by
        calc M - K = c * ((M - K) / c) := by field_simp
          _ ≤ c * Real.log (Real.log X) := by nlinarith
      linarith
    calc M ≤ c * Real.log (Real.log X) + K := hM
      _ = (Real.log (δ / 2) + Real.log (Real.log X) - 1)
          - (Real.log C + (1 - c) * (Real.log 2 + Real.log (Real.log X)) + 13) := by
          rw [hK]
          ring
      _ ≤ ((∑ p ∈ y.primesBelow, (1 : ℝ) / p) + 1 - 1)
          - (Real.log C + (1 - c) * Real.log (Real.log ((q : ℝ) * (|s| + 2))) + 13) := by
          have h1 : Real.log (δ / 2) + Real.log (Real.log X)
              ≤ (∑ p ∈ y.primesBelow, (1 : ℝ) / p) + 1 :=
            le_trans hloglogy (le_trans hfloor (by linarith))
          have h2 : (1 - c) * Real.log (Real.log ((q : ℝ) * (|s| + 2)))
              ≤ (1 - c) * (Real.log 2 + Real.log (Real.log X)) := by
            have hc' : (0 : ℝ) ≤ 1 - c := by linarith
            nlinarith
          linarith
      _ ≤ (∑ p ∈ y.primesBelow, (1 : ℝ) / p)
          - ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * s)).re / p := by
          linarith [hpret]

/-- **Milestone restatement**: Theorem 1.8 now rests on exactly
`{LogElliottNonasymptoticAssumption, LittlewoodLBoundAssumption}` — the
Vinogradov–Korobov pretense interface is fully reduced to a standard L-function
bound. -/
theorem theorem18_of_logElliott_littlewood
    [LogElliottNonasymptoticAssumption] [LittlewoodLBoundAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, sndMomentPartialSum G n ≤ C :=
  theorem18_of_logElliott_vinogradovKorobov μ G

/-- **EDP milestone**: the Erdős discrepancy theorem for all sign sequences,
conditional on exactly the nonasymptotic Elliott estimate and a Littlewood-strength
L-function bound. -/
theorem edp_of_logElliott_littlewood
    [LogElliottNonasymptoticAssumption] [LittlewoodLBoundAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  edp_of_logElliott_vinogradovKorobov f hf

end Tao2015

end MoltResearch
