import MoltResearch.Discrepancy.ParsevalBridge
import MoltResearch.Discrepancy.TypicalFactorization
import MoltResearch.Discrepancy.HalaszComplex

/-!
# Track C: the window assembly (Track R, A.2 leg, G-ladder)

The end-to-end assembly of the log-averaged window bound
`∑_{n ∈ (x/w, x]} ‖W_n‖/(H·n) ≤ ε·log w` from the in-tree pieces: the
Parseval bridge's time side (`slice_time_side`), the Plancherel
harness's regime split, the `𝒰`-recursion band energies, the typical
factorization density, and the ℂ-valued plain-sum Halász.  Units are
the G-ladder of the A2-II/III design (state file): G1–G5 glue the
frequency side, G6 expands the major arc, G7 supplies the Halász sup,
G8–G10 aggregate and close.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory

/-- **G1**: an interval energy is at most the line energy, for a
nonnegative-integrand shape (norm-squared of a continuous compactly
supported profile). -/
theorem intervalIntegral_norm_sq_le_integral (G : ℝ → ℂ)
    (hGc : Continuous G) (hGs : HasCompactSupport G) (a b : ℝ) :
    ∫ y in a..b, ‖G y‖^2 ≤ ∫ y, ‖G y‖^2 := by
  have hint : Integrable (fun y => ‖G y‖^2) :=
    ((hGc.norm.pow 2)).integrable_of_hasCompactSupport
      (hGs.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp))
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab]
    refine le_trans (le_of_eq (integral_Ioc_eq_integral_Ioo)) ?_
    exact setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun y => by positivity)
  · rw [intervalIntegral.integral_of_ge hab]
    have h0 : (0:ℝ) ≤ ∫ y in Set.Ioc b a, ‖G y‖^2 :=
      setIntegral_nonneg measurableSet_Ioc fun y _ => by positivity
    have h1 : (0:ℝ) ≤ ∫ y, ‖G y‖^2 :=
      integral_nonneg fun y => by positivity
    linarith

/-- **G2**: the open-ball low band is at most the closed interval
band, for a nonnegative integrand. -/
theorem setIntegral_ball_le_intervalIntegral (φ : ℝ → ℝ)
    (hφ : Integrable φ) (hφ0 : ∀ ξ, 0 ≤ φ ξ) (K : ℝ) (hK : 0 ≤ K) :
    ∫ ξ in {ξ : ℝ | |ξ| < K}, φ ξ ≤ ∫ ξ in (-K)..K, φ ξ := by
  have hset : {ξ : ℝ | |ξ| < K} = Set.Ioo (-K) K := by
    ext ξ
    simp [abs_lt]
  rw [hset, intervalIntegral.integral_of_le (by linarith),
    ← integral_Ioc_eq_integral_Ioo]

end ExpSums

end MoltResearch
