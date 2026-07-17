import MoltResearch.Discrepancy.UniformCounting
import Mathlib.Probability.Moments.SubGaussian

/-!
# Discrepancy: sub-Gaussian bounds on uniform spaces

Track C, Elliott campaign (issue #2946, E6e-2): bounded mean-zero functions on a
finite uniform space are sub-Gaussian (Hoeffding's lemma), and the bound lifts
through coordinate evaluation to the product uniform — the hypotheses of
Mathlib's Hoeffding inequality, assembled for the counting world.
-/

namespace MoltResearch

open MeasureTheory ProbabilityTheory
open scoped NNReal

section UniformIntegral

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Integration against the uniform measure is averaging. -/
theorem integral_uniform (f : α → ℝ) :
    ∫ x, f x ∂((PMF.uniformOfFintype α).toMeasure)
      = (∑ x, f x) / Fintype.card α := by
  rw [integral_fintype _ (Integrable.of_finite)]
  simp_rw [uniform_real_singleton, smul_eq_mul, one_div_mul_eq_div]
  rw [← Finset.sum_div]

/-- **Hoeffding's lemma on a uniform space**: a `[-c, c]`-bounded function with
zero sum is sub-Gaussian with parameter `c²`. -/
theorem hasSubgaussianMGF_uniform (f : α → ℝ) {c : ℝ≥0}
    (hbound : ∀ x, f x ∈ Set.Icc (-(c : ℝ)) c) (hmean : ∑ x, f x = 0) :
    HasSubgaussianMGF f (c ^ 2) ((PMF.uniformOfFintype α).toMeasure) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := (PMF.uniformOfFintype α).toMeasure) (X := f)
    (measurable_of_finite f).aemeasurable (ae_of_all _ hbound)
    (by rw [integral_uniform, hmean, zero_div])
  have hconst : (‖(c : ℝ) - -(c : ℝ)‖₊ / 2) ^ 2 = c ^ 2 := by
    have h2 : ((c : ℝ) - -(c : ℝ)) = 2 * (c : ℝ) := by ring
    apply NNReal.coe_injective
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, h2, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    push_cast
    ring
  rw [hconst] at h
  exact h

end UniformIntegral

section ProductLift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
  [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] [∀ i, MeasurableSpace (Ω i)]
  [∀ i, MeasurableSingletonClass (Ω i)]

/-- A coordinate-wise sub-Gaussian bound lifts to the product uniform. -/
theorem hasSubgaussianMGF_eval_uniformPi (f : Π i, Ω i → ℝ) (i : ι) {c : ℝ≥0}
    (h : HasSubgaussianMGF (f i) c ((PMF.uniformOfFintype (Ω i)).toMeasure)) :
    HasSubgaussianMGF (fun ω => f i (ω i)) c (uniformPi Ω) := by
  have hmp : (uniformPi Ω).map (fun ω => ω i)
      = (PMF.uniformOfFintype (Ω i)).toMeasure := by
    rw [uniformPi]
    exact (measurePreserving_eval _ i).map_eq
  have h' : HasSubgaussianMGF (f i ∘ fun ω => ω i) c (uniformPi Ω) :=
    HasSubgaussianMGF.of_map (measurable_of_finite _).aemeasurable
      (by rw [hmp]; exact h)
  exact h'

/-- **Hoeffding's inequality in counting form**: bounded mean-zero coordinate
functions on the product uniform deviate exponentially rarely. -/
theorem card_deviation_le_uniformPi (f : Π i, Ω i → ℝ) (c : ι → ℝ≥0)
    (hbound : ∀ i, ∀ x, f i x ∈ Set.Icc (-(c i : ℝ)) (c i))
    (hmean : ∀ i, ∑ x, f i x = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ((Finset.univ.filter
        (fun ω : Π i, Ω i => ε ≤ ∑ i, f i (ω i))).card : ℝ)
        / Fintype.card (Π i, Ω i)
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ i, (c i) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  have hsub : ∀ i ∈ Finset.univ, HasSubgaussianMGF
      (fun ω : Π j, Ω j => f i (ω i)) ((c i) ^ 2) (uniformPi Ω) := fun i _ =>
    hasSubgaussianMGF_eval_uniformPi f i
      (hasSubgaussianMGF_uniform (f i) (hbound i) (hmean i))
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (iIndepFun_eval_uniformPi f) hsub hε
  rw [uniformPi_real_filter (fun ω => ε ≤ ∑ i, f i (ω i))] at hH
  exact hH

end ProductLift

end MoltResearch
