import MoltResearch.Discrepancy.ZeroFreeRegion

/-!
# Landau's zeta estimate at a variable radius

This leaf exposes the radius dependence already present in
`landau_inequality`.  The centre is kept at height at least one so that the
full closed ball avoids the pole of `riemannZeta`; the later growth
application works at much larger heights.  The leading constant is `16`, and
therefore specializes to `32` when the radius is `1 / 2`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- The absolute constant in the variable-radius Landau estimate. -/
def zetaLandauConstant : ℝ := 16

/-- **V-C4-1.**  Landau's estimate for `riemannZeta` at a free radius.

The height condition is the pole-separation condition needed by
`landau_inequality`: together with `R ≤ 1/2`, it ensures that the full
radius-`R` ball is contained in `ℂ \ {1}`.  The growth ratio itself is an
input, so no particular global zeta growth estimate is built into this
statement.
-/
theorem zeta_landau_core_at_radius
    (σ₀ τ R K : ℝ) (hσ1 : 1 < σ₀) (hσ2 : σ₀ ≤ 3 / 2)
    (hR0 : 0 < R) (hRhalf : R ≤ 1 / 2) (hτ : 1 ≤ |τ|) (hK : 0 ≤ K)
    (hratio : ∀ z ∈ Metric.closedBall ((σ₀ : ℂ) + I * τ) R,
      ‖riemannZeta z‖ ≤ Real.exp K *
        ‖riemannZeta ((σ₀ : ℂ) + I * τ)‖) :
    (∀ ρ ∈ Metric.closedBall ((σ₀ : ℂ) + I * τ) (R / 4),
      riemannZeta ρ = 0 →
      -(deriv riemannZeta ((σ₀ : ℂ) + I * τ) /
          riemannZeta ((σ₀ : ℂ) + I * τ)).re ≤
        zetaLandauConstant * (K + 1) / R -
          (1 / (((σ₀ : ℂ) + I * τ) - ρ)).re) ∧
      -(deriv riemannZeta ((σ₀ : ℂ) + I * τ) /
          riemannZeta ((σ₀ : ℂ) + I * τ)).re ≤
        zetaLandauConstant * (K + 1) / R := by
  have _hK : 0 ≤ K := hK
  let c : ℂ := (σ₀ : ℂ) + I * τ
  have hcre : c.re = σ₀ := by simp [c]
  have hcim : c.im = τ := by simp [c]
  have hfc : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; linarith)
  have hUopen : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    intro z hz
    exact (differentiableAt_riemannZeta
      (Set.mem_compl_singleton_iff.mp hz)).differentiableWithinAt
  have hball : Metric.closedBall c R ⊆ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz1
    have hdist : dist z c ≤ R := Metric.mem_closedBall.mp hz
    have him : |τ| ≤ ‖z - c‖ := by
      calc
        |τ| = |(z - c).im| := by rw [hz1, Complex.sub_im, hcim]; simp
        _ ≤ ‖z - c‖ := Complex.abs_im_le_norm _
    have hnorm : ‖z - c‖ ≤ R := by rwa [← dist_eq_norm]
    linarith
  have hrecond : ∀ z ∈ Metric.closedBall c (R / 4),
      riemannZeta z = 0 → z.re ≤ c.re := by
    intro z _ hz0
    by_contra hzre
    push_neg at hzre
    exact (riemannZeta_ne_zero_of_one_le_re (by
      rw [hcre] at hzre
      linarith)) hz0
  have hratio' : ∀ z ∈ Metric.closedBall c R,
      ‖riemannZeta z‖ ≤ Real.exp K * ‖riemannZeta c‖ := by
    simpa only [c] using hratio
  constructor
  · intro ρ hρ hζρ
    simpa only [c, zetaLandauConstant] using
      landau_inequality hUopen hf hR0 hball hfc hratio' hrecond hρ hζρ
  · simpa only [c, zetaLandauConstant] using
      landau_inequality_free hUopen hf hR0 hball hfc hratio' hrecond

end ExpSums

end MoltResearch
