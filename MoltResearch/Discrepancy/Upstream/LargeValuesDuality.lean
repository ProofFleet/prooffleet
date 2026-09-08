import MoltResearch.Discrepancy.DyadicMVT
import MoltResearch.Discrepancy.HalaszMontgomeryLargeValues

/-!
# Upstreaming slot UP-6: Gallagher's separated-sum inequality and the Halász–Montgomery duality lemma

Pre-allocated leaf for card item UP-6 of `Problems/nucleus_upstreaming.md`. The claimant of UP-6 fills this file with
the Mathlib-style restatement, proved from the imported tree lemmas; no other file is to be edited.
-/

namespace MoltResearch

namespace Upstream

/-- **Gallagher's separated-sum inequality.** For a continuously
differentiable complex-valued function, its squared norm on a finite
`1`-separated subset of `[-T, T]` is controlled by one interval integral.

This is the separated-points form of P. X. Gallagher's classical large-sieve
inequality; see Gallagher, *A large sieve density estimate near σ = 1*
(Invent. Math. 11, 1970). -/
theorem gallagher_separated_sum (F dF : ℝ → ℂ)
    (hF : ∀ u, HasDerivAt F (dF u) u) (hFc : Continuous F)
    (hdFc : Continuous dF) (𝒯 : Finset ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hmem : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hsep : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s → 1 ≤ |t - s|) :
    ∑ t ∈ 𝒯, ‖F t‖ ^ 2 ≤
      ∫ u in (-T)..(T + 1), (‖F u‖ ^ 2 + 2 * ‖F u‖ * ‖dF u‖) := by
  exact ExpSums.sum_norm_sq_le_integral_of_separated F dF hF hFc hdFc 𝒯 T hT hmem hsep

/-- **Halász–Montgomery duality/Schur bound.** The synthesis energy of a
finite family of complex phases is at most the coefficient energy times the
largest absolute row sum of its Gram kernel.

This is the classical Halász–Montgomery inequality; see H. L. Montgomery,
*Topics in Multiplicative Number Theory* (Lecture Notes in Mathematics 227,
1971). -/
theorem halasz_montgomery_duality {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (hJ : J.Nonempty)
    (b : ι → ℂ) (χ : ι → κ → ℂ) :
    ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2 ≤
      (∑ i ∈ I, ‖b i‖ ^ 2) *
        J.sup' hJ (fun t =>
          ∑ s ∈ J, ‖∑ i ∈ I, χ i t * (starRingEnd ℂ) (χ i s)‖) := by
  classical
  let row : κ → ℝ := fun t =>
    ∑ s ∈ J, ‖∑ i ∈ I, χ i t * (starRingEnd ℂ) (χ i s)‖
  change ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2 ≤
    (∑ i ∈ I, ‖b i‖ ^ 2) * J.sup' hJ row
  refine sum_norm_sq_le_norm_sq_mul_sup_kernel I J b χ (J.sup' hJ row) ?_ ?_
  · obtain ⟨t, ht⟩ := hJ
    exact (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (Finset.le_sup' row ht)
  · intro t ht
    exact Finset.le_sup' row ht

example (F dF : ℝ → ℂ)
    (hF : ∀ u, HasDerivAt F (dF u) u) (hFc : Continuous F)
    (hdFc : Continuous dF) (𝒯 : Finset ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hmem : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hsep : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s → 1 ≤ |t - s|) :
    ∑ t ∈ 𝒯, ‖F t‖ ^ 2 ≤
      ∫ u in (-T)..(T + 1), (‖F u‖ ^ 2 + 2 * ‖F u‖ * ‖dF u‖) :=
  gallagher_separated_sum F dF hF hFc hdFc 𝒯 T hT hmem hsep

example {ι κ : Type*} (I : Finset ι) (J : Finset κ) (hJ : J.Nonempty)
    (b : ι → ℂ) (χ : ι → κ → ℂ) :
    ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2 ≤
      (∑ i ∈ I, ‖b i‖ ^ 2) *
        J.sup' hJ (fun t =>
          ∑ s ∈ J, ‖∑ i ∈ I, χ i t * (starRingEnd ℂ) (χ i s)‖) :=
  halasz_montgomery_duality I J hJ b χ

end Upstream

end MoltResearch
