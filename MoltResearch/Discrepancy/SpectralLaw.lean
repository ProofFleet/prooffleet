import MoltResearch.Discrepancy.FiniteSpectralSample
import MoltResearch.Discrepancy.PrimeDataSpace
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Discrepancy: the spectral laws on the space of prime data

Tao 2015 §2 (arXiv:1509.05363, `Problems/tao2015_derivation_c.md`, issue #2920): the
per-scale laws `ν_X` of the finite spectral samples, living on the compact space
`PrimeData`, with the second-moment bounds transported.

* `Circle` gets its Borel measurable structure (a `def`-wrapped subtype of `ℂ`, so the
  instance must be declared).
* `liftFreq X M ξ` — a finite frequency as full prime data (`e(ξ_p/M)` below the
  cutoff, `1` above); `toCM_liftFreq`: the encoded function **is** the finite spectral
  sample.
* `spectralPMF` — the `‖F̂‖²` law on the finite frequency space (mass exactly `1`).
* `spectralLaw` — the pushforward `ν_X : ProbabilityMeasure PrimeData`.
* `integral_windowFunctional_spectralLaw_le` — `∫ ‖∑_{j≤n} toCM ω j‖² dν_X ≤ B² + 1`
  for `n ≤ X` — the per-scale bound the limit (P8) will preserve.
-/

namespace MoltResearch

open Finset MeasureTheory

noncomputable instance : MeasurableSpace Circle := borel Circle

instance : BorelSpace Circle := ⟨rfl⟩

variable {X M : ℕ} [NeZero M]

/-- A finite frequency as full prime data: `e(ξ_p/M)` below the cutoff, `1` above. -/
noncomputable def liftFreq (X M : ℕ) [NeZero M] (ξ : PrimeIdx X → ZMod M) :
    PrimeData :=
  fun p => if h : (p : ℕ) ∈ (X + 1).primesBelow then ZMod.toCircle (ξ ⟨p.1, h⟩) else 1

/-- The lifted frequency encodes exactly the finite spectral sample. -/
theorem toCM_liftFreq (ξ : PrimeIdx X → ZMod M) :
    toCM (liftFreq X M ξ) = spectralSample X M ξ := by
  funext n
  unfold toCM spectralSample cmOfPrimes
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors
    (by rwa [Nat.support_factorization] at hp)
  congr 1
  simp only []
  rw [dif_pos hpp]
  unfold liftFreq spectralPrimeData
  by_cases hmem : p ∈ (X + 1).primesBelow
  · rw [dif_pos hmem, dif_pos hmem]
    rfl
  · rw [dif_neg hmem, dif_neg hmem]
    rfl

/-- The `‖F̂‖²` spectral law on the finite frequency space (mass exactly `1`). -/
noncomputable def spectralPMF (f : ℕ → ℤ) (X M : ℕ) [NeZero M]
    (hs : IsSignSequence f) : PMF (PrimeIdx X → ZMod M) :=
  PMF.ofFintype (fun ξ => ENNReal.ofReal (‖prodDFT (smoothEval f X) ξ‖ ^ 2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ξ _ => by positivity,
      sum_normSq_prodDFT_smoothEval hs, ENNReal.ofReal_one])

/-- The per-scale law `ν_X` on the space of prime data. -/
noncomputable def spectralLaw (f : ℕ → ℤ) (X M : ℕ) [NeZero M]
    (hs : IsSignSequence f) : ProbabilityMeasure PrimeData :=
  ⟨((spectralPMF f X M hs).toMeasure).map (liftFreq X M),
    inferInstance⟩

/-- **The per-scale second-moment bound, transported**: against `ν_X`, the window
functionals integrate to at most `B² + 1` up to scale `X`. -/
theorem integral_windowFunctional_spectralLaw_le {f : ℕ → ℤ} (hs : IsSignSequence f)
    {B : ℕ} (hB : ∀ d n : ℕ, d > 0 → (apSum f d n).natAbs ≤ B)
    {n : ℕ} (hnX : n ≤ X)
    (hM : Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 ≤ M) :
    ∫ ω, windowFunctional n ω ∂(spectralLaw f X M hs : Measure PrimeData)
      ≤ (B : ℝ) ^ 2 + 1 := by
  have hmap : (spectralLaw f X M hs : Measure PrimeData)
      = ((spectralPMF f X M hs).toMeasure).map (liftFreq X M) := rfl
  rw [hmap, integral_map Measurable.of_discrete.aemeasurable
    (windowFunctional n).continuous.aestronglyMeasurable]
  rw [MeasureTheory.integral_fintype (Integrable.of_finite)]
  have hterm : ∀ ξ : PrimeIdx X → ZMod M,
      ((spectralPMF f X M hs).toMeasure).real {ξ}
          • windowFunctional n (liftFreq X M ξ)
        = ‖prodDFT (smoothEval f X) ξ‖ ^ 2
          * ‖apSumC (spectralSample X M ξ) 1 n‖ ^ 2 := by
    intro ξ
    have hmass : ((spectralPMF f X M hs).toMeasure).real {ξ}
        = ‖prodDFT (smoothEval f X) ξ‖ ^ 2 := by
      unfold Measure.real
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton ξ)]
      unfold spectralPMF
      rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (by positivity)]
    rw [hmass, windowFunctional_apply, toCM_liftFreq, smul_eq_mul]
  rw [Finset.sum_congr rfl fun ξ _ => hterm ξ]
  exact weighted_normSq_apSumC_spectralSample_le hs hB hnX hM

end MoltResearch
