import MoltResearch.Discrepancy.SpectralLaw
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Discrepancy: the limiting spectral law

Tao 2015 §2 (arXiv:1509.05363, `Problems/tao2015_derivation_c.md`, issue #2920): the
compactness step.  The per-scale laws `ν_X` live on the compact space `PrimeData`, so
the space of probability measures is compact (Prokhorov); an ultrafilter refining
`atTop` therefore has a limit law `ν`, and since each window bound
`∫ ‖∑_{j≤n}·‖² dν_X ≤ B² + 1` holds for **all** `X ≥ n`, it passes to the limit for
**every** `n` — no subsequences or metrizability needed.

* `modSchedule X` — an exponent modulus large enough for eq. (fpi) at scale `X`.
* `scaleLaws f hs X` — the law `ν_X` at the scheduled modulus.
* `exists_limit_law` — the limit `ν` with all window bounds: the law of the paper's
  random completely multiplicative function `𝐠`.
-/

namespace MoltResearch

open MeasureTheory Filter

/-- The exponent-modulus schedule: large enough for eq. (fpi) at scale `X`. -/
def modSchedule (X : ℕ) : ℕ :=
  max 1 (Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2)

instance (X : ℕ) : NeZero (modSchedule X) := ⟨by unfold modSchedule; omega⟩

/-- The per-scale spectral laws along the schedule. -/
noncomputable def scaleLaws (f : ℕ → ℤ) (hs : IsSignSequence f) (X : ℕ) :
    ProbabilityMeasure PrimeData :=
  spectralLaw f X (modSchedule X) hs

/-- **The limiting law** (Tao 2015 §2, the compactness step): an ultrafilter limit of
the per-scale laws carries every window bound simultaneously. -/
theorem exists_limit_law (f : ℕ → ℤ) (hs : IsSignSequence f)
    {B : ℕ} (hB : ∀ d n : ℕ, d > 0 → (apSum f d n).natAbs ≤ B) :
    ∃ ν : ProbabilityMeasure PrimeData, ∀ n : ℕ,
      ∫ ω, windowFunctional n ω ∂(ν : Measure PrimeData) ≤ (B : ℝ) ^ 2 + 1 := by
  set 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.atTop with h𝒰
  obtain ⟨ν, -, hν⟩ :=
    (isCompact_univ (X := ProbabilityMeasure PrimeData)).ultrafilter_le_nhds
      (𝒰.map (scaleLaws f hs)) (by simp)
  refine ⟨ν, fun n => ?_⟩
  have htend : Filter.Tendsto (scaleLaws f hs) ↑𝒰 (nhds ν) := by
    rw [Filter.Tendsto, ← Ultrafilter.coe_map]
    exact hν
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htend
    (windowFunctional n)
  have hev : ∀ᶠ X in Filter.atTop,
      ∫ ω, windowFunctional n ω ∂(scaleLaws f hs X : Measure PrimeData)
        ≤ (B : ℝ) ^ 2 + 1 := by
    filter_upwards [Filter.eventually_ge_atTop n] with X hX
    exact integral_windowFunctional_spectralLaw_le hs hB hX (le_max_right _ _)
  exact le_of_tendsto hint (hev.filter_mono (Ultrafilter.of_le _))

end MoltResearch
