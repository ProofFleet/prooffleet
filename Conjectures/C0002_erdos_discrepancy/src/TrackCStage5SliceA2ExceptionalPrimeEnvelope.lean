import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalPrime

/-!
# Track R A2-V': fixed exceptional sharp envelope

The exceptional sharp bound and positive-ladder Brun remainder are uniform
over the remote cells.  This leaf installs their constant envelope as
`DeltaU`, checks its fixed squared condition using the explicit
epsilon-prime choice, and leaves only the two decaying tail estimates and
the high-moment damping inequality.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- A sharp-cell estimate and a ladder-remainder estimate add to the chosen
constant exceptional envelope. -/
theorem sliceA2Exceptional_delta_bound_of_sharp_remainder
    (Cp : ℝ) (A1 : ℕ) (epsc eps rho0 tail rem sharp remainder : ℝ)
    (hsharp : sharp ≤
      2 * (2 * sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 *
        Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) + tail))
    (hremainder : remainder ≤ rem) :
    sharp + remainder ≤
      sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem := by
  exact exceptionalDeltaEnvelope_bounds_sharp_add_remainder
    sharp remainder
    (sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0)
    (exceptionalIntervalRatio epsc : ℝ) tail rem hsharp hremainder

/-- The concrete prime aggregate from uniform sharp, Brun and damping
envelopes. -/
theorem sliceA2Exceptional_prime_fit_of_envelopes
    (Cp : ℝ) (hCp1 : 1 ≤ Cp)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (A A1 : ℕ) (epsc eps rho0 T tail rem : ℝ)
    (hA : 2 ≤ A) (hT : 0 ≤ T) (heps : 0 ≤ eps) (hrho0 : 0 ≤ rho0)
    (htail0 : 0 ≤ tail) (hrem0 : 0 ≤ rem)
    (hanchor : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
      6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog1 : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hlog6 : 2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hGammaFit : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
      primeHighMomentCountCost
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0)
          (sliceA2ExceptionalMoment A1 v epsc eps rho0 T)
          (eadicCell (exceptionalPrimes A1 epsc)
            (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
          T (exceptionalSplitThreshold A) 1 *
          (Real.log (2 * T)) ^ 2 ≤
        Real.exp (Real.log
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) /
            (Real.log (2 * T)) ^ primeLargeValuesExponent))
    (htail : 2 * tail + rem ≤
      4 * sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 *
        Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ)) :
    let d := sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem
    2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
        (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
          exceptionalPrimeCellCost Cp
            (fun u => eadicCell (exceptionalPrimes A1 epsc)
              (2 * sliceA2ExceptionalN A1 epsc eps rho0) u)
            (sliceA2ExceptionalAnchor A1 · epsc eps rho0) g (fun _ => d)
            (sliceA2ExceptionalGamma A A1 · epsc eps rho0 T) v) ≤
      eps ^ 2 * rho0 / 64 := by
  dsimp only
  let d := sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem
  have hepsPrime0 : 0 ≤
      sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 := by
    unfold sliceA2ExceptionalEpsilonPrime exceptionalEpsilonPrime
    positivity
  have hR0 : (0 : ℝ) ≤ exceptionalIntervalRatio epsc := by positivity
  have hd0 : 0 ≤ d := by
    dsimp [d, sliceA2ExceptionalDeltaEnvelope]
    exact exceptionalDeltaEnvelope_nonneg _ _ _ _
      hepsPrime0 hR0 htail0 hrem0
  have hfixed0 := sliceA2Exceptional_delta_fixed_condition
    Cp hCp1 A1 epsc eps rho0 tail rem heps hrho0 htail0 hrem0 htail
  have hfixed :
      3072 * Cp * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
        (exceptionalIntervalRatio epsc : ℝ) * d ^ 2 *
          sliceA2ExceptionalMass A1 epsc ≤ eps ^ 2 * rho0 := by
    dsimp [d]
    convert hfixed0 using 1 <;> ring
  apply sliceA2Exceptional_prime_fit Cp hCp1 g hg A A1 epsc eps rho0 T
    (fun _ => d) d hA hT hanchor hlog1 hlog6
  · intro v hv
    exact hd0
  · intro v hv
    exact le_rfl
  · intro v hv
    exact sliceA2ExceptionalGamma_le_one A A1 v epsc eps rho0 T
      (hGammaFit v hv)
  · exact hfixed

end Tao2015

end MoltResearch
