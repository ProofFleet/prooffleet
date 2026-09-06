import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalPrimeEnvelope

/-!
# Track R A2-V': complete exceptional aggregate

This is the final bookkeeping layer for the exceptional half-band.  It
combines the integer-cell, prime-cell, and wide-error estimates with the
fixed short-slice budget.  All three conclusions are in the literal form
consumed by `sliceA2_inner_band_of_aggregate_fits`.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

theorem sliceA2Exceptional_aggregate_fits
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta P0 ratio0 eta J A1 : ℕ)
    (epsc eps rho0 K1 K2 T tail rem : ℝ)
    (hA : 2 ≤ A) (hDelta : Delta ≤ A)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A)
    (hT : 1 ≤ T) (hTA : T ≤ A)
    (heps : 0 < eps) (hrho0 : 0 < rho0)
    (htail0 : 0 ≤ tail) (hrem0 : 0 ≤ rem)
    (hanchor : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
      6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog1 : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hlog6 : 2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hinteger :
      1024 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) ^ 2 *
          exceptionalSplitThreshold A ^ 2 *
          sliceA2ExceptionalLogFactor T *
          (1 + sliceA2ExceptionalCover g P0 ratio0 eta J A1
              eps epsc rho0 K1 K2 * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ)) ≤
        eps ^ 2 * rho0 / 64)
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
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
    (htail : 2 * tail + rem ≤
      4 * sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 *
        Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ))
    (hreplacementCard : 1152 * Real.exp Real.pi *
        (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
      eps ^ 2 * rho0 / 192)
    (hcollisionPrime : 320 * Real.exp Real.pi /
        (exceptionalPrimeLower A1 : ℝ) ≤ eps ^ 2 * rho0 / 192)
    (hcollisionCard : 80 * Real.exp Real.pi *
        (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
      eps ^ 2 * rho0 / 192) :
    let d := sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem
    (2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
        (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
          exceptionalIntegerCellCost (exceptionalSplitThreshold A)
            (sliceA2ExceptionalBq A Delta A1 v epsc eps rho0)
            (sliceA2ExceptionalCover g P0 ratio0 eta J A1
              eps epsc rho0 K1 K2) T
            (sliceA2ExceptionalLogFactor T)
            (sliceA2ExceptionalCoeffMass g A Delta P0 ratio0 eta J A1 v
              epsc eps rho0)) ≤ eps ^ 2 * rho0 / 64) ∧
    (2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
        (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
          exceptionalPrimeCellCost
            (fun u => eadicCell (exceptionalPrimes A1 epsc)
              (2 * sliceA2ExceptionalN A1 epsc eps rho0) u)
            (sliceA2ExceptionalAnchor A1 · epsc eps rho0) g (fun _ => d)
            (sliceA2ExceptionalGamma A A1 · epsc eps rho0 T) v) ≤
      eps ^ 2 * rho0 / 64) ∧
    (2 * (2 * replacementEnergyBoundWide A (exceptionalPrimes A1 epsc)
          (sliceA2ExceptionalN A1 epsc eps rho0) T +
        2 * (4 * collisionEnergyBoundWide A
          (exceptionalPrimes A1 epsc) T)) ≤ eps ^ 2 * rho0 / 32) := by
  dsimp only
  constructor
  · exact sliceA2Exceptional_integer_fit g hg A Delta P0 ratio0 eta J A1
      epsc eps rho0 K1 K2 T (by omega) hDelta hQsq hT hinteger
  constructor
  · exact sliceA2Exceptional_prime_fit_of_envelopes g hg A A1 epsc eps rho0
      T tail rem hA (by linarith) heps.le hrho0.le htail0 hrem0 hanchor
      hlog1 hlog6 hGammaFit htail
  · exact sliceA2Exceptional_wide_fit A1 A epsc eps rho0 T hA hTA heps
      hrho0 hreplacementCard hcollisionPrime hcollisionCard

end Tao2015

end MoltResearch
