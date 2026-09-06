import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentBounds

/-!
# Track R A2-V': high-moment certificate closure

The cover and damped exceptional-prime estimates now consume only additive
logarithmic certificates.  All analytic large-value inputs, cell masses and
finite sums are discharged here.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- A common logarithmic envelope for the last ordinary cells implies the
scale bound needed by the exceptional integer leg. -/
theorem sliceA2ExceptionalCover_scale_of_log
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (P0 ratio0 eta J A1 A : ℕ) (eps epsc rho0 K1 K2 T Z : ℝ)
    (hP0 : 2 ≤ P0) (hJ : 0 < J) (hT : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (hanchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
      6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
    (hlogAnchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
      256 ≤ Real.log
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ))
    (hlog : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
      sliceA2MomentLogEnvelope
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
        (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
        (Real.exp (-(innerBandScheduleAlpha (J - 1) * (r : ℝ) /
          ((2 * sliceA2OrdinaryN P0 ratio0 eta (J - 1)
            eps rho0 : ℕ) : ℝ)))) ≤ Z)
    (hscale :
      2 * ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1)).card : ℝ) *
          Real.exp Z * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A) :
    sliceA2ExceptionalCover g P0 ratio0 eta J A1
        eps epsc rho0 K1 K2 * Real.sqrt T *
          (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A := by
  let I := Finset.Ico
    (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
    (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1)
  have hraw := sliceA2ExceptionalCover_le_envelopes g hg P0 ratio0 eta J A1
    eps epsc rho0 K1 K2 T hP0 hJ hT hTK2 hanchor hlogAnchor
  have hpoint : ∀ r ∈ I,
      ordinaryCoverMomentEnvelope
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
        (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
        (Real.exp (-(innerBandScheduleAlpha (J - 1) * (r : ℝ) /
          ((2 * sliceA2OrdinaryN P0 ratio0 eta (J - 1)
            eps rho0 : ℕ) : ℝ)))) ≤ Real.exp Z := by
    intro r hr
    apply ordinaryCoverMomentEnvelope_le_exp_of_log
    · positivity
    · exact hlog r (by simpa [I] using hr)
  have hsum :
      (∑ r ∈ I, 2 * ordinaryCoverMomentEnvelope
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
        (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
        (Real.exp (-(innerBandScheduleAlpha (J - 1) * (r : ℝ) /
          ((2 * sliceA2OrdinaryN P0 ratio0 eta (J - 1)
            eps rho0 : ℕ) : ℝ))))) ≤ 2 * (I.card : ℝ) * Real.exp Z := by
    calc
      _ ≤ ∑ _r ∈ I, 2 * Real.exp Z := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hpoint r hr) (by norm_num)
      _ = 2 * (I.card : ℝ) * Real.exp Z := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hcover : sliceA2ExceptionalCover g P0 ratio0 eta J A1
      eps epsc rho0 K1 K2 ≤ 2 * (I.card : ℝ) * Real.exp Z :=
    hraw.trans (by simpa [I] using hsum)
  have hnonneg : 0 ≤ Real.sqrt T *
      (exceptionalPrimeUpper A1 epsc : ℝ) := by positivity
  calc
    sliceA2ExceptionalCover g P0 ratio0 eta J A1
          eps epsc rho0 K1 K2 * Real.sqrt T *
          (exceptionalPrimeUpper A1 epsc : ℝ) ≤
        (2 * (I.card : ℝ) * Real.exp Z) * Real.sqrt T *
          (exceptionalPrimeUpper A1 epsc : ℝ) := by gcongr
    _ ≤ A := by simpa [I] using hscale

/-- A logarithmic damping certificate proves the literal exceptional
`hGammaFit` inequality for one remote cell. -/
theorem sliceA2ExceptionalGamma_fit_of_log
    (A A1 v : ℕ) (epsc eps rho0 T : ℝ)
    (hA : 3 ≤ A) (hT : 1 ≤ T)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlogAnchor : 256 ≤ Real.log
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))
    (hlog :
      Real.pi +
          ((sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) + 2) *
            Real.log 2 +
          2 * (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) *
            Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) +
          2 * (Real.log 9 +
            Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) +
            Real.log (Real.log (2 *
              (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ)))) +
          200 * (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) *
            Real.log (Real.log (A : ℝ)) +
          2 * Real.log (Real.log (2 * T)) ≤
        Real.log (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) /
          (Real.log (2 * T)) ^ primeLargeValuesExponent) :
    primeHighMomentCountCost
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0)
          (sliceA2ExceptionalMoment A1 v epsc eps rho0 T)
          (eadicCell (exceptionalPrimes A1 epsc)
            (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
          T (exceptionalSplitThreshold A) 1 *
          (Real.log (2 * T)) ^ 2 ≤
        Real.exp (Real.log
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) /
            (Real.log (2 * T)) ^ primeLargeValuesExponent) := by
  let P := sliceA2ExceptionalAnchor A1 v epsc eps rho0
  let ell := sliceA2ExceptionalMoment A1 v epsc eps rho0 T
  let Y := eadicCell (exceptionalPrimes A1 epsc)
    (2 * sliceA2ExceptionalN A1 epsc eps rho0) v
  have hbounds : ∀ p ∈ Y, P < p ∧ p ≤ 2 * P := by
    intro p hp
    exact eadicCell_mem_lowerAnchor_dyadic
      (exceptionalPrimes A1 epsc)
      (fun q hq => exceptionalPrimes_prime A1 epsc q hq)
      (sliceA2ExceptionalN A1 epsc eps rho0) v
      (sliceA2ExceptionalN_two_le A1 epsc eps rho0)
      (by simpa [P, sliceA2ExceptionalAnchor, exceptionalCellAnchor] using hanchor)
      p hp
  have hmassRaw := sum_one_div_prime_dyadic_le P (by omega) Y
    (fun p hp => exceptionalPrimes_prime A1 epsc p (mem_eadicCell.mp hp).1)
    (fun p hp => (hbounds p hp).1) (fun p hp => (hbounds p hp).2)
  have hmass : ∑ p ∈ Y, (1 : ℝ) / p ≤ 1 := by
    exact hmassRaw.trans (by
      have hlogpos : 0 < Real.log (P : ℝ) := by
        dsimp [P]
        linarith
      rw [div_le_one hlogpos]
      simpa [P] using hlogAnchor)
  have htime : (T + 1) / ((P ^ ell : ℕ) : ℝ) ≤ 1 := by
    have hPtwo : 2 ≤ P := by
      dsimp [P]
      omega
    simpa [P, ell, sliceA2ExceptionalMoment] using
      exceptionalCellMoment_time_term_le_one
        (sliceA2ExceptionalN A1 epsc eps rho0) v T (by
          simpa [P, sliceA2ExceptionalAnchor] using hPtwo) hT
  apply primeHighMomentCountCost_damped_fit_of_log P ell Y T
    (exceptionalSplitThreshold A)
    (Real.log (P : ℝ) / (Real.log (2 * T)) ^ primeLargeValuesExponent)
  · omega
  · exact hT
  · exact exceptionalSplitThreshold_pos A (by omega)
  · exact htime
  · exact hmass
  · calc
      sliceA2MomentLogEnvelope P ell (exceptionalSplitThreshold A) +
            2 * Real.log (Real.log (2 * T)) ≤
          (Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
              2 * (ell : ℝ) * Real.log (ell : ℝ) +
              2 * (Real.log 9 + Real.log (ell : ℝ) +
                Real.log (Real.log (2 * (P : ℝ)))) +
              200 * (ell : ℝ) * Real.log (Real.log (A : ℝ))) +
            2 * Real.log (Real.log (2 * T)) :=
        by
          have henv := sliceA2MomentLogEnvelope_exceptional_le A P ell hA
            (by omega) (sliceA2ExceptionalMoment_one_le A1 v epsc eps rho0 T)
          linarith
      _ ≤ Real.log (P : ℝ) / (Real.log (2 * T)) ^ primeLargeValuesExponent := by
        simpa [P, ell] using hlog

end Tao2015

end MoltResearch
