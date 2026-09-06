import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalData

/-!
# Track R A2-V': the concrete exceptional integer leg

This leaf installs the literal quotient endpoint, coefficient mass, raw
cover cardinality and logarithmic factor used by the shifted capstone.  The
coefficient tail is discharged here; only the displayed scale envelope for
the split threshold and cover remains.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

noncomputable def sliceA2ExceptionalI
    (A1 : ℕ) (epsc eps rho0 : ℝ) : Finset ℕ :=
  Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
    (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1)

noncomputable def sliceA2ExceptionalBq
    (A Delta A1 v : ℕ) (epsc eps rho0 : ℝ) : ℝ :=
  (((A + Delta) /
    sliceA2ExceptionalRepresentative A1 v epsc eps rho0 : ℕ) : ℝ)

noncomputable def sliceA2ExceptionalCoeffMass
    (g : ℕ → ℂ) (A Delta P0 ratio0 eta J A1 v : ℕ)
    (epsc eps rho0 : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1
      ((A + Delta) /
        sliceA2ExceptionalRepresentative A1 v epsc eps rho0),
    ‖cellBlockCoeff g A (A + Delta) (exceptionalPrimes A1 epsc)
      ((List.range J).map (sliceA2LadderPrimes P0 ratio0 eta))
      (sliceA2ExceptionalRepresentative A1 v epsc eps rho0) n‖ ^ 2 /
        (n : ℝ) ^ 2

noncomputable def sliceA2ExceptionalCover
    (g : ℕ → ℂ) (P0 ratio0 eta J A1 : ℕ)
    (eps epsc rho0 K1 K2 : ℝ) : ℝ :=
  ((cellsMeetingSet (bandCells K2)
    (bandPartOn
      (levelSmallSet (sliceA2LadderPrimes P0 ratio0 eta)
        (fun j => sliceA2OrdinaryN P0 ratio0 eta j eps rho0)
        (fun j => sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (fun j => sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0)
        g innerBandScheduleAlpha) J
      {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J)).card : ℝ)

noncomputable def sliceA2ExceptionalLogFactor (T : ℝ) : ℝ :=
  Real.log (2 * T) + 1

theorem sliceA2ExceptionalI_card_fixed
    (A1 : ℕ) (epsc eps rho0 : ℝ)
    (hlog : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ)) :
    ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) ≤
      3 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
        (exceptionalIntervalRatio epsc : ℝ) *
          Real.log (exceptionalPrimeLower A1 : ℝ) := by
  simpa [sliceA2ExceptionalI, sliceA2ExceptionalV0,
    sliceA2ExceptionalV1] using
      exceptionalLevel_cell_card_fixed A1
        (sliceA2ExceptionalN A1 epsc eps rho0) epsc
        (sliceA2ExceptionalN_pos A1 epsc eps rho0) hlog

theorem sliceA2ExceptionalRepresentative_le_upper
    (A1 v : ℕ) (epsc eps rho0 : ℝ) :
    sliceA2ExceptionalRepresentative A1 v epsc eps rho0 ≤
      exceptionalPrimeUpper A1 epsc := by
  exact exceptionalRepresentative_le_upper A1
    (sliceA2ExceptionalN A1 epsc eps rho0) v epsc
    (sliceA2ExceptionalN_pos A1 epsc eps rho0)

theorem sliceA2ExceptionalRepresentative_two_mul_le
    (A1 A v : ℕ) (epsc eps rho0 : ℝ)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A) :
    2 * sliceA2ExceptionalRepresentative A1 v epsc eps rho0 ≤ A := by
  exact exceptionalRepresentative_two_mul_le A1 A
    (sliceA2ExceptionalN A1 epsc eps rho0) v epsc
    (sliceA2ExceptionalN_pos A1 epsc eps rho0) hQsq

theorem sliceA2ExceptionalRepresentative_quotient_one_le
    (A1 A v : ℕ) (epsc eps rho0 : ℝ)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A) :
    1 ≤ A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0 := by
  exact exceptionalRepresentative_quotient_one_le A1 A
    (sliceA2ExceptionalN A1 epsc eps rho0) v epsc
    (sliceA2ExceptionalN_pos A1 epsc eps rho0) hQsq

/-- The literal exceptional integer cost follows from one scale inequality.
The coefficient-mass bound and every natural-division rounding term have
already been discharged in the conclusion. -/
theorem sliceA2Exceptional_integer_fit
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta P0 ratio0 eta J A1 : ℕ) (epsc eps rho0 K1 K2 T : ℝ)
    (hA : 0 < A) (hDelta : Delta ≤ A)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A)
    (hT : 1 ≤ T)
    (hfit :
      1024 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) ^ 2 *
          exceptionalSplitThreshold A ^ 2 *
          sliceA2ExceptionalLogFactor T *
          (1 + sliceA2ExceptionalCover g P0 ratio0 eta J A1
              eps epsc rho0 K1 K2 * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) / (A : ℝ)) ≤
        eps ^ 2 * rho0 / 64) :
    2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
        (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
          exceptionalIntegerCellCost (exceptionalSplitThreshold A)
            (sliceA2ExceptionalBq A Delta A1 v epsc eps rho0)
            (sliceA2ExceptionalCover g P0 ratio0 eta J A1
              eps epsc rho0 K1 K2) T
            (sliceA2ExceptionalLogFactor T)
            (sliceA2ExceptionalCoeffMass g A Delta P0 ratio0 eta J A1 v
              epsc eps rho0)) ≤
      eps ^ 2 * rho0 / 64 := by
  let I := sliceA2ExceptionalI A1 epsc eps rho0
  let q := fun v => sliceA2ExceptionalRepresentative A1 v epsc eps rho0
  let Bq := fun v => sliceA2ExceptionalBq A Delta A1 v epsc eps rho0
  let coeffMass := fun v =>
    sliceA2ExceptionalCoeffMass g A Delta P0 ratio0 eta J A1 v epsc eps rho0
  let Kcov := sliceA2ExceptionalCover g P0 ratio0 eta J A1
    eps epsc rho0 K1 K2
  let L := sliceA2ExceptionalLogFactor T
  have hq1 : ∀ v ∈ I, 1 ≤ q v := by
    intro v hv
    exact (sliceA2Exceptional_cell_data A1 epsc eps rho0).2.2.1 v
  have hqQ : ∀ v ∈ I, q v ≤ exceptionalPrimeUpper A1 epsc := by
    intro v hv
    exact sliceA2ExceptionalRepresentative_le_upper A1 v epsc eps rho0
  have h2qA : ∀ v ∈ I, 2 * q v ≤ A := by
    intro v hv
    exact sliceA2ExceptionalRepresentative_two_mul_le A1 A v epsc eps rho0 hQsq
  have hBq : ∀ v ∈ I,
      Bq v ≤ 2 * (((A / q v + 1 : ℕ) : ℝ)) := by
    intro v hv
    have hq0 : 0 < q v := by have := hq1 v hv; omega
    have hnat : (A + Delta) / q v ≤ 2 * (A / q v) + 1 :=
      div_le_two_mul_div_add_one A (A + Delta) (q v) hq0 (by omega)
    have hnat' : (A + Delta) / q v ≤ 2 * (A / q v + 1) := by omega
    change (((A + Delta) / q v : ℕ) : ℝ) ≤
      2 * (((A / q v + 1 : ℕ) : ℝ))
    exact_mod_cast hnat'
  have hcoeff0 : ∀ v ∈ I, 0 ≤ coeffMass v := by
    intro v hv
    exact Finset.sum_nonneg fun n hn => by positivity
  have hcoeff : ∀ v ∈ I,
      coeffMass v ≤ 2 / (((A / q v + 1 : ℕ) : ℝ)) := by
    intro v hv
    exact sum_norm_cellBlockCoeff_sq_div_sq_le_two_div g hg A (A + Delta)
      (exceptionalPrimes A1 epsc)
      ((List.range J).map (sliceA2LadderPrimes P0 ratio0 eta)) (q v)
      (sliceA2ExceptionalRepresentative_quotient_one_le
        A1 A v epsc eps rho0 hQsq)
  have hK : 0 ≤ Kcov := by
    dsimp [Kcov, sliceA2ExceptionalCover]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L, sliceA2ExceptionalLogFactor]
    have h2T : 1 ≤ 2 * T := by linarith
    linarith [Real.log_nonneg h2T]
  have hresult := exceptional_integer_aggregate_fit_ratio I A
    (exceptionalPrimeUpper A1 epsc) q Bq coeffMass
    (exceptionalSplitThreshold A) Kcov T L 1 eps rho0 hA hK hL
    hq1 hqQ h2qA hBq hcoeff0 hcoeff (by simpa [I, Kcov, L] using hfit)
  simpa [I, q, Bq, coeffMass, Kcov, L] using hresult

end Tao2015

end MoltResearch
