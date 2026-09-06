import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalInteger

/-!
# Track R A2-V': the concrete exceptional prime leg

The lower Brun anchor can fall just below the remote interval endpoint
because of integer rounding.  We retain half of the endpoint logarithm;
the fixed factor six pays this rounding and also converts the exceptional
cell-count bound.  The resulting prime aggregate has a fixed coefficient,
with no dependence on the ordinary ladder height.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Logarithmic scale retained after lower-anchor rounding. -/
noncomputable def sliceA2ExceptionalPrimeLog (A1 : ℕ) : ℝ :=
  Real.log (exceptionalPrimeLower A1 : ℝ) / 2

/-- Exact damped high-moment correction used by the capstone. -/
noncomputable def sliceA2ExceptionalGamma
    (A A1 v : ℕ) (epsc eps rho0 T : ℝ) : ℝ :=
  exceptionalPrimeGamma
    (primeHighMomentCountCost
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0)
      (sliceA2ExceptionalMoment A1 v epsc eps rho0 T)
      (eadicCell (exceptionalPrimes A1 epsc)
        (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
      T (exceptionalSplitThreshold A) 1)
    (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) T

/-- Coefficient of the fixed squared sharp envelope. -/
noncomputable def sliceA2ExceptionalPrimeCoefficient
    (A1 : ℕ) (epsc eps rho0 : ℝ) : ℝ :=
  max 1
    (196608 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
      (exceptionalIntervalRatio epsc : ℝ) *
        sliceA2ExceptionalMass A1 epsc)

theorem sliceA2ExceptionalPrimeCoefficient_pos
    (A1 : ℕ) (epsc eps rho0 : ℝ) :
    0 < sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0 := by
  unfold sliceA2ExceptionalPrimeCoefficient
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Fixed sharpness choice at the short-slice budget floor. -/
noncomputable def sliceA2ExceptionalEpsilonPrime
    (A1 : ℕ) (epsc eps rho0 : ℝ) : ℝ :=
  exceptionalEpsilonPrime (eps * Real.sqrt rho0) 1
    (exceptionalIntervalRatio epsc : ℝ)
    (sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0)

noncomputable def sliceA2ExceptionalDeltaEnvelope
    (A1 : ℕ) (epsc eps rho0 tail rem : ℝ) : ℝ :=
  exceptionalDeltaEnvelope
    (sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0)
    (exceptionalIntervalRatio epsc : ℝ) tail rem

theorem sliceA2ExceptionalEpsilonPrime_pos
    (A1 : ℕ) (epsc eps rho0 : ℝ)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 := by
  unfold sliceA2ExceptionalEpsilonPrime exceptionalEpsilonPrime
  have hR : (0 : ℝ) < exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hM := sliceA2ExceptionalPrimeCoefficient_pos A1 epsc eps rho0
  positivity

/-- The chosen epsilon-prime turns a small tail and Brun remainder into the
fixed aggregate inequality required by the prime cells. -/
theorem sliceA2Exceptional_delta_fixed_condition
    (A1 : ℕ) (epsc eps rho0 tail rem : ℝ)
    (heps : 0 ≤ eps) (hrho0 : 0 ≤ rho0)
    (htail0 : 0 ≤ tail) (hrem0 : 0 ≤ rem)
    (htail : 2 * tail + rem ≤
      4 * sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 *
        Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ)) :
    196608 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
        (exceptionalIntervalRatio epsc : ℝ) *
        sliceA2ExceptionalMass A1 epsc *
        sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem ^ 2 ≤
      eps ^ 2 * rho0 := by
  let R : ℝ := exceptionalIntervalRatio epsc
  let M := sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0
  let e := eps * Real.sqrt rho0
  let d := sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hM : 0 < M := by
    simpa [M] using sliceA2ExceptionalPrimeCoefficient_pos A1 epsc eps rho0
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hcore := exceptional_delta_fixed_condition e 1 R M tail rem
    he (by norm_num) hR hM htail0 hrem0 (by
      simpa [e, R, M, sliceA2ExceptionalEpsilonPrime] using htail)
  have hcoefficient :
      196608 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
          (exceptionalIntervalRatio epsc : ℝ) *
            sliceA2ExceptionalMass A1 epsc ≤ M := by
    dsimp [M, sliceA2ExceptionalPrimeCoefficient]
    exact le_max_right _ _
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  calc
    196608 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
          (exceptionalIntervalRatio epsc : ℝ) *
          sliceA2ExceptionalMass A1 epsc *
          sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem ^ 2 ≤
        M * d ^ 2 := by
      dsimp [d]
      exact mul_le_mul_of_nonneg_right hcoefficient hd2
    _ ≤ e ^ 2 := by
      simpa [d, e, R, M, sliceA2ExceptionalDeltaEnvelope,
        sliceA2ExceptionalEpsilonPrime] using hcore
    _ = eps ^ 2 * rho0 := by
      dsimp [e]
      rw [mul_pow, Real.sq_sqrt hrho0]

/-! ## Rounding-safe lower logarithm -/

/-- Every scheduled exceptional lower anchor is within a factor six of the
remote lower endpoint. -/
theorem exceptionalPrimeLower_le_six_mul_sliceA2ExceptionalAnchor
    (A1 v : ℕ) (epsc eps rho0 : ℝ)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 1 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) :
    (exceptionalPrimeLower A1 : ℝ) ≤
      6 * (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := by
  let N := sliceA2ExceptionalN A1 epsc eps rho0
  let P := exceptionalPrimeLower A1
  let Pc := sliceA2ExceptionalAnchor A1 v epsc eps rho0
  have hN : 0 < N := by simpa [N] using
    sliceA2ExceptionalN_pos A1 epsc eps rho0
  have hP : 3 ≤ P := by simpa [P] using exceptionalPrimeLower_three_le A1
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hPreal : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hv' : v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
      (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1) := by
    simpa only [sliceA2ExceptionalI] using hv
  have hv0 : sliceA2ExceptionalV0 A1 epsc eps rho0 ≤ v :=
    (Finset.mem_Ico.mp hv').1
  have hceil1 : 1 ≤ ⌈(2 * N : ℕ) * Real.log P⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos (by positivity) hlogP)
  have hceilv : ⌈(2 * N : ℕ) * Real.log P⌉₊ ≤ v + 1 := by
    unfold sliceA2ExceptionalV0 exceptionalV0 eadicCoverIndexLower at hv0
    simpa [N, P] using (show
      ⌈((2 * sliceA2ExceptionalN A1 epsc eps rho0 : ℕ) : ℝ) *
        Real.log (exceptionalPrimeLower A1 : ℝ)⌉₊ ≤ v + 1 by omega)
  have hlower : ((2 * N : ℕ) : ℝ) * Real.log P ≤ (v : ℝ) + 1 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilv)
  have hquot : Real.log P ≤ (v + 1 : ℝ) / (2 * N : ℕ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * N : ℕ))]
    simpa [mul_comm] using hlower
  have hPexp : (P : ℝ) ≤
      Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
    calc
      (P : ℝ) = Real.exp (Real.log P) := (Real.exp_log hPreal).symm
      _ ≤ Real.exp ((v + 1 : ℝ) / (2 * N : ℕ)) :=
        Real.exp_le_exp.mpr hquot
      _ = Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
        push_cast
        ring_nf
  have hfrac : (1 : ℝ) / (2 * (N : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith
  have hexpfrac : Real.exp (1 / (2 * (N : ℝ))) ≤ 3 := by
    calc
      Real.exp (1 / (2 * (N : ℝ))) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr hfrac
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hsplit :
      Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) =
        Real.exp ((v : ℝ) / (2 * (N : ℝ))) *
          Real.exp (1 / (2 * (N : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hPcExp : Real.exp ((v : ℝ) / (2 * (N : ℝ))) ≤ 2 * Pc := by
    simpa [N, Pc, sliceA2ExceptionalAnchor, exceptionalCellAnchor] using
      exp_cell_lower_le_two_anchor N v (by simpa [Pc] using hanchor)
  calc
    (P : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := hPexp
    _ = Real.exp ((v : ℝ) / (2 * (N : ℝ))) *
        Real.exp (1 / (2 * (N : ℝ))) := hsplit
    _ ≤ Real.exp ((v : ℝ) / (2 * (N : ℝ))) * 3 := by gcongr
    _ ≤ (2 * Pc) * 3 := by gcongr
    _ = 6 * (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := by
      dsimp [Pc]
      ring

/-- Half the remote endpoint logarithm is below every cell-anchor
logarithm. -/
theorem sliceA2ExceptionalPrimeLog_le_anchor_log
    (A1 v : ℕ) (epsc eps rho0 : ℝ)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog : 2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ)) :
    sliceA2ExceptionalPrimeLog A1 ≤
      Real.log (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := by
  let P := exceptionalPrimeLower A1
  let Pc := sliceA2ExceptionalAnchor A1 v epsc eps rho0
  have hPpos : (0 : ℝ) < P := by
    exact_mod_cast (show 0 < P by
      dsimp [P]
      have := exceptionalPrimeLower_three_le A1
      omega)
  have hPcpos : (0 : ℝ) < Pc := by exact_mod_cast (show 0 < Pc by omega)
  have hbound := exceptionalPrimeLower_le_six_mul_sliceA2ExceptionalAnchor
    A1 v epsc eps rho0 hv (by omega)
  have hlogs : Real.log (P : ℝ) ≤ Real.log (6 * Pc) :=
    Real.log_le_log hPpos hbound
  rw [Real.log_mul (by norm_num) (ne_of_gt hPcpos)] at hlogs
  unfold sliceA2ExceptionalPrimeLog
  dsimp [P, Pc] at hlogs
  linarith

/-- The fixed cell-count form using the same half-logarithm as the prime
aggregate. -/
theorem sliceA2ExceptionalI_card_primeLog
    (A1 : ℕ) (epsc eps rho0 : ℝ)
    (hlog : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ)) :
    ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) ≤
      6 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
        (exceptionalIntervalRatio epsc : ℝ) *
          sliceA2ExceptionalPrimeLog A1 := by
  have hcard := sliceA2ExceptionalI_card_fixed A1 epsc eps rho0 hlog
  unfold sliceA2ExceptionalPrimeLog
  nlinarith

theorem sliceA2ExceptionalGamma_nonneg
    (A A1 v : ℕ) (epsc eps rho0 T : ℝ) :
    2 ≤ A → 0 ≤ T →
      0 ≤ sliceA2ExceptionalGamma A A1 v epsc eps rho0 T := by
  intro hA hT
  apply exceptionalPrimeGamma_nonneg
  apply primeHighMomentCountCost_nonneg_of
  · exact hT
  · exact ne_of_gt (exceptionalSplitThreshold_pos A (by omega))
  · norm_num

theorem sliceA2ExceptionalGamma_le_one
    (A A1 v : ℕ) (epsc eps rho0 T : ℝ)
    (hfit :
      primeHighMomentCountCost
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0)
          (sliceA2ExceptionalMoment A1 v epsc eps rho0 T)
          (eadicCell (exceptionalPrimes A1 epsc)
            (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
          T (exceptionalSplitThreshold A) 1 *
          (Real.log (2 * T)) ^ 2 ≤
        Real.exp (Real.log
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ))) :
    sliceA2ExceptionalGamma A A1 v epsc eps rho0 T ≤ 1 := by
  exact exceptionalPrimeGamma_le_one _ _ _ hfit

/-- All structural prime-cell inputs reduce the literal aggregate to its
single fixed squared-envelope condition. -/
theorem sliceA2Exceptional_prime_fit
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (A A1 : ℕ) (epsc eps rho0 T : ℝ) (DeltaU : ℕ → ℝ) (d : ℝ)
    (hA : 2 ≤ A) (hT : 0 ≤ T)
    (hanchor : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
      6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog1 : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hlog6 : 2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ))
    (hDelta0 : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0, 0 ≤ DeltaU v)
    (hDelta : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0, DeltaU v ≤ d)
    (hGamma : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
      sliceA2ExceptionalGamma A A1 v epsc eps rho0 T ≤ 1)
    (hfixed :
      196608 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) *
        (exceptionalIntervalRatio epsc : ℝ) *
        d ^ 2 * sliceA2ExceptionalMass A1 epsc ≤ eps ^ 2 * rho0) :
    2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
        (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
          exceptionalPrimeCellCost
            (fun u => eadicCell (exceptionalPrimes A1 epsc)
              (2 * sliceA2ExceptionalN A1 epsc eps rho0) u)
            (sliceA2ExceptionalAnchor A1 · epsc eps rho0) g DeltaU
            (sliceA2ExceptionalGamma A A1 · epsc eps rho0 T) v) ≤
      eps ^ 2 * rho0 / 64 := by
  let I := sliceA2ExceptionalI A1 epsc eps rho0
  have hadata := sliceA2Exceptional_anchor_data A1 epsc eps rho0 hanchor
  have hcov := (sliceA2Exceptional_cell_data A1 epsc eps rho0).1
  have hmassEq := sum_eadicCell_harmonic_eq I (exceptionalPrimes A1 epsc)
    (sliceA2ExceptionalN A1 epsc eps rho0) (by simpa [I] using hcov)
  have hmass :
      ∑ v ∈ I, ∑ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
          (1 : ℝ) / p ≤ sliceA2ExceptionalMass A1 epsc := by
    rw [hmassEq]
    exact exceptionalPrimes_mass_le_sliceA2ExceptionalMass A1 epsc
  have hresult := exceptional_prime_aggregate_fit_ratio I
    (fun v => eadicCell (exceptionalPrimes A1 epsc)
      (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
    (sliceA2ExceptionalAnchor A1 · epsc eps rho0)
    (fun v hv => hadata.1 v (by
      simpa [I, sliceA2ExceptionalI] using hv))
    (fun v hv p hp => hadata.2.1 v (by
      simpa [I, sliceA2ExceptionalI] using hv) p hp) g hg DeltaU
    (sliceA2ExceptionalGamma A A1 · epsc eps rho0 T) d
    (sliceA2ExceptionalPrimeLog A1) (sliceA2ExceptionalMass A1 epsc)
    (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ)
    (exceptionalIntervalRatio epsc : ℝ) 6 1 eps rho0
    (by unfold sliceA2ExceptionalPrimeLog; linarith)
    (sliceA2ExceptionalMass_nonneg A1 epsc)
    (by simpa [I] using hDelta0) (by simpa [I] using hDelta)
    (by intro v hv; exact sliceA2ExceptionalGamma_nonneg A A1 v epsc eps rho0 T hA hT)
    (by simpa [I] using hGamma)
    (by
      intro v hv
      exact sliceA2ExceptionalPrimeLog_le_anchor_log A1 v epsc eps rho0
        (by simpa [I] using hv) (hanchor v (by simpa [I] using hv)) hlog6)
    hmass (by simpa [I] using
      sliceA2ExceptionalI_card_primeLog A1 epsc eps rho0 hlog1)
    (by convert hfixed using 1 <;> ring)
  simpa [I, Function.comp_def] using hresult

end Tao2015

end MoltResearch
