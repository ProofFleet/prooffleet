import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryWindowMargins

/-!
# Track R A2-V': closed ordinary schedule

The bottom main term, all positive main terms, and both wide-error families
are assembled for the concrete two-ratio ladder.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- Exact ordinary interface consumed by the shifted inner-band capstone. -/
def SliceA2OrdinaryScheduleClosed
    (g : ℕ → ℂ) (A Delta : ℕ) (Pu : Finset ℕ)
    (P0 ratio0 eta J : ℕ) (eps rho0 T K1 K2 : ℝ) : Prop :=
  let Pl := sliceA2LadderPrimes P0 ratio0 eta
  let Nl := fun j => sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let v0l := fun j => sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0
  let v1l := fun j => sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0
  let ql := fun j => sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0
  (∀ j < J,
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2) ≤
        sliceA2KappaMain j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ))) ∧
  (∀ j < J,
      2 * replacementEnergyBoundWide A (Pl j) (Nl j) T ≤
        sliceA2KappaReplacement j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ))) ∧
  (∀ j < J,
      8 * collisionEnergyBoundWide A (Pl j) T ≤
        sliceA2KappaCollision j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ))) ∧
  (∀ j < J,
      2 * sliceA2KappaMain j + 2 * sliceA2KappaReplacement j +
          2 * sliceA2KappaCollision j ≤ (1 : ℝ) / 2 ^ (j + 2))

set_option maxHeartbeats 1000000 in
/-- Fixed bottom margins and three window-scale inequalities close the
complete ordinary interface. -/
theorem sliceA2_ordinary_schedule_closed
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pu : Finset ℕ)
    (P0 ratio0 eta J Qlog0 : ℕ)
    (hP0 : 21 ≤ P0) (hJ : 0 < J) (hDelta : Delta ≤ A)
    (eps rho0 tau T K1 K2 : ℝ)
    (heps : 0 < eps) (hrho0 : 0 < rho0)
    (htauEq : tau = 2 * T / A) (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hfirst : 1 ≤ (sliceA2LadderP P0 ratio0 eta 1 : ℝ) * tau)
    (hdouble : 2 * sliceA2LadderQ P0 ratio0 eta (J - 1) ≤ A)
    (hcollar : Delta + sliceA2LadderQ P0 ratio0 eta (J - 1) ≤ A)
    (hT : 0 < T) (hTA : T ≤ A) (hTK2 : K2 + 2 ≤ T)
    (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hzeroFits : SliceA2OrdinaryZeroFits
      P0 ratio0 eta A eps rho0 T)
    (hlogP0 : Real.log 6 + 256 ≤ Real.log (P0 : ℝ))
    (hfarBottom :
      40960 * (2 * Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 11) ≤
        Real.log (P0 : ℝ))
    (hQlog : Qlog0 ≤ P0)
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hcloseBottom :
      sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 ^ 20 *
          (2 : ℝ) ^ 720 ≤ P0)
    (hcardScale :
      64 * 9 * Real.exp Real.pi *
          ((sliceA2LadderQ P0 ratio0 eta (J - 1) : ℝ) / A) ≤
        3 * eps ^ 2 * rho0 / (1024 * (2 : ℝ) ^ J))
    (hcollisionBottom :
      (160 * 2048 : ℝ) * Real.exp Real.pi ≤
        3 * eps ^ 2 * rho0 * P0) :
    SliceA2OrdinaryScheduleClosed
      g A Delta Pu P0 ratio0 eta J eps rho0 T K1 K2 := by
  let Pl := sliceA2LadderPrimes P0 ratio0 eta
  let Nl := fun j => sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let v0l := fun j => sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0
  let v1l := fun j => sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0
  let ql := fun j => sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0
  have hP02 : 2 ≤ P0 := by omega
  have hQlast2 : 2 ≤ sliceA2LadderQ P0 ratio0 eta (J - 1) :=
    (sliceA2LadderP_two_le P0 ratio0 eta (J - 1) hP02).trans
      (sliceA2LadderP_le_Q P0 ratio0 eta (J - 1))
  have hA : 2 ≤ A := by omega
  have hguards := sliceA2Ordinary_representative_guards
    P0 ratio0 eta J A Delta eps rho0 hP02 hJ hdouble hcollar
  have hx := sliceA2Ordinary_cellScale_mul_tau_one_le
    P0 ratio0 eta J eps rho0 tau hP02 htau0 hfirst
  have hQthreshold := sliceA2Ordinary_Qlog_threshold
    P0 ratio0 eta J Qlog0 hP02 hQlog
  have hzero :
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} 0,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl 0)
          (innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0)
          (Nl 0) (v0l 0) (v1l 0) (ql 0) xi‖ ^ 2) ≤
        sliceA2KappaMain 0 *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)) := by
    simpa [Pl, Nl, v0l, v1l, ql] using
      sliceA2_level_zero_main_closed g hg A Delta Pu P0 ratio0 eta J
        (by omega) hJ hDelta eps rho0 T K1 K2
        (hguards.1 0 hJ) hT hTK2 hratio hzeroFits
  have hlater : ∀ j, 0 < j → j < J →
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2) ≤
        sliceA2KappaMain j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj0 hjJ
    have hj := sliceA2_later_level_main_closed
      g hg A Delta Pu P0 ratio0 eta J j Qlog0 hP0 hj0 hjJ
      eps rho0 tau T K1 K2 heps hrho0 htauEq htau0 htau
      (fun v hv => hx j hj0 hjJ v)
      (fun v hv => hguards.2 j hjJ v)
      (fun v hv => hguards.1 j hjJ v)
      hT hratio hlogP0 hfarBottom (hQthreshold j hj0 hjJ)
      hlogFit hcloseBottom hTK2
    simpa [Pl, Nl, v0l, v1l, ql, sliceA2KappaMain] using hj
  obtain ⟨hreplacement, hcollision⟩ :=
    sliceA2Ordinary_all_wide_fits P0 ratio0 eta J A eps rho0
      ((Delta : ℝ) / A) T (by omega) hJ hA hTA heps hrho0 hratio
      hcardScale hcollisionBottom
  have hall := sliceA2_ordinary_schedule
    g A Delta Pl Pu J Nl v0l v1l ql K1 K2 T 1 eps
    hzero hlater (by simpa [Pl, Nl] using hreplacement)
      (by simpa [Pl] using hcollision)
  simpa [SliceA2OrdinaryScheduleClosed, Pl, Nl, v0l, v1l, ql] using hall

end Tao2015

end MoltResearch
