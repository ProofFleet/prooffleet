import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryCloseFit

/-!
# Track R A2-V': exact later-level numerology

The closed scalar estimate is converted back through the uniform
previous-cell share and the fixed ladder jump, producing the exact
`hnumerology` input of `sliceA2_later_level_main`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Every positive ordinary level satisfies the exact per-previous-cell
numerology once the two fixed bottom margins have been imposed. -/
theorem sliceA2Ordinary_later_numerology
    (P0 ratio0 eta j Qlog0 : ℕ) (eps rho0 tau : ℝ)
    (hP0 : 3 ≤ P0) (hj : 0 < j)
    (heps : 0 < eps) (hrho0 : 0 < rho0) (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hprevCells : (Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)).Nonempty)
    (hlogThreshold : Qlog0 ≤
      sliceA2LadderQ P0 ratio0 eta (j - 1))
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hbottom :
      sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 ^ 20 *
          (2 : ℝ) ^ 720 ≤ P0) :
    let Icur := Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)
    let Iprev := Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)
    let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
    let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
    (Icur.card : ℝ) ^ 2 *
        ordinaryLadderCellEnvelope
          (sliceA2OrdinaryN P0 ratio0 eta j eps rho0)
          (sliceA2LadderP P0 ratio0 eta j) Qprev tau
          (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1)) L ≤
      ordinaryUniformCellShare j Iprev * (eps ^ 2 * rho0 / 8) := by
  dsimp only
  let Icur := Finset.Ico
    (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
    (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)
  let Iprev := Finset.Ico
    (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
    (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
  let R := (Icur.card : ℝ) ^ 2 *
    (Real.exp (innerBandScheduleAlpha j / (N : ℝ) +
        2 * (2 * Real.log L + 3) + 10) *
      tau ^ (2 * innerBandScheduleAlpha (j - 1)) *
      (Qprev : ℝ) ^ (-(9 : ℝ) / 20))
  have hreduce := sliceA2Ordinary_reduced_cost_le_close_envelope
    P0 ratio0 eta j eps rho0 tau hP0 hj heps hrho0 htau0 htau
  have hclose := sliceA2Ordinary_close_envelope_fit
    P0 ratio0 eta j Qlog0 eps rho0 hP0 hj heps hrho0
      hlogThreshold hlogFit hbottom
  have hmult : R * (Iprev.card : ℝ) ≤
      ordinaryLegShare j * eps ^ 2 * rho0 / 8 := by
    have hreduce' : R * (Iprev.card : ℝ) ≤
        sliceA2OrdinaryCellCountCoefficient eps rho0 ^ 3 * Real.exp 17 *
          (2 : ℝ) ^ (3 * j) * L ^ 8 * Real.log (Qprev : ℝ) ^ 6 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by
      simpa [R, Icur, Iprev, N, L, Qprev] using hreduce
    have hclose' :
        sliceA2OrdinaryCellCountCoefficient eps rho0 ^ 3 * Real.exp 17 *
            (2 : ℝ) ^ (3 * j) * L ^ 8 * Real.log (Qprev : ℝ) ^ 6 *
            (Qprev : ℝ) ^ (-(9 : ℝ) / 20) ≤
          ordinaryLegShare j * eps ^ 2 * rho0 / 8 := by
      simpa [L, Qprev] using hclose
    exact hreduce'.trans hclose'
  have hcardPos : (0 : ℝ) < Iprev.card := by
    exact_mod_cast (Finset.card_pos.mpr (by simpa [Iprev] using hprevCells))
  have hrhs :
      (ordinaryLegShare j / (Iprev.card : ℝ)) * (3 * rho0) * eps ^ 2 / 24 =
        (ordinaryLegShare j * eps ^ 2 * rho0 / 8) / (Iprev.card : ℝ) := by
    field_simp
    ring
  have hpoly : R ≤
      (ordinaryLegShare j / (Iprev.card : ℝ)) * (3 * rho0) * eps ^ 2 / 24 := by
    rw [hrhs, le_div_iff₀ hcardPos]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmult
  have hQprev1 : 1 ≤ Qprev := by
    have hQ2 : 2 ≤ sliceA2LadderQ P0 ratio0 eta (j - 1) :=
      (sliceA2LadderP_two_le P0 ratio0 eta (j - 1) (by omega)).trans
        (sliceA2LadderP_le_Q P0 ratio0 eta (j - 1))
    simpa only [Qprev] using (show 1 ≤
      sliceA2LadderQ P0 ratio0 eta (j - 1) by omega)
  have hschedule := ordinaryLadder_card_envelope_le_of_schedule
    Icur Iprev N Qprev tau L (3 * rho0) eps j hj hQprev1 htau0
      (by simpa [R] using hpoly)
  have hpred : j - 1 + 1 = j := by omega
  have hPshape : sliceA2LadderP P0 ratio0 eta j = Qprev ^ (100 * j ^ 2) := by
    simpa only [hpred, Qprev] using sliceA2LadderP_succ P0 ratio0 eta (j - 1)
  have hrhsSchedule :
      (ordinaryLegShare j / (Iprev.card : ℝ)) * (3 * rho0) * eps ^ 2 / 24 =
        (ordinaryLegShare j / (Iprev.card : ℝ)) * (eps ^ 2 * rho0 / 8) := by
    ring
  rw [hrhsSchedule] at hschedule
  simpa [Icur, Iprev, N, L, Qprev, hPshape, ordinaryUniformCellShare] using hschedule

end Tao2015

end MoltResearch
