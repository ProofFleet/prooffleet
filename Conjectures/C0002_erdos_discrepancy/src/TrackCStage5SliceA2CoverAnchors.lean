import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverCellMargins

/-!
# Track R A2-V': last-level cover anchors

The least-crossing property puts the last ordinary lower endpoint above
`(log A1)^40`; hence every lower cell anchor has logarithm at least `256`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The cutoff lower bound supplies both anchor hypotheses used by the raw
high-moment cover estimate. -/
theorem sliceA2Ordinary_last_anchor_margins_of_reaches
    (P0 ratio0 eta J A1 r : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0)
    (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1))
    (hX : 12 ≤ Real.log (A1 : ℝ))
    (hlogX : 7 ≤ Real.log (Real.log (A1 : ℝ)))
    (hreaches : ordinaryLadderCutoff A1 ≤
      (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ)) :
    6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r ∧
      256 ≤ Real.log
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ) := by
  let X := Real.log (A1 : ℝ)
  let P := sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hXone : 1 ≤ X := by dsimp [X]; linarith
  have hcut21 : (21 : ℝ) ≤ ordinaryLadderCutoff A1 := by
    unfold ordinaryLadderCutoff
    have hx2 : (21 : ℝ) ≤ X ^ (2 : ℕ) := by nlinarith [sq_nonneg (X - 12)]
    exact hx2.trans (pow_le_pow_right₀ hXone (by norm_num : (2 : ℕ) ≤ 40))
  have hPlevel21 : 21 ≤ sliceA2LadderP P0 ratio0 eta (J - 1) := by
    exact_mod_cast hcut21.trans hreaches
  have hanchorRaw : 6 ≤
      eadicCellLowerAnchor
        (sliceA2OrdinaryN P0 ratio0 eta (J - 1) eps rho0) r := by
    apply eadicCellLowerAnchor_six_of_cover_lower
      (sliceA2OrdinaryN P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2LadderP P0 ratio0 eta (J - 1)) r
      (sliceA2OrdinaryN_pos P0 ratio0 eta (J - 1) eps rho0)
      hPlevel21
    have := (Finset.mem_Ico.mp hr).1
    simpa [sliceA2OrdinaryV0, ordinaryLevelV0] using this
  have hanchor : 6 ≤ P := by simpa [P, sliceA2OrdinaryAnchor] using hanchorRaw
  have hPlevel := sliceA2LadderP_le_six_mul_ordinaryAnchor
    P0 ratio0 eta J r eps rho0 hP0 hr (by omega)
  have hPlevelPos : (0 : ℝ) <
      sliceA2LadderP P0 ratio0 eta (J - 1) := by positivity
  have hPpos : (0 : ℝ) < P := by
    have : (0 : ℝ) < 6 * (P : ℝ) := hPlevelPos.trans_le (by
      simpa [P] using hPlevel)
    positivity
  have hlogLevel : 40 * Real.log X ≤
      Real.log (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ) := by
    have hcutPos : 0 < ordinaryLadderCutoff A1 := by
      unfold ordinaryLadderCutoff
      positivity
    have hlogs := Real.log_le_log hcutPos hreaches
    unfold ordinaryLadderCutoff at hlogs
    rw [Real.log_pow] at hlogs
    norm_num at hlogs
    simpa [X] using hlogs
  have hlogSixP :
      Real.log (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ) ≤
        Real.log 6 + Real.log (P : ℝ) := by
    calc
      Real.log (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ) ≤
          Real.log (6 * (P : ℝ)) :=
        Real.log_le_log hPlevelPos (by simpa [P] using hPlevel)
      _ = Real.log 6 + Real.log (P : ℝ) :=
        Real.log_mul (by norm_num) hPpos.ne'
  have hlog6 : Real.log 6 ≤ 3 := by
    exact (Real.log_le_log (by norm_num) (by norm_num : (6 : ℝ) ≤ 9)).trans
      (log_nine_le.trans (by norm_num))
  have hlogAnchor : 256 ≤ Real.log (P : ℝ) := by
    have : 40 * Real.log X - 3 ≤ Real.log (P : ℝ) := by linarith
    change 7 ≤ Real.log X at hlogX
    linarith
  exact ⟨by simpa [P] using hanchor, by simpa [P] using hlogAnchor⟩

/-- Beyond the scalar cover threshold, the selected last-level anchors meet
the raw cover theorem's two lower bounds simultaneously. -/
theorem exists_sliceA2Ordinary_last_anchor_margins
    (P0 ratio0 eta : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      0 < J ∧
      ∀ r ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
        6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r ∧
          256 ≤ Real.log
            (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ) := by
  obtain ⟨A0, hA0⟩ := exists_sliceA2Cover_scalar_margins
  refine ⟨A0, fun A1 hA1 => ?_⟩
  obtain ⟨hX, hlogX, hscalar⟩ := hA0 A1 hA1
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  have hJ : 0 < J := by
    dsimp [J]
    exact sliceA2LadderJ_pos P0 ratio0 eta A1 hP0
  refine ⟨hJ, fun r hr => ?_⟩
  apply sliceA2Ordinary_last_anchor_margins_of_reaches
    P0 ratio0 eta J A1 r eps rho0 hP0 hr hX hlogX
  simpa [J] using sliceA2LadderJ_last_reaches P0 ratio0 eta A1 hP0

end Tao2015

end MoltResearch
