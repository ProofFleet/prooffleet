import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryMainData

/-!
# Track R A2-V': instantiated positive ordinary main term

All structural inputs of the cell-local L3 wrapper are now supplied by the
two-ratio ladder.  Only the window-scale guards, moment envelope and final
numerical fit remain visible.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

set_option maxHeartbeats 800000 in
/-- A positive ordinary level of the final ladder satisfies its main-term
allocation once the displayed scale and envelope inequalities hold. -/
theorem sliceA2_later_level_main
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pu : Finset ℕ)
    (P0 ratio0 eta J j : ℕ) (hP0 : 2 ≤ P0) (hj0 : 0 < j) (hjJ : j < J)
    (eps rho0 tau L T K1 K2 : ℝ)
    (htauEq : tau = 2 * T / A) (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hx : ∀ v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      1 ≤ (sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v : ℝ) * tau)
    (hqguard : ∀ v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      Delta + sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v ≤ A)
    (h2qA : ∀ v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      2 * sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v ≤ A)
    (hT : 0 < T)
    (hanchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r)
    (hlogAnchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      256 ≤ Real.log (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r))
    (hL : 1 ≤ L)
    (hellL : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      ∀ v ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      (sliceA2LaterMoment
        (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0) tau r v : ℝ) ≤ L)
    (hfar : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      (2 * Real.log L + 3) /
          Real.log (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r) ≤
        innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1))
    (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hprevCells : (Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)).Nonempty)
    (hnumerology : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).card : ℝ) ^ 2 *
        ordinaryLadderCellEnvelope
          (sliceA2OrdinaryN P0 ratio0 eta j eps rho0)
          (sliceA2LadderP P0 ratio0 eta j)
          (sliceA2LadderQ P0 ratio0 eta (j - 1)) tau
          (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1)) L ≤
        ordinaryUniformCellShare j (Finset.Ico
          (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
          (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)) *
            (eps ^ 2 * rho0 / 8))
    (hTK2 : K2 + 2 ≤ T) :
    (∫ xi in bandPartOn
        (levelSmallSet
          (sliceA2LadderPrimes P0 ratio0 eta)
          (fun i => sliceA2OrdinaryN P0 ratio0 eta i eps rho0)
          (fun i => sliceA2OrdinaryV0 P0 ratio0 eta i eps rho0)
          (fun i => sliceA2OrdinaryV1 P0 ratio0 eta i eps rho0)
          g innerBandScheduleAlpha) J
        {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
      ‖typicalSCellUniformMain g A (A + Delta)
        (sliceA2LadderPrimes P0 ratio0 eta j)
        (innerBandLevelsBefore (sliceA2LadderPrimes P0 ratio0 eta) J j ++
          innerBandLevelsAfter (sliceA2LadderPrimes P0 ratio0 eta) Pu J j)
        (sliceA2OrdinaryN P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0) xi‖ ^ 2) ≤
      ordinaryLegShare j * bandBudget 1 eps ((Delta : ℝ) / A) := by
  let Pl := sliceA2LadderPrimes P0 ratio0 eta
  let Nl := fun i => sliceA2OrdinaryN P0 ratio0 eta i eps rho0
  let v0l := fun i => sliceA2OrdinaryV0 P0 ratio0 eta i eps rho0
  let v1l := fun i => sliceA2OrdinaryV1 P0 ratio0 eta i eps rho0
  let ql := fun i => sliceA2OrdinaryRepresentative P0 ratio0 eta i eps rho0
  let Pmom := sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0
  let t := sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0
  have hcellCur := sliceA2Ordinary_cell_data P0 ratio0 eta j eps rho0 hP0
  have hbounds := sliceA2OrdinaryAnchor_cell_bounds P0 ratio0 eta j eps rho0
    hP0 hj0 hanchor
  apply innerBand_later_level_main_of_envelope_ratio_cellMass
    g hg A Delta Pl Pu Nl v0l v1l ql J j hj0 hjJ
    (fun p hp => sliceA2LadderPrimes_prime P0 ratio0 eta (j - 1) p hp)
    Pmom t (sliceA2LadderP P0 ratio0 eta j)
    (sliceA2LadderQ P0 ratio0 eta (j - 1)) tau L T 1 eps rho0
  · exact sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  · exact sliceA2OrdinaryN_pos P0 ratio0 eta (j - 1) eps rho0
  · intro r hr
    exact (hanchor r hr).trans' (by norm_num)
  · intro r hr p hp
    exact (hbounds r hr p hp).1
  · intro r hr p hp
    exact (hbounds r hr p hp).2
  · exact (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans' (by norm_num)
  · intro v hv
    exact le_max_left _ _
  · intro r hr
    exact sliceA2OrdinaryAnchor_le_Q P0 ratio0 eta j eps rho0 hP0 hj0 r hr
  · intro v hv
    exact sliceA2OrdinaryCellScale_le_exp P0 ratio0 eta j eps rho0 hP0 v hv
  · intro r hr
    exact exp_cell_lower_le_two_anchor _ _ ((hanchor r hr).trans' (by norm_num))
  · exact htauEq
  · exact htau0
  · exact htau
  · exact hx
  · exact hcellCur.2.2.1
  · intro v hv
    exact le_max_right _ _
  · exact hqguard
  · exact h2qA
  · exact hT
  · exact sliceA2Ordinary_cell_mass_le_one P0 ratio0 eta j eps rho0
      hP0 hj0 hanchor hlogAnchor
  · exact hL
  · exact hellL
  · exact hfar
  · norm_num
  · exact hratio
  · exact hprevCells
  · simpa [Pl, Nl, v0l, v1l, Pmom, t] using hnumerology
  · exact hTK2

end Tao2015

end MoltResearch
