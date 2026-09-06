import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryNumerologyClose
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZero

/-!
# Track R A2-V': closed positive ordinary levels

All scale-free positive-level conditions are now automatic from the fixed
bottom margins.  Only the ambient-window inequalities remain as inputs.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- Every canonical ordinary index range is nonempty. -/
theorem sliceA2Ordinary_index_nonempty
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0) :
    (Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).Nonempty := by
  rw [Finset.nonempty_Ico]
  suffices sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0 ≤
      sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 by omega
  let P := sliceA2LadderP P0 ratio0 eta j
  let Q := sliceA2LadderQ P0 ratio0 eta j
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let x : ℝ := (2 * N : ℕ) * Real.log (P : ℝ)
  let y : ℝ := (2 * N : ℕ) * Real.log (Q : ℝ)
  have hP2 : 2 ≤ P := by
    dsimp [P]
    exact sliceA2LadderP_two_le P0 ratio0 eta j hP0
  have hPQ : P ≤ Q := by
    dsimp [P, Q]
    exact sliceA2LadderP_le_Q P0 ratio0 eta j
  have hN : 0 < N := by
    dsimp [N]
    exact sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (by
    dsimp [x]
    positivity)
  have hpredX : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
    have hc := Nat.ceil_lt_add_one hx0
    rw [Nat.cast_sub hceil1]
    push_cast
    linarith
  have hxy : x ≤ y := by
    dsimp [x, y]
    have hlogPQ : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hPQ)
    gcongr
  have hfloor : ⌈x⌉₊ - 1 ≤ ⌊y⌋₊ :=
    Nat.le_floor (hpredX.le.trans hxy)
  simpa [sliceA2OrdinaryV0, sliceA2OrdinaryV1, ordinaryLevelV0,
    ordinaryLevelV1, eadicCoverIndexLower, eadicCoverIndexUpper, P, Q, N, x, y]
    using hfloor

set_option maxHeartbeats 800000 in
/-- Positive ordinary levels with every scale-free schedule condition
discharged by the fixed bottom margins. -/
theorem sliceA2_later_level_main_closed
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pu : Finset ℕ)
    (P0 ratio0 eta J j Qlog0 : ℕ)
    (hP0 : 21 ≤ P0) (hj0 : 0 < j) (hjJ : j < J)
    (eps rho0 tau T K1 K2 : ℝ)
    (heps : 0 < eps) (hrho0 : 0 < rho0)
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
    (hT : 0 < T) (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hlogP0 : Real.log 6 + 256 ≤ Real.log (P0 : ℝ))
    (hfarBottom :
      40960 * (2 * Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 11) ≤
        Real.log (P0 : ℝ))
    (hlogThreshold : Qlog0 ≤
      sliceA2LadderQ P0 ratio0 eta (j - 1))
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hcloseBottom :
      sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 ^ 20 *
          (2 : ℝ) ^ 720 ≤ P0)
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
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  have hanchor := fun r hr => sliceA2Ordinary_anchor_six
    P0 ratio0 eta j eps rho0 hP0 hj0 r hr
  have hlogAnchor := fun r hr => sliceA2Ordinary_anchor_log_margin
    P0 ratio0 eta j eps rho0 hP0 hj0 hlogP0 r hr
  have hL : 1 ≤ L := by
    dsimp [L]
    exact sliceA2OrdinaryMomentEnvelope_one_le ratio0 eta j
  have hellL := sliceA2LaterMoment_le_envelope
    P0 ratio0 eta j eps rho0 tau hP0 hj0 htau0 htau hx
  have hfar := fun r hr => sliceA2Ordinary_far_margin
    P0 ratio0 eta j eps rho0 hP0 hj0 hfarBottom r hr
  have hprevCells := sliceA2Ordinary_index_nonempty
    P0 ratio0 eta (j - 1) eps rho0 (by omega)
  have hnumerology := sliceA2Ordinary_later_numerology
    P0 ratio0 eta j Qlog0 eps rho0 tau (by omega) hj0 heps hrho0 htau0 htau
      hprevCells hlogThreshold hlogFit hcloseBottom
  exact sliceA2_later_level_main g hg A Delta Pu P0 ratio0 eta J j (by omega)
    hj0 hjJ eps rho0 tau L T K1 K2 htauEq htau0 htau hx hqguard h2qA hT
    hanchor hlogAnchor hL hellL hfar hratio hprevCells
    (fun _r _hr => by simpa [L] using hnumerology) hTK2

end Tao2015

end MoltResearch
