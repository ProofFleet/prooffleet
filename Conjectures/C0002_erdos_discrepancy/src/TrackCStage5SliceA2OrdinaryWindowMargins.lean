import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZeroMainClose

/-!
# Track R A2-V': ordinary window margins

All quotient and collar guards reduce to the last ordinary endpoint.  The
positive-level moment lower guard reduces to the first ladder jump.
-/

namespace MoltResearch

namespace Tao2015

/-- The empty-cell-safe ordinary representative never exceeds its level's
upper endpoint. -/
theorem sliceA2OrdinaryRepresentative_le_Q
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (v : ℕ) (hP0 : 2 ≤ P0) :
    sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v ≤
      sliceA2LadderQ P0 ratio0 eta j := by
  classical
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let P := sliceA2LadderPrimes P0 ratio0 eta j
  have hN : 0 < N := by
    dsimp [N]
    exact sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  unfold sliceA2OrdinaryRepresentative sliceA2LevelRepresentative
    scaleCellRepresentative
  split_ifs with hcell
  · obtain ⟨p, hp⟩ := hcell
    have hpPrime := sliceA2LadderPrimes_prime P0 ratio0 eta j p
      (mem_eadicCell.mp hp).1
    exact (ceil_cell_lower_le hN hp hpPrime.one_le).trans
      (sliceA2LadderPrimes_bounds P0 ratio0 eta j p
        (mem_eadicCell.mp hp).1).2
  · have hQ2 : 2 ≤ sliceA2LadderQ P0 ratio0 eta j :=
      (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans
        (sliceA2LadderP_le_Q P0 ratio0 eta j)
    omega

/-- A last-endpoint bound supplies every ordinary quotient and collar
guard, including the unrestricted level-zero representative guard. -/
theorem sliceA2Ordinary_representative_guards
    (P0 ratio0 eta J A Delta : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (hJ : 0 < J)
    (hdouble : 2 * sliceA2LadderQ P0 ratio0 eta (J - 1) ≤ A)
    (hcollar : Delta + sliceA2LadderQ P0 ratio0 eta (J - 1) ≤ A) :
    (∀ j < J, ∀ v,
      2 * sliceA2OrdinaryRepresentative
        P0 ratio0 eta j eps rho0 v ≤ A) ∧
    (∀ j < J, ∀ v,
      Delta + sliceA2OrdinaryRepresentative
        P0 ratio0 eta j eps rho0 v ≤ A) := by
  constructor
  · intro j hj v
    have hq := sliceA2OrdinaryRepresentative_le_Q
      P0 ratio0 eta j eps rho0 v hP0
    have hlast := sliceA2LadderQ_le_last P0 ratio0 eta J j hP0 hJ hj
    omega
  · intro j hj v
    have hq := sliceA2OrdinaryRepresentative_le_Q
      P0 ratio0 eta j eps rho0 v hP0
    have hlast := sliceA2LadderQ_le_last P0 ratio0 eta J j hP0 hJ hj
    omega

/-- The first positive lower endpoint controls the moment lower guard at
every later level. -/
theorem sliceA2Ordinary_cellScale_mul_tau_one_le
    (P0 ratio0 eta J : ℕ) (eps rho0 tau : ℝ)
    (hP0 : 2 ≤ P0) (htau0 : 0 ≤ tau)
    (hfirst : 1 ≤ (sliceA2LadderP P0 ratio0 eta 1 : ℝ) * tau) :
    ∀ j, 0 < j → j < J → ∀ v,
      1 ≤ (sliceA2OrdinaryCellScale
        P0 ratio0 eta j eps rho0 v : ℝ) * tau := by
  intro j hj0 hjJ v
  have hPmono : sliceA2LadderP P0 ratio0 eta 1 ≤
      sliceA2LadderP P0 ratio0 eta j :=
    sliceA2LadderP_mono P0 ratio0 eta hP0 hj0
  have hPcell : sliceA2LadderP P0 ratio0 eta j ≤
      sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v := by
    unfold sliceA2OrdinaryCellScale
    exact le_max_left _ _
  have hscale : (sliceA2LadderP P0 ratio0 eta 1 : ℝ) ≤
      sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v := by
    exact_mod_cast hPmono.trans hPcell
  exact hfirst.trans (mul_le_mul_of_nonneg_right hscale htau0)

/-- A bottom threshold for the logarithmic comparison applies at every
positive level because each preceding upper endpoint lies above `P0`. -/
theorem sliceA2Ordinary_Qlog_threshold
    (P0 ratio0 eta J Qlog0 : ℕ) (hP0 : 2 ≤ P0)
    (hQlog : Qlog0 ≤ P0) :
    ∀ j, 0 < j → j < J →
      Qlog0 ≤ sliceA2LadderQ P0 ratio0 eta (j - 1) := by
  intro j hj0 hjJ
  exact hQlog.trans ((sliceA2LadderP_mono P0 ratio0 eta hP0
    (Nat.zero_le (j - 1))).trans (sliceA2LadderP_le_Q P0 ratio0 eta (j - 1)))

end Tao2015

end MoltResearch
