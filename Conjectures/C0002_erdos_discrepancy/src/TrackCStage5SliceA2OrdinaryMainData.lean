import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryMainCellMass

/-!
# Track R A2-V': concrete later-level main data

This leaf chooses the previous-cell anchor and the empty-cell-safe current
scale used in the positive ordinary levels.  Their exponential endpoint,
dyadic containment and cell-mass properties are then automatic.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Previous-cell lower anchor used by the borrowed moment. -/
noncomputable def sliceA2OrdinaryAnchor
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (r : ℕ) : ℕ :=
  eadicCellLowerAnchor
    (sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0) r

/-- Current scale used in the L3 envelope.  The maximum makes empty cells
harmless while retaining the true representative on occupied cells. -/
noncomputable def sliceA2OrdinaryCellScale
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (v : ℕ) : ℕ :=
  max (sliceA2LadderP P0 ratio0 eta j)
    (sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v)

/-- Every scheduled index lies above the lower endpoint on the exponential
scale, including indices of empty cells. -/
theorem sliceA2Ordinary_lower_le_exp
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0)
    (v : ℕ) (hv : v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)) :
    (sliceA2LadderP P0 ratio0 eta j : ℝ) ≤
      Real.exp (((v : ℝ) + 1) /
        (2 * (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ))) := by
  let P := sliceA2LadderP P0 ratio0 eta j
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  have hN : 0 < N := by simpa [N] using
    sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  have hP : 2 ≤ P := by simpa [P] using
    sliceA2LadderP_two_le P0 ratio0 eta j hP0
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hPreal : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hv0 : ordinaryLevelV0 P N ≤ v := by
    simpa [sliceA2OrdinaryV0, P, N] using (Finset.mem_Ico.mp hv).1
  have hceil1 : 1 ≤ ⌈(2 * N : ℕ) * Real.log P⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos (by positivity) hlogP)
  have hceilv : ⌈(2 * N : ℕ) * Real.log P⌉₊ ≤ v + 1 := by
    unfold ordinaryLevelV0 eadicCoverIndexLower at hv0
    omega
  have hlower : ((2 * N : ℕ) : ℝ) * Real.log P ≤ (v : ℝ) + 1 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilv)
  have hquot : Real.log P ≤ (v + 1 : ℝ) / (2 * N : ℕ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * N : ℕ))]
    simpa [mul_comm] using hlower
  calc
    (P : ℝ) = Real.exp (Real.log P) := (Real.exp_log hPreal).symm
    _ ≤ Real.exp ((v + 1 : ℝ) / (2 * N : ℕ)) :=
      Real.exp_le_exp.mpr hquot
    _ = Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
      push_cast
      ring_nf

/-- The chosen current scale remains below the cell's exponential upper
endpoint. -/
theorem sliceA2OrdinaryCellScale_le_exp
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0)
    (v : ℕ) (hv : v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)) :
    (sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v : ℝ) ≤
      Real.exp (((v : ℝ) + 1) /
        (2 * (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ))) := by
  have hcell := (sliceA2Ordinary_cell_data P0 ratio0 eta j eps rho0 hP0).2.1 v hv
  have hlower := sliceA2Ordinary_lower_le_exp P0 ratio0 eta j eps rho0
    hP0 v hv
  unfold sliceA2OrdinaryCellScale
  rw [Nat.cast_max]
  exact max_le hlower hcell

/-- A previous lower anchor never exceeds the previous level's upper
endpoint. -/
theorem sliceA2OrdinaryAnchor_le_Q
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0) (hj : 0 < j)
    (r : ℕ) (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)) :
    (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) ≤
      sliceA2LadderQ P0 ratio0 eta (j - 1) := by
  let N := sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0
  let Q := sliceA2LadderQ P0 ratio0 eta (j - 1)
  let x := Real.exp ((r : ℝ) / (2 * (N : ℝ)))
  have hN : 0 < N := by simpa [N] using
    sliceA2OrdinaryN_pos P0 ratio0 eta (j - 1) eps rho0
  have hQr : (0 : ℝ) < Q := by
    have hP := sliceA2LadderP_two_le P0 ratio0 eta (j - 1) hP0
    exact_mod_cast (show 0 < Q by
      exact lt_of_lt_of_le (by omega) (sliceA2LadderP_le_Q P0 ratio0 eta (j - 1)))
  have hrUpper : r ≤ ordinaryLevelV1 Q N := by
    have := (Finset.mem_Ico.mp hr).2
    simpa [sliceA2OrdinaryV1, Q, N] using (show r ≤
      sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 by omega)
  have hfloor : (r : ℝ) ≤ (2 * N : ℕ) * Real.log Q := by
    unfold ordinaryLevelV1 eadicCoverIndexUpper at hrUpper
    exact (by exact_mod_cast hrUpper : (r : ℝ) ≤ ⌊(2 * N : ℕ) * Real.log Q⌋₊) |>.trans
      (Nat.floor_le (by positivity))
  have hexpQ : x ≤ Q := by
    have hNreal : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    have hdiv : (r : ℝ) / (2 * (N : ℝ)) ≤ Real.log Q := by
      rw [div_le_iff₀ hNreal]
      simpa [mul_comm] using hfloor
    calc
      x ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr hdiv
      _ = Q := Real.exp_log hQr
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hanchorX : (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) ≤ x := by
    have hceil := Nat.ceil_lt_add_one hx0
    unfold sliceA2OrdinaryAnchor eadicCellLowerAnchor
    rw [Nat.cast_sub hceil1]
    push_cast
    linarith
  exact hanchorX.trans hexpQ

/-- The standard lower anchor gives dyadic containment of an occupied
previous cell. -/
theorem sliceA2OrdinaryAnchor_cell_bounds
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0)
    (hj : 0 < j)
    (hanchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
        6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r) :
    ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      ∀ p ∈ eadicCell (sliceA2LadderPrimes P0 ratio0 eta (j - 1))
          (2 * sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0) r,
        sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r < p ∧
          p ≤ 2 * sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r := by
  intro r hr
  exact eadicCell_mem_lowerAnchor_dyadic
    (sliceA2LadderPrimes P0 ratio0 eta (j - 1))
    (fun p hp => sliceA2LadderPrimes_prime P0 ratio0 eta (j - 1) p hp)
    (sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0) r
    (by
      unfold sliceA2OrdinaryN
      exact sliceA2LevelN_two_le _ _ _ _ _)
    (hanchor r hr)

/-- Once the anchor logarithm is at least `256`, every preceding cell has
reciprocal-prime mass at most one. -/
theorem sliceA2Ordinary_cell_mass_le_one
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0)
    (hj : 0 < j)
    (hanchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
        6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r)
    (hlog : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
        256 ≤ Real.log (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r)) :
    ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      ∑ p ∈ eadicCell (sliceA2LadderPrimes P0 ratio0 eta (j - 1))
          (2 * sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0) r,
        (1 : ℝ) / p ≤ 1 := by
  intro r hr
  have hb := sliceA2OrdinaryAnchor_cell_bounds P0 ratio0 eta j eps rho0
    hP0 hj hanchor r hr
  have hm := sum_one_div_prime_dyadic_le
    (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r)
    (by have := hanchor r hr; omega)
    (eadicCell (sliceA2LadderPrimes P0 ratio0 eta (j - 1))
      (2 * sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0) r)
    (fun p hp => sliceA2LadderPrimes_prime P0 ratio0 eta (j - 1) p
      (mem_eadicCell.mp hp).1)
    (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2)
  exact hm.trans (by
    have hp := hlog r hr
    have hlog0 : 0 < Real.log (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r) :=
      lt_of_lt_of_le (by norm_num) hp
    rw [div_le_one hlog0]
    exact hp)

end Tao2015

end MoltResearch
