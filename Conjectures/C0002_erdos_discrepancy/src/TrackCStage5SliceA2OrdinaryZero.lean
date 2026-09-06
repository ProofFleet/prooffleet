import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryLater

/-!
# Track R A2-V': instantiated level-zero main term

The bottom-level analytic theorem is specialized to the final ladder cells,
the inner-band partition, `R = 2`, and the sharp quotient harmonic bound
`log 4`.  Only its two closed schedule inequalities remain.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- Exact endpoint inequalities for the final ordinary index range. -/
theorem sliceA2Ordinary_index_endpoints
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) (hP0 : 2 ≤ P0) :
    ((sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 : ℝ) ≤
      2 * (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ) *
        Real.log (sliceA2LadderQ P0 ratio0 eta j)) ∧
    (2 * (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ) *
        Real.log (sliceA2LadderP P0 ratio0 eta j) - 1 ≤
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0 : ℝ)) := by
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let P := sliceA2LadderP P0 ratio0 eta j
  let Q := sliceA2LadderQ P0 ratio0 eta j
  have hP : 2 ≤ P := by simpa [P] using
    sliceA2LadderP_two_le P0 ratio0 eta j hP0
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hN : 0 < N := by simpa [N] using
    sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  constructor
  · unfold sliceA2OrdinaryV1 ordinaryLevelV1 eadicCoverIndexUpper
    have hf := Nat.floor_le (show 0 ≤ ((2 * N : ℕ) : ℝ) * Real.log Q by
      have hQ : P ≤ Q := sliceA2LadderP_le_Q P0 ratio0 eta j
      have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      positivity)
    simpa [N, Q] using hf
  · unfold sliceA2OrdinaryV0 ordinaryLevelV0 eadicCoverIndexLower
    have hceil1 : 1 ≤ ⌈((2 * N : ℕ) : ℝ) * Real.log P⌉₊ :=
      Nat.one_le_ceil_iff.mpr (by positivity)
    have hc := Nat.le_ceil (((2 * N : ℕ) : ℝ) * Real.log P)
    rw [Nat.cast_sub hceil1]
    push_cast
    simpa [N, P] using (sub_le_sub_right hc 1)

set_option maxHeartbeats 800000 in
/-- The final level-zero cells satisfy the main-term allocation from the two
closed scale inequalities below. -/
theorem sliceA2_level_zero_main
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pu : Finset ℕ) (P0 ratio0 eta J : ℕ)
    (hP0 : 2 ≤ P0) (hJ : 0 < J) (hDelta : Delta ≤ A)
    (eps rho0 T K1 K2 : ℝ)
    (h2qA : ∀ v, 2 * sliceA2OrdinaryRepresentative
      P0 ratio0 eta 0 eps rho0 v ≤ A)
    (hT : 0 < T) (hTK2 : K2 + 2 ≤ T)
    (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hfitT :
      (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
        (Real.exp Real.pi * Real.log 4 *
          ((2 * T * Real.exp
              (1 / ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ)) /
              (A : ℝ)) *
            ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^
                (1 - 2 * innerBandScheduleAlpha 0) *
              Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
            (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
                (1 - 2 * innerBandScheduleAlpha 0) + 1))) ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8))
    (hfitP :
      (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
        (Real.exp Real.pi * Real.log 4 *
          (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
              (-(2 * innerBandScheduleAlpha 0)) *
            Real.exp (2 * innerBandScheduleAlpha 0 /
              ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
            (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
              (2 * innerBandScheduleAlpha 0) + 1))) ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8)) :
    (∫ xi in bandPartOn
        (levelSmallSet
          (sliceA2LadderPrimes P0 ratio0 eta)
          (fun i => sliceA2OrdinaryN P0 ratio0 eta i eps rho0)
          (fun i => sliceA2OrdinaryV0 P0 ratio0 eta i eps rho0)
          (fun i => sliceA2OrdinaryV1 P0 ratio0 eta i eps rho0)
          g innerBandScheduleAlpha) J
        {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} 0,
      ‖typicalSCellUniformMain g A (A + Delta)
        (sliceA2LadderPrimes P0 ratio0 eta 0)
        (innerBandLevelsBefore (sliceA2LadderPrimes P0 ratio0 eta) J 0 ++
          innerBandLevelsAfter (sliceA2LadderPrimes P0 ratio0 eta) Pu J 0)
        (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0)
        (sliceA2OrdinaryV0 P0 ratio0 eta 0 eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta 0 eps rho0)
        (sliceA2OrdinaryRepresentative P0 ratio0 eta 0 eps rho0) xi‖ ^ 2) ≤
      sliceA2KappaMain 0 * bandBudget 1 eps ((Delta : ℝ) / A) := by
  let Pl := sliceA2LadderPrimes P0 ratio0 eta
  let Nl := fun i => sliceA2OrdinaryN P0 ratio0 eta i eps rho0
  let v0l := fun i => sliceA2OrdinaryV0 P0 ratio0 eta i eps rho0
  let v1l := fun i => sliceA2OrdinaryV1 P0 ratio0 eta i eps rho0
  let ql := fun i => sliceA2OrdinaryRepresentative P0 ratio0 eta i eps rho0
  let band := {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2}
  let G := bandPartOn (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J band 0
  have hN := sliceA2OrdinaryN_pos P0 ratio0 eta 0 eps rho0
  have hcell := sliceA2Ordinary_cell_data P0 ratio0 eta 0 eps rho0 hP0
  have hend := sliceA2Ordinary_index_endpoints P0 ratio0 eta 0 eps rho0 hP0
  have halpha := innerBandScheduleAlpha_bounds 0
  have hA2 : 2 ≤ A := by
    have hq := hcell.2.2.1 0
    have hs := h2qA 0
    omega
  have hAreal : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have halphaDen : 0 < 1 - 2 * innerBandScheduleAlpha 0 := by
    linarith [halpha.2]
  have hPReal : (0 : ℝ) < sliceA2LadderP P0 ratio0 eta 0 := by
    exact_mod_cast (show 0 < sliceA2LadderP P0 ratio0 eta 0 by
      have := sliceA2LadderP_two_le P0 ratio0 eta 0 hP0
      omega)
  have hPpow : 0 ≤ (sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
      (-(2 * innerBandScheduleAlpha 0)) :=
    (Real.rpow_pos_of_pos hPReal _).le
  have hcount := ordinaryLevel_cell_card_le
    (sliceA2LadderP P0 ratio0 eta 0) (sliceA2LadderQ P0 ratio0 eta 0)
    (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0)
    (sliceA2LadderP_two_le P0 ratio0 eta 0 hP0)
    (sliceA2LadderP_le_Q P0 ratio0 eta 0) hN
  have hfitT' := (mul_le_mul_of_nonneg_right hcount (by positivity :
      0 ≤ Real.exp Real.pi * Real.log 4 *
        ((2 * T * Real.exp
            (1 / ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ)) / A) *
          ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^
              (1 - 2 * innerBandScheduleAlpha 0) *
            Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
              ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
          (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
            (1 - 2 * innerBandScheduleAlpha 0) + 1)))).trans hfitT
  have hfitPfactor : 0 ≤ Real.exp Real.pi * Real.log 4 *
      (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
          (-(2 * innerBandScheduleAlpha 0)) *
        Real.exp (2 * innerBandScheduleAlpha 0 /
          ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
        (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
          (2 * innerBandScheduleAlpha 0) + 1)) := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlast : 0 ≤
        ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
          (2 * innerBandScheduleAlpha 0) + 1 := by
      exact add_nonneg (div_nonneg (by positivity)
        (mul_nonneg (by norm_num) halpha.1.le)) (by norm_num)
    exact mul_nonneg (mul_nonneg (by positivity) hlog4)
      (mul_nonneg (mul_nonneg (by positivity)
        (mul_nonneg hPpow (by positivity))) hlast)
  have hfitP' := (mul_le_mul_of_nonneg_right hcount (hfitPfactor)).trans hfitP
  have hGm : MeasurableSet G := bandPartOn_measurableSet _
    (fun i => levelSmallSet_measurableSet Pl Nl v0l v1l g
      innerBandScheduleAlpha i) J band (measurableSet_inner_band K1 K2) 0
  have hGT : G ⊆ Set.Ioc (-T) T :=
    innerBandPartOn_subset_Ioc _ J 0 K1 K2 T hTK2
  have hC : ∀ v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta 0 eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta 0 eps rho0 + 1),
      ∑ m ∈ Finset.Ioc
        (A / sliceA2OrdinaryRepresentative P0 ratio0 eta 0 eps rho0 v)
        ((A + Delta) / sliceA2OrdinaryRepresentative P0 ratio0 eta 0 eps rho0 v),
        (1 : ℝ) / m ≤ Real.log 4 := by
    intro v hv
    convert quotient_harmonic_le_log_two_mul A (A + Delta)
      (sliceA2OrdinaryRepresentative P0 ratio0 eta 0 eps rho0 v) 2
      (hcell.2.2.1 v) (by have := h2qA v; omega) (by norm_num) (by omega)
      using 1 <;> norm_num
  have hsmall : ∀ v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta 0 eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta 0 eps rho0 + 1), ∀ xi ∈ G,
      ‖levelCellPoly (sliceA2LadderPrimes P0 ratio0 eta 0)
        (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0) v g xi‖ ≤
        Real.exp (-(innerBandScheduleAlpha 0 * (v : ℝ) /
          ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) := by
    intro v hv xi hxi
    exact levelSmallSet_small_of_mem_bandPartOn Pl Nl v0l v1l g
      innerBandScheduleAlpha J 0 band xi hJ (by simpa [G] using hxi) v hv
  exact band_energy_level_zero_main_of_ratio
    (sliceA2LadderPrimes P0 ratio0 eta 0)
    (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0) hN
    (sliceA2OrdinaryV0 P0 ratio0 eta 0 eps rho0)
    (sliceA2OrdinaryV1 P0 ratio0 eta 0 eps rho0)
    (sliceA2OrdinaryRepresentative P0 ratio0 eta 0 eps rho0)
    A (A + Delta) 2 (by norm_num) (by omega)
    hcell.2.2.1 h2qA hcell.2.1 g hg
    (typicalS 0 (A + Delta)
      (innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0))
    T hT G hGm hGT (innerBandScheduleAlpha 0) halpha.1
    (by linarith [halpha.2]) (Real.log 4) (Real.log_nonneg (by norm_num))
    hC hsmall (sliceA2LadderP P0 ratio0 eta 0)
    (sliceA2LadderQ P0 ratio0 eta 0) 1 eps rho0 ((Delta : ℝ) / A)
    (sliceA2KappaMain 0) hPReal
    (hPReal.trans_le (by exact_mod_cast sliceA2LadderP_le_Q P0 ratio0 eta 0))
    hend.1 hend.2 (by norm_num) (sliceA2Kappa_nonneg 0).1 hratio
    (by simpa [sliceA2OrdinaryV0, sliceA2OrdinaryV1, one_mul] using hfitT')
    (by simpa [sliceA2OrdinaryV0, sliceA2OrdinaryV1, one_mul,
      show 4 * (2 : ℝ) = 8 by norm_num] using hfitP')

end Tao2015

end MoltResearch
