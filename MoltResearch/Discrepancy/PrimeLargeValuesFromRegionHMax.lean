import MoltResearch.Discrepancy.PrimeLargeValuesFromRegionH

/-!
# Prime large values at the balanced contour height

The right-line truncation tail for the Mellin window is balanced against the
zero-free saving by taking the rectangle height

`max (8 * pi * T) (exp ((log P) ^ (1 / (1 + theta))))`.

Unlike the earlier square-root-height wrapper, this height does not make the
zero-free width collapse to a power of `log P` in the intermediate range.
-/

namespace MoltResearch

open Complex ExpSums Finset
open scoped ContDiff

/-- The balanced rectangle height used in V-B″. -/
noncomputable def zeroFreeRegionHeightHMax (theta T P : ℝ) : ℝ :=
  max (8 * Real.pi * T)
    (Real.exp ((Real.log P) ^ (1 / (1 + theta))))

set_option maxHeartbeats 800000

/-- **V-B″-1.**  The V-A kernel estimate at the balanced rectangle height,
with both analytic parameters evaluated at that same height. -/
theorem exists_primeMellin_kernel_bound_of_zeroFreeRegionDataHMax
    {theta m : ℝ} (h : ZeroFreeRegionDataH theta m) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀
      (S : ℝ → ℝ) (C P T u : ℝ),
      ContDiff ℝ ∞ S →
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) →
      (∀ v, v ≤ 0 → S v = 0) →
      (∀ v, 1 ≤ v → S v = 1) →
      0 ≤ C → (∀ v, |deriv S v| ≤ C) →
      (∀ v, |deriv (deriv S) v| ≤ C) →
      2 ≤ P → 1 ≤ T → 1 ≤ |u| → |u| ≤ 4 * Real.pi * T →
      let Z := zeroFreeRegionHeightHMax theta T P
      let eta := zeroFreeRegionEtaH theta h.eta0 Z
      let M := zeroFreeRegionRegularBoundH m h.M0 Z
      let c := 1 + 1 / Real.log (2 * P)
      ‖∑ p ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter Nat.Prime,
          ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
            (p : ℂ) ^ (I * (u : ℂ))‖ ≤
        (250000 * (C + 1) ^ 2 * P) / |u| ^ 2 +
          K * (C + 1) ^ 2 * (M + 1) *
            (P ^ (1 - eta / 2) +
              P ^ c * Real.log (2 * P) / (Z - |u|) +
              P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
  obtain ⟨K, hK, hkernel⟩ := exists_primeMellin_kernel_bound
  refine ⟨K, hK, ?_⟩
  intro S C P T u hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hT hu1 huT
  let Z := zeroFreeRegionHeightHMax theta T P
  let eta := zeroFreeRegionEtaH theta h.eta0 Z
  let M := zeroFreeRegionRegularBoundH m h.M0 Z
  have hZtwo : 2 ≤ Z := by
    dsimp only [Z, zeroFreeRegionHeightHMax]
    have hpiT : 2 ≤ 8 * Real.pi * T := by
      nlinarith [Real.pi_gt_three]
    exact le_trans hpiT (le_max_left _ _)
  have hlogZ : 0 < Real.log (2 * Z) :=
    Real.log_pos (by nlinarith)
  have heta0 : 0 < eta := by
    dsimp only [eta, zeroFreeRegionEtaH]
    exact lt_min h.eta0_pos (Real.rpow_pos_of_pos hlogZ _)
  have hetaHalf : eta ≤ 1 / 2 := by
    exact le_trans (min_le_left _ _) h.eta0_le_half
  have hM0 : 0 ≤ M := by
    dsimp only [M, zeroFreeRegionRegularBoundH]
    exact le_trans (by linarith [h.one_le_M0] : 0 ≤ h.M0) (le_max_left _ _)
  have huZ : |u| ≤ Z / 2 := by
    dsimp only [Z, zeroFreeRegionHeightHMax]
    have hbase : 8 * Real.pi * T ≤
        max (8 * Real.pi * T)
          (Real.exp ((Real.log P) ^ (1 / (1 + theta)))) :=
      le_max_left _ _
    linarith
  exact hkernel S C P eta Z u M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP
    heta0 hetaHalf (by linarith) hM0 hu1 huZ (h.zero Z hZtwo) (h.reg Z hZtwo)

end MoltResearch
