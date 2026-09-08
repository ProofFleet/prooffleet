import MoltResearch.Discrepancy.PrimeLargeValuesFromRegion

/-!
# Prime large values from height-indexed zero-free data

This leaf repairs the height mismatch in `ZeroFreeRegionData`.  The analytic
input is indexed by the actual contour height `Z`: both the zero-free width
and the regular-part bound are evaluated at that height.  The constants
`eta0` and `M0` cover the bounded-height range without imposing an artificial
half-strip there.
-/

namespace MoltResearch

open Complex ExpSums Finset
open scoped ContDiff

/-- Width of the height-indexed zero-free region. -/
noncomputable def zeroFreeRegionEtaH (theta eta0 Z : ℝ) : ℝ :=
  min eta0 ((Real.log (2 * Z)) ^ (-theta))

/-- Rectangle height used by the repaired Mellin shift. -/
noncomputable def zeroFreeRegionHeightH (T P : ℝ) : ℝ :=
  8 * Real.pi * T + Real.sqrt P

/-- Height-indexed bound for the regular part of `-zeta'/zeta`. -/
noncomputable def zeroFreeRegionRegularBoundH (m M0 Z : ℝ) : ℝ :=
  max M0 ((Real.log (2 * Z)) ^ m)

/-- Quantitative zero-free data indexed by the actual rectangle height.

The small-height constants are part of the data.  Thus an asymptotic
zero-free theorem only has to shrink `eta0` and enlarge `M0` once; it does not
have to assert a fixed half-strip at every bounded height. -/
structure ZeroFreeRegionDataH (theta m : ℝ) where
  theta_pos : 0 < theta
  eta0 : ℝ
  eta0_pos : 0 < eta0
  eta0_le_half : eta0 ≤ 1 / 2
  M0 : ℝ
  one_le_M0 : 1 ≤ M0
  zero : ∀ Z : ℝ, 2 ≤ Z → ∀ z : ℂ,
    1 - zeroFreeRegionEtaH theta eta0 Z ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ Z → z ≠ 1 → riemannZeta z ≠ 0
  reg : ∀ Z : ℝ, 2 ≤ Z → ∀ z : ℂ,
    1 - zeroFreeRegionEtaH theta eta0 Z ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ Z → z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          zeroFreeRegionRegularBoundH m M0 Z

set_option maxHeartbeats 800000

/-- **V-B′-2.**  The V-A kernel estimate at the repaired rectangle height
`8*pi*T + sqrt P`, with width and regular bound supplied by height-indexed
data. -/
theorem exists_primeMellin_kernel_bound_of_zeroFreeRegionDataH
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
      let Z := zeroFreeRegionHeightH T P
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
  let Z := zeroFreeRegionHeightH T P
  let eta := zeroFreeRegionEtaH theta h.eta0 Z
  let M := zeroFreeRegionRegularBoundH m h.M0 Z
  have hZtwo : 2 ≤ Z := by
    dsimp only [Z, zeroFreeRegionHeightH]
    have hsqrt : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
    nlinarith [Real.pi_gt_three]
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
    dsimp only [Z, zeroFreeRegionHeightH]
    nlinarith [Real.sqrt_nonneg P]
  exact hkernel S C P eta Z u M hSs hS01 hS0 hS1 hC0 hC1 hC2 hP
    heta0 hetaHalf (by linarith) hM0 hu1 huZ (h.zero Z hZtwo) (h.reg Z hZtwo)

end MoltResearch
