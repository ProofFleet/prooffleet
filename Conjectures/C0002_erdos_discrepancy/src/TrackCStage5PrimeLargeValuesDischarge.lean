import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ZetaGrowth
import MoltResearch.Discrepancy.ZetaGrowthVinogradov

/-!
# Track R: unconditional prime large values and EDP

This leaf composes the proved Vinogradov zeta-growth estimate with the
height-indexed V-C4 zero-free-region interface.  For `a = 33/25`, the
zero-free exponent has the strict margin
`31/40 - (25/33 + 1/100) = 47/6600`.
-/

namespace MoltResearch

namespace Tao2015

/-- Existence form of the V-C4 height-indexed zero-free data supplied by the
Vinogradov growth bound. -/
theorem nonempty_zeroFreeRegionData_from_vinogradov : Nonempty
    (ZeroFreeRegionDataH
      (1 / (33 / 25 : ℝ) + 1 / 100)
      (1 / (33 / 25 : ℝ) + 1 / 10)) := by
  obtain ⟨t₀, B, B₀, _ht₀, _hB, hgrowth⟩ :=
    ExpSums.exists_zetaGrowthBound_vinogradov
  exact ExpSums.nonempty_zeroFreeRegionDataH_of_growth hgrowth (by norm_num)

/-- The chosen V-C4 height-indexed zero-free data. -/
noncomputable def zeroFreeRegionData_from_vinogradov :
    ZeroFreeRegionDataH
      (1 / (33 / 25 : ℝ) + 1 / 100)
      (1 / (33 / 25 : ℝ) + 1 / 10) :=
  Classical.choice nonempty_zeroFreeRegionData_from_vinogradov

/-- The exact exponent margin used by the three-regime consumer. -/
theorem vinogradov_growth_theta_lt :
    1 / (33 / 25 : ℝ) + 1 / 100 < 31 / 40 := by
  norm_num

/-- The unconditional prime-supported large-values input obtained from the
Vinogradov zero-free region. -/
noncomputable instance primeLargeValuesAssumption_vinogradov :
    PrimeLargeValuesAssumption :=
  primeLargeValues_of_zeroFreeRegionH zeroFreeRegionData_from_vinogradov
    vinogradov_growth_theta_lt (by norm_num)

/-- The Erdos discrepancy theorem with no analytic hypothesis classes. -/
theorem erdos_discrepancy_unconditional (f : ℕ → ℤ)
    (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact trackR_edp_halasz f hf

#print axioms zeroFreeRegionData_from_vinogradov
#print axioms primeLargeValuesAssumption_vinogradov
#print axioms erdos_discrepancy_unconditional

end Tao2015

end MoltResearch
