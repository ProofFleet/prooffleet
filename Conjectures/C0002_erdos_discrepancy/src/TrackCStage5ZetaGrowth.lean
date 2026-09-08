import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ZeroFreeRegionH
import MoltResearch.Discrepancy.ZetaGrowthDataH
namespace MoltResearch
namespace Tao2015

/-- A zeta growth bound with exponent at least `33/25` supplies the stable
prime-supported large-values interface. -/
theorem primeLargeValues_of_zetaGrowth
    {t₀ a B b B₀ : ℝ} (h : ExpSums.ZetaGrowthBound t₀ a B b B₀)
    (ha : 33 / 25 ≤ a) : PrimeLargeValuesAssumption := by
  have hrecip : 1 / a ≤ (25 / 33 : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 33 / 25) ha
    norm_num at hh ⊢
    exact hh
  have htheta : 1 / a + 1 / 100 < (31 / 40 : ℝ) := by
    nlinarith
  have hm : 1 / a + 1 / 10 ≤ (2 : ℝ) := by
    nlinarith
  exact primeLargeValues_of_zeroFreeRegionH
    (ExpSums.zeroFreeRegionDataH_of_growth h ha) htheta hm

/-- Track R endpoint from zeta growth. -/
theorem trackR_edp_of_zetaGrowth
    {t₀ a B b B₀ : ℝ} (h : ExpSums.ZetaGrowthBound t₀ a B b B₀)
    (ha : 33 / 25 ≤ a) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  letI : PrimeLargeValuesAssumption := primeLargeValues_of_zetaGrowth h ha
  exact trackR_edp_halasz f hf

#print axioms primeLargeValues_of_zetaGrowth
#print axioms trackR_edp_of_zetaGrowth

end Tao2015

end MoltResearch
