import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LargeValuesDischarge
import MoltResearch.Discrepancy.PrimeLargeValuesThreeRegime

/-!
# Track R: EDP from height-indexed zero-free-region data

This leaf connects the three-regime analytic theorem to the stable
`PrimeLargeValuesAssumption` interface.  The record exponent is first compared
with `31/40`; the consumer exponent `4/5` supplies the remaining strict slack.
-/

namespace MoltResearch

namespace Tao2015

/-- Height-indexed zero-free data with exponent below `31/40` and regular-part
loss at most `log²` supplies the prime large-values interface. -/
theorem primeLargeValues_of_zeroFreeRegionH {theta m : ℝ}
    (h : ZeroFreeRegionDataH theta m) (htheta : theta < 31 / 40)
    (hm : m ≤ 2) : PrimeLargeValuesAssumption := by
  have hgap : theta < (4 / 5 : ℝ) := lt_trans htheta (by norm_num)
  obtain ⟨C, hC, hb⟩ :=
    prime_large_values_bound_of_zeroFreeRegionDataH' h hgap (by norm_num) hm
  refine ⟨⟨C, hC, ?_⟩⟩
  intro P Y hYprime hYrange a T 𝒯 hP hT hrange hsep
  have hs := hb P Y hYprime hYrange a T 𝒯 hP hT hrange hsep
  unfold primeLargeValuesDecay at hs
  unfold primeLargeValuesExponent
  convert hs using 1 <;> ring

/-- **Track R endpoint.** EDP follows from height-indexed zero-free data; the
large-values instance is local to the proof. -/
theorem trackR_edp_of_zeroFreeRegionH {theta m : ℝ}
    (h : ZeroFreeRegionDataH theta m) (htheta : theta < 31 / 40)
    (hm : m ≤ 2) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  letI : PrimeLargeValuesAssumption :=
    primeLargeValues_of_zeroFreeRegionH h htheta hm
  exact trackR_edp_halasz f hf

#print axioms primeLargeValues_of_zeroFreeRegionH
#print axioms trackR_edp_of_zeroFreeRegionH

end Tao2015

end MoltResearch
