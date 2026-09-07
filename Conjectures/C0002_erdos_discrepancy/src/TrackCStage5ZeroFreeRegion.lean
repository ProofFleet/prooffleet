import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LargeValuesDischarge
import MoltResearch.Discrepancy.ZeroFreeRegionData

/-!
# Track R: EDP from quantitative zero-free-region data

This is the Conjectures-layer bridge from the analytic nucleus to the
`PrimeLargeValuesAssumption` interface.  It is deliberately a theorem, not a
global instance: callers choose the zero-free input explicitly.

The standard Vinogradov--Korobov bookkeeping uses
`theta = 31/40 = 3/4 + 1/40`, which is strictly below the consumer exponent
`4/5`; every fixed real logarithmic loss `m` is allowed.  The elementary
two-region absorption is represented by `ZeroFreeRegionData.envelope`.
-/

namespace MoltResearch

namespace Tao2015

/-- Quantitative nonvanishing and regular-part bounds for zeta produce the
prime-supported large-values interface. -/
theorem primeLargeValues_of_zeroFreeRegion {m : ℝ}
    (h : ZeroFreeRegionData (31 / 40) m) : PrimeLargeValuesAssumption := by
  obtain ⟨C, hC, hb⟩ := prime_large_values_bound_of_zeroFreeRegionData h
  refine ⟨⟨C, hC, ?_⟩⟩
  intro P Y hYprime hYrange a T 𝒯 hP hT hrange hsep
  have hs := hb P Y hYprime hYrange a T 𝒯 hP hT hrange hsep
  unfold primeLargeValuesDecay at hs
  unfold primeLargeValuesExponent
  convert hs using 1 <;> ring

/-- **Track R endpoint.**  EDP follows from the zero-free-region data alone;
the prime large-values instance exists only locally in this proof. -/
theorem trackR_edp_of_zeroFreeRegion {m : ℝ}
    (h : ZeroFreeRegionData (31 / 40) m)
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  letI : PrimeLargeValuesAssumption := primeLargeValues_of_zeroFreeRegion h
  exact trackR_edp_halasz f hf

end Tao2015

end MoltResearch
