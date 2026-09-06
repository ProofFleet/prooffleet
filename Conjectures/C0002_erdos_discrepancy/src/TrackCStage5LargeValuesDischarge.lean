import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Final
import MoltResearch.Discrepancy.HalaszMontgomeryLargeValues

/-!
# Track C: the integer large-values interface, discharged

The in-tree Halász–Montgomery theorem supplies the integer-supported
large-values instance.  Consequently the Track R endpoint now retains only
the genuinely prime-supported large-values interface.
-/

namespace MoltResearch

namespace Tao2015

/-- The integer-supported large-values interface is unconditional. -/
instance : HalaszLargeValuesAssumption := ⟨halaszMontgomery_large_values⟩

/-- The Track R discrepancy endpoint after discharging the integer-supported
Halász large-values input. -/
theorem trackR_edp_halasz [PrimeLargeValuesAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  trackR_edp f hf

end Tao2015

end MoltResearch
