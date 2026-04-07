import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 3 core lemmas (Tao 2015 plane)

This file is intentionally tiny.

It contains the minimal proved projections/lemmas about `Tao2015.Stage3Output` needed by
later stages, without importing the large Stage-3 output-lemma library
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output`.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Alias for the packaged global conclusion, matching Stage-2 naming.

Stage 2 calls this statement `Stage2Output.notBoundedOriginal`; Stage 3 exposes it as the method
`out.notBounded` (derived from the Stage-2 output). This alias lets downstream code use a
consistent name at both boundaries.
-/
abbrev notBoundedOriginal (out : Stage3Output f) : ¬ BoundedDiscrepancy f :=
  out.notBounded

/-- Convenience projection: the reduced step size packaged in Stage 3.

We intentionally route this through the Stage-2 boundary API (`Stage2Output.d`) so Stage 3 does not
depend on Stage-1 record fields.
-/
abbrev d (out : Stage3Output f) : ℕ := out.out2.d

/-- Convenience projection: the reduced sequence packaged in Stage 3.

We intentionally route this through the Stage-2 boundary API (`Stage2Output.g`) so Stage 3 does not
depend on Stage-1 record fields.
-/
abbrev g (out : Stage3Output f) : ℕ → ℤ := out.out2.g

/-- The reduced sequence packaged in Stage 3 is a sign sequence. -/
theorem hg (out : Stage3Output f) : IsSignSequence out.g := by
  simpa [Stage3Output.g] using (Stage2Output.hg (f := f) out.out2)

/-- Stage 3 retains the Stage-2 reduced-step unboundedness witness.

This is a tiny convenience projection so consumers of `Stage3Output` do not have to reach into the
nested Stage-2 record field `out.out2.unbounded`.
-/
abbrev unboundedReducedAlong (out : Stage3Output f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d :=
  out.out2.unbounded

/-- Equivalent packaging: arbitrarily large reduced-sequence discrepancy witnesses along `out.d`.

This is the `HasDiscrepancyAtLeastAlong` normal form of `unboundedReducedAlong`.
-/
theorem forall_hasDiscrepancyAtLeastAlong (out : Stage3Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- `UnboundedDiscrepancyAlong` is definitionally `∀ C, HasDiscrepancyAtLeastAlong ... C`.
  simpa [Tao2015.UnboundedDiscrepancyAlong, HasDiscrepancyAtLeastAlong, Stage3Output.g,
    Stage3Output.d] using out.out2.unbounded

/-- Convenience projection: the bundled offset parameter packaged in Stage 3. -/
abbrev m (out : Stage3Output f) : ℕ := out.out2.m

/-- Rewrite for the reduced sequence packaged in Stage 3: it is a shift by `m*d`. -/
theorem g_eq (out : Stage3Output f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [Stage3Output.g, Stage3Output.m, Stage3Output.d] using
    (Stage2Output.g_eq (f := f) out.out2 k)

/-- Convenience projection: positivity of the reduced step size. -/
abbrev hd (out : Stage3Output f) : out.d > 0 := out.out2.hd

/-- Convenience lemma: the reduced step size is nonzero.

We intentionally delegate this to the Stage-2 boundary API lemma (`Stage2Output.d_ne_zero`), so
Stage 3 doesn't re-prove arithmetic facts about its projections.
-/
theorem d_ne_zero (out : Stage3Output f) : out.d ≠ 0 := by
  simpa [Stage3Output.d] using (Stage2Output.d_ne_zero (f := f) out.out2)

/-- Convenience lemma: the reduced step size is at least `1`.

We intentionally delegate this to the Stage-2 boundary API lemma (`Stage2Output.one_le_d`).
-/
theorem one_le_d (out : Stage3Output f) : 1 ≤ out.d := by
  simpa [Stage3Output.d] using (Stage2Output.one_le_d (f := f) out.out2)

end Stage3Output

end Tao2015

end MoltResearch
