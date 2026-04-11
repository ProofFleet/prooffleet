import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 core lemmas (Tao 2015 plane)

This file is intentionally tiny.

It contains the minimal proved lemmas about `Tao2015.Stage2Output` needed by later stages to
close the global goal `¬ BoundedDiscrepancy f`.

Design note: Track C's hard-gate build for
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`
should not need to compile the full library of Stage-2 convenience lemmas.

Additional witness-form wrappers live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output`.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage2Output

variable {f : ℕ → ℤ}

/-!
## Stage-2 minimal projections

These are the small, proved projections off `Tao2015.Stage2Output` that downstream stages use
frequently.

We keep them in this core file so consumers can avoid importing the much larger library of
Stage-2 convenience lemmas in `TrackCStage2Output.lean`.
-/

/-- Convenience projection: the reduced step size. -/
abbrev d (out : Stage2Output f) : ℕ := out.out1.d

/-- Convenience projection: the reduced sequence. -/
abbrev g (out : Stage2Output f) : ℕ → ℤ := out.out1.g

/-- The reduced sequence packaged by Stage 2 is a sign sequence. -/
theorem hg (out : Stage2Output f) : IsSignSequence out.g := by
  simpa [Stage2Output.g] using out.out1.hg

/-- Convenience projection: the offset parameter bundled in Stage 1. -/
abbrev m (out : Stage2Output f) : ℕ := out.out1.m

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1. -/
abbrev start (out : Stage2Output f) : ℕ := out.m * out.d

/-- The affine-tail start index `out.start` is a multiple of the reduced step size `out.d`. -/
theorem d_dvd_start (out : Stage2Output f) : out.d ∣ out.start := by
  -- `out.start` is definitionally `m*d`.
  simpa [Stage2Output.start] using (Nat.dvd_mul_left out.d out.m)

/-- The affine-tail start index `out.start` has remainder `0` when reduced modulo `out.d`.

This is often the most convenient form of `d_dvd_start` for arithmetic rewriting.
-/
theorem start_mod_d (out : Stage2Output f) : out.start % out.d = 0 := by
  exact Nat.mod_eq_zero_of_dvd (d_dvd_start (f := f) out)

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem g_eq (out : Stage2Output f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [Stage2Output.g, Stage2Output.m, Stage2Output.d] using out.out1.g_eq k

/-- Rewrite for the reduced sequence produced by Stage 2, phrased using the bundled start index
`out.start = out.m * out.d`. -/
theorem g_eq_start (out : Stage2Output f) (k : ℕ) :
    out.g k = f (k + out.start) := by
  simpa [Stage2Output.start] using (out.g_eq (f := f) k)

/-- Function-level rewrite for the reduced sequence produced by Stage 2: it is the shifted sequence
`fun k => f (k + out.start)`.
-/
theorem g_eq_fun (out : Stage2Output f) :
    out.g = fun k => f (k + out.start) := by
  funext k
  simpa using out.g_eq_start (f := f) k

/-- Convenience projection: positivity of the reduced step size. -/
abbrev hd (out : Stage2Output f) : out.d > 0 := out.out1.hd

/-- Convenience lemma: the reduced step size is nonzero. -/
theorem d_ne_zero (out : Stage2Output f) : out.d ≠ 0 := by
  exact Nat.ne_of_gt out.hd

/-- Convenience lemma: the reduced step size is at least `1`. -/
theorem one_le_d (out : Stage2Output f) : 1 ≤ out.d := by
  -- `out.hd` is `0 < out.d`.
  simpa using (Nat.succ_le_iff).2 out.hd

/-- Consumer-facing form: Stage 2 implies global unbounded discrepancy for the original sequence.

This is the minimal “bridge back to the main theorem statement” lemma: it packages the fact that
Stage 2 gives unbounded discrepancy along the reduced sequence, and uses the Stage-1 contract
carried by `out.out1` to conclude `¬ BoundedDiscrepancy f`.
-/
theorem notBoundedOriginal (out : Stage2Output f) : ¬ BoundedDiscrepancy f := by
  exact out.out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f) out.unbounded

/-- Stage 2 output implies unbounded bundled offset discrepancy for the original sequence
at the concrete parameters `out.d` and `out.m`.

This is the Stage-1 transport contract applied to the fixed-step unboundedness witness
`out.unbounded`.
-/
theorem unboundedDiscOffset (out : Stage2Output f) : UnboundedDiscOffset f out.d out.m := by
  simpa [Stage2Output.d, Stage2Output.m] using
    ((out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f))).1 out.unbounded

/-- Stage 2 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `notBoundedOriginal`.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBoundedOriginal (f := f)

/-- Stage-2 unboundedness, re-expressed using the verified core predicate.

This is a small convenience lemma: many consumers outside the `Tao2015` namespace use the core
predicate `MoltResearch.UnboundedDiscrepancyAlong` rather than the Track-C-local definition.

We keep this lemma in `TrackCStage2Core.lean` so downstream stages can access it without importing
the larger convenience-lemma library `TrackCStage2Output.lean`.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage2Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.unboundedDiscrepancyAlong_iff_core (g := out.g) (d := out.d)).1 out.unbounded

end Stage2Output

end Tao2015

end MoltResearch
