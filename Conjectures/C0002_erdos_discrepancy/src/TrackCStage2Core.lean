import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 core lemmas (Tao 2015 plane)

This file is intentionally tiny.

It contains the minimal proved lemmas about `Tao2015.Stage2Output` needed by later hard-gate stages
to close the global goal `¬ BoundedDiscrepancy f` and to expose the small Stage-2 API used by the
Stage-3 hard-gate entry point.

Additional arithmetic/rewrite helpers (e.g. the start index `m*d`, reduced-sequence rewrite lemmas,
and tail-nucleus normal forms phrased using `out.start`) live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2CoreExtras`.

The larger collection of witness-form wrappers lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output`.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage2Output

variable {f : ℕ → ℤ}

/-!
## Stage-2 minimal projections

These are small, proved projections off `Tao2015.Stage2Output` that downstream hard-gate stages use
frequently.
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

/-- Convenience projection: positivity of the reduced step size. -/
abbrev hd (out : Stage2Output f) : out.d > 0 := out.out1.hd

/-- Convenience lemma: the reduced step size is nonzero. -/
theorem d_ne_zero (out : Stage2Output f) : out.d ≠ 0 := by
  exact Nat.ne_of_gt out.hd

/-- Convenience lemma: the reduced step size is at least `1`. -/
theorem one_le_d (out : Stage2Output f) : 1 ≤ out.d := by
  simpa using (Nat.succ_le_iff).2 out.hd

/-!
## Stage-2 bridge back to the global statement
-/

/-- Consumer-facing form: Stage 2 implies global unbounded discrepancy for the original sequence.

This is the minimal “bridge back to the main theorem statement” lemma: it packages the fact that
Stage 2 gives unbounded discrepancy along the reduced sequence, and uses the Stage-1 contract
carried by `out.out1` to conclude `¬ BoundedDiscrepancy f`.
-/
theorem notBoundedOriginal (out : Stage2Output f) : ¬ BoundedDiscrepancy f := by
  exact out.out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f) out.unbounded

/-- Stage 2 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `notBoundedOriginal`.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBoundedOriginal (f := f)

/-- Specialization of `forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem hasDiscrepancyAtLeast (out : Stage2Output f) (C : ℕ) : HasDiscrepancyAtLeast f C := by
  exact (out.forall_hasDiscrepancyAtLeast (f := f)) C

/-!
## Offset-discrepancy normal forms used by Stage 3
-/

/-- Stage 2 output implies unbounded bundled offset discrepancy for the original sequence
at the concrete parameters `out.d` and `out.m`.

This is the Stage-1 transport contract applied to the fixed-step unboundedness witness
`out.unbounded`.
-/
theorem unboundedDiscOffset (out : Stage2Output f) : UnboundedDiscOffset f out.d out.m := by
  simpa [Stage2Output.d, Stage2Output.m] using
    ((out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f))).1 out.unbounded

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset discrepancies
`discOffset f out.d out.m n`, with witnesses `n > 0`.

This is a thin wrapper around
`Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos`.
-/
theorem forall_exists_discOffset_gt'_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ discOffset f out.d out.m n > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos
      (f := f) (d := out.d) (m := out.m) hunb)

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset discrepancies
`discOffset f out.d out.m n`, with witnesses `n > 0`.

This is `forall_exists_discOffset_gt'_witness_pos` rewritten using `gt_iff_lt`.
-/
theorem forall_exists_discOffset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ B < discOffset f out.d out.m n := by
  intro B
  rcases out.forall_exists_discOffset_gt'_witness_pos (f := f) B with ⟨n, hnpos, hn⟩
  exact ⟨n, hnpos, (gt_iff_lt).1 hn⟩

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset nuclei
`Int.natAbs (apSumOffset f out.d out.m n)`, with witnesses `n > 0`.

This is a thin wrapper around
`Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos`.
-/
theorem forall_exists_natAbs_apSumOffset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f out.d out.m n) > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos
      (f := f) (d := out.d) (m := out.m) hunb)

/-- Stage 2 implies there is no uniform bound on the bundled offset discrepancy family
`discOffset f out.d out.m`.

This is the negation-normal-form version of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage2Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.d out.m B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f)
        (d := out.d) (m := out.m)).1
      hunb

/-!
## Core-predicate bridge
-/

/-- Stage-2 unboundedness, re-expressed using the verified core predicate.

This is a small convenience lemma: many consumers outside the `Tao2015` namespace use the core
predicate `MoltResearch.UnboundedDiscrepancyAlong` rather than the Track-C-local definition.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage2Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.unboundedDiscrepancyAlong_iff_core (g := out.g) (d := out.d)).1 out.unbounded

end Stage2Output

end Tao2015

end MoltResearch
