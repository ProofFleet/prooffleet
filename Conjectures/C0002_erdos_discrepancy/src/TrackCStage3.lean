import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 3 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue.

Stage 2 produces a fixed-step unboundedness witness for the reduced sequence `g` (at step `d`),
plus a transport lemma back to an *offset discrepancy* witness for the original sequence `f`.

Stage 3 is the boundary where we finally discharge the global goal `¬ BoundedDiscrepancy f`.

Design goal: keep the hard-gate surface small.

Most convenience lemmas about `Stage3Output` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output`.
-/

namespace MoltResearch

namespace Tao2015

/-- Output of Stage 3 of the Track C pipeline.

We keep the full Stage-2 output for traceability. The global conclusion
`¬ BoundedDiscrepancy f` is derived (as `Stage3Output.notBounded`) from the Stage-2 boundary.
-/
structure Stage3Output (f : ℕ → ℤ) : Type where
  out2 : Tao2015.Stage2Output f

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Convenience projection: Stage 3 carries the full Stage-2 output, hence also carries the
underlying Stage-1 reduction output.

This is occasionally useful when later stages want access to the deterministic parameters
`g, d, m` and the Stage-1 transport contracts, without reaching through multiple record fields.
-/
@[simp] abbrev out1 (out : Stage3Output f) : Tao2015.ReductionOutput f :=
  out.out2.out1

/-- Stage 3 already closes the global goal `¬ BoundedDiscrepancy f`.

We intentionally do not store this as a field: it is derived from the Stage-2 output.

Implementation note: we delegate to the tiny Stage-2 core bridge lemma `Stage2Output.notBoundedOriginal`.
-/
theorem notBounded (out : Stage3Output f) : ¬ BoundedDiscrepancy f := by
  exact out.out2.notBoundedOriginal (f := f)

/-- Stage 3 output also exposes the Stage-2 offset-discrepancy witness predicate.

This is a thin wrapper around the Stage-2 core lemma `Stage2Output.unboundedDiscOffset`.
-/
theorem unboundedDiscOffset (out : Stage3Output f) :
    UnboundedDiscOffset f out.out2.d out.out2.m := by
  exact out.out2.unboundedDiscOffset (f := f)

/-- Stage 3 output implies there is no bundled offset bound at the deterministic Stage-2 parameters.

This is the stable boundedness-negation normal form of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage3Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.out2.d out.out2.m B := by
  exact out.out2.not_exists_boundedDiscOffset (f := f)

/-- Deterministic Stage-3 completion: a Stage-2 output already contains enough information to
contradict any global boundedness hypothesis.

This is the main “stage boundary” lemma: it is *proved* (no `sorry`) and should remain stable.
-/
def ofStage2Output (out2 : Tao2015.Stage2Output f) : Stage3Output f :=
  ⟨out2⟩

/-- Stage 3 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

We keep this lemma in the hard-gate module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage3Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBounded (f := f)

/-- Specialization of `forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem hasDiscrepancyAtLeast (out : Stage3Output f) (C : ℕ) : HasDiscrepancyAtLeast f C := by
  exact (out.forall_hasDiscrepancyAtLeast (f := f)) C

end Stage3Output

/-!
## Stage 3 entry point

The Stage-3 entry point `stage3` (a definition, not an axiom) lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore` (re-exported by
`...TrackCStage3Entry`) so that this file remains purely “API + wiring”.
-/

end Tao2015

end MoltResearch
