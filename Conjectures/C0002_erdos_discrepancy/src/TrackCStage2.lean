import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Track C: Stage 2 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue: it introduces a *named stage boundary* for the Tao 2015
Erdős discrepancy proof pipeline.

Design goals:
- Keep the interface small and typed (IO contract, not a pile of lemmas).
- Avoid lemma sprawl: downstream work should prove theorems *about this boundary*, rather than
  repeatedly re-stating the same intermediate reductions.

No statements here are intended for the verified substrate (`MoltResearch/`).
-/

namespace MoltResearch

namespace Tao2015

/-!
Stage 1 (`ReductionOutput`) packages a shift reduction from the original sign sequence `f` to an
auxiliary sign sequence `g` together with a step size `d`.

Stage 2 (this file) is the next boundary we want to populate: from the Stage-1 reduced sequence,
produce a fixed-step *unboundedness witness form* (`UnboundedDiscrepancyAlong`).

The point of naming this as a record is so later stages can consume it without depending on the
exact internal path used to obtain unboundedness.
-/

/-- Output of Stage 2 of the Track C pipeline.

This is intentionally minimal:
- we keep the full Stage-1 `ReductionOutput` so later stages have access to `g`, `d`, `m`, and the
  bridge contracts;
- we expose the Stage-2 result as *unbounded discrepancy along the fixed step* `d`.

Downstream stages should treat `out1.g` (at step `out1.d`) as the canonical fixed-step locus.
-/
structure Stage2Output (f : ℕ → ℤ) : Type where
  out1 : Tao2015.ReductionOutput f
  unbounded : Tao2015.UnboundedDiscrepancyAlong out1.g out1.d

namespace Stage2Output

variable {f : ℕ → ℤ}

/-- Convenience projection: the reduced step size. -/
abbrev d (out : Stage2Output f) : ℕ := out.out1.d

/-- Convenience projection: the reduced sequence. -/
abbrev g (out : Stage2Output f) : ℕ → ℤ := out.out1.g

/-- Unboundedness of the reduced sequence in explicit witness form (`B < discrepancy ...`). -/
theorem forall_exists_discrepancy_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  -- This is just the definitional witness form for `UnboundedDiscrepancyAlong`.
  simpa [Tao2015.UnboundedDiscrepancyAlong] using out.unbounded

/-- Equivalent packaging: arbitrarily large discrepancy witnesses along `out.d`. -/
theorem forall_hasDiscrepancyAtLeastAlong (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- Use the lemma in `Tao2015` that relates `∀ C, HasDiscrepancyAtLeastAlong` to unboundedness.
  have : (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      Tao2015.UnboundedDiscrepancyAlong out.g out.d :=
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong
      (g := out.g) (d := out.d))
  exact (this.2 out.unbounded)

/-- Stage 2 implies the reduced sequence is not bounded along its fixed step size. -/
theorem notBoundedReducedAlong (out : Stage2Output f) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.UnboundedDiscrepancyAlong.iff_not_boundedDiscrepancyAlong
    (g := out.g) (d := out.d)).1 out.unbounded

/-- Consumer-facing form: Stage 2 unboundedness transferred back to the original sequence as an
unbounded **offset discrepancy** witness.

This is just a wrapper around
`Tao2015.ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt`.

Note the inequality direction: this produces witnesses of the form `B < discOffset ...`.
-/
theorem forall_exists_discOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.out1.d out.out1.m n := by
  -- Unfold the Stage-2 witness form and transport it through the Stage-1 contract.
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)).1 out.unbounded)

/-- Stage 2 implies *unbounded offset discrepancy* for the original sequence, at the bundled
parameters `(out.out1.d, out.out1.m)`.

This is the packaged predicate version of `forall_exists_discOffset_gt`.
-/
theorem unboundedDiscOffset (out : Stage2Output f) :
    Tao2015.UnboundedDiscOffset f out.out1.d out.out1.m := by
  -- `UnboundedDiscOffset` is defined using the witness form `∀ B, ∃ n, B < discOffset ...`.
  simpa [Tao2015.UnboundedDiscOffset] using out.forall_exists_discOffset_gt (f := f)

/-- Backwards-compatible alias for `forall_exists_discOffset_gt`.

Deprecated because the suffix `_lt` was misleading: the statement is `B < ...` (i.e. “greater than B”).
-/
@[deprecated "Use `forall_exists_discOffset_gt` (the statement is `B < discOffset ...`)." (since := "2026-03-08")]
theorem forall_exists_discOffset_lt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.out1.d out.out1.m n := by
  simpa using out.forall_exists_discOffset_gt (f := f)

/-- Sum-level variant of `forall_exists_discOffset_gt`.

This is occasionally the right normal form for later analytic stages: it exposes the raw nucleus
`apSumOffset` rather than the wrapper `discOffset`.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.out1.d out.out1.m n) := by
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_lt (f := f)).1
      out.unbounded)

/-- Backwards-compatible alias for `forall_exists_natAbs_apSumOffset_gt`.

Deprecated because the suffix `_lt` was misleading: the statement is `B < ...`.
-/
@[deprecated "Use `forall_exists_natAbs_apSumOffset_gt` (the statement is `B < Int.natAbs ...`)." (since := "2026-03-08")]
theorem forall_exists_natAbs_apSumOffset_lt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.out1.d out.out1.m n) := by
  simpa using out.forall_exists_natAbs_apSumOffset_gt (f := f)

/-- Consumer-facing form: Stage 2 implies global unbounded discrepancy for the original sequence.

This is the minimal “bridge back to the main theorem statement” lemma: it packages the fact that
Stage 2 gives an explicit unbounded offset-discrepancy family for `f`, and then uses the Stage-1
contract carried by `out.out1` to conclude `¬ BoundedDiscrepancy f`.
-/
theorem notBoundedOriginal (out : Stage2Output f) : ¬ BoundedDiscrepancy f := by
  -- Stage 2 → explicit offset unboundedness witness.
  have hunb : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.out1.d out.out1.m n :=
    out.forall_exists_discOffset_gt (f := f)
  -- Stage 1 contract transfers unboundedness back to `f`.
  exact out.out1.not_boundedDiscrepancy_of_forall_exists_discOffset_gt (f := f) hunb

end Stage2Output

/-!
## Stage 2 conjecture stub

This is the first *nontrivial* boundary after `ReductionOutput`: it should encapsulate whatever
Tao-style argument (Fourier-analytic / entropy decrement / pretentiousness machinery) yields a
fixed-step unboundedness witness.

We keep it as a single named theorem so future refactors do not leak intermediate lemmas into the
public surface.
-/

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, produce a Stage-1 reduction output and show that the reduced sequence
has unbounded discrepancy along its associated fixed step.

This is an axiom stub for now; it serves as the typed seam between Stage 1 (pure index gymnastics) and
later analytic/combinatorial stages.
-/
axiom stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f

end Tao2015

end MoltResearch
