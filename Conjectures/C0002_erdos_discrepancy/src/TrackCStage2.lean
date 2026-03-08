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

This is `sorry` for now; it serves as the typed seam between Stage 1 (pure index gymnastics) and
later analytic/combinatorial stages.
-/
theorem stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f := by
  classical
  -- TODO(Track C): fill in Tao 2015’s first major reduction producing fixed-step unboundedness.
  -- For now we expose the contract as a named boundary.
  refine
    { out1 := Tao2015.ReductionOutput.ofShift (f := f) (hf := hf) (d := 1) (m := 0) (hd := by decide)
      unbounded := ?_ }
  -- Placeholder: the actual proof will replace this `sorry`.
  sorry

end Tao2015

end MoltResearch
