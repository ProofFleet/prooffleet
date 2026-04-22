import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 conjecture stub (Tao 2015 plane)

This file is **Conjectures-only** glue.

It isolates the single non-verified assumption of Track C: the Stage-2 boundary axiom.

Design goal: downstream hard-gate consumers (Stage 3, `ErdosDiscrepancy.lean`) should only need to
import this stub to access `stage2Out`, avoiding compilation of additional Stage-2 convenience
lemmas.
-/

namespace MoltResearch

namespace Tao2015

/-- Typeclass packaging of the Stage-2 conjecture assumption.

We package the conjecture as a `Prop` (existence of a Stage-2 output) rather than committing to a
specific function. The definitional output `stage2`/`stage2Out` is then selected noncomputably via
`Classical.choice`.

This lets downstream code replace the axiom stub by providing a local instance (e.g. derived from a
verified Stage-2 construction).
-/
class Stage2Assumption : Prop where
  /-- Stage 2 of Tao 2015: given a sign sequence `f`, a Stage-2 output exists consisting of a
  Stage-1 reduction output and an unbounded fixed-step discrepancy witness along the reduced
  sequence. -/
  stage2_nonempty (f : ℕ → ℤ) (hf : IsSignSequence f) : Nonempty (Stage2Output f)

/-- Non-typeclass entry point: run Stage 2 using an explicit `Stage2Assumption` proof.

This is useful in downstream developments that want to avoid `letI` / typeclass search and pass a
verified Stage-2 assumption explicitly.
-/
noncomputable def stage2Of (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage2Output f := by
  classical
  -- Use the explicit assumption directly, avoiding typeclass search.
  exact Classical.choice (inst.stage2_nonempty (f := f) (hf := hf))

/-- Abbreviation wrapper for `stage2Of` (mirrors `stage2Out`). -/
noncomputable abbrev stage2OutOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage2Output f :=
  stage2Of inst (f := f) (hf := hf)

/-- Default axiom instance for the Stage-2 assumption (Conjectures-only stub).

Design note: we register this instance at very low priority so that downstream developments can
provide a verified `Stage2Assumption` instance that will be preferred by typeclass search.
-/
axiom instStage2Assumption : Stage2Assumption
-- Low-priority default: downstream developments can provide a verified instance that typeclass
-- search will prefer (larger priorities are tried first).
attribute [instance 10] instStage2Assumption

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, choose a Stage-2 output using `Classical.choice` from the existence
statement packaged by `Stage2Assumption`.
-/
noncomputable def stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] : Stage2Output f :=
  Classical.choice (Stage2Assumption.stage2_nonempty (f := f) (hf := hf))

/-- Deterministic name for the Stage-2 output (useful to keep later statements readable). -/
noncomputable abbrev stage2Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f :=
  stage2 (f := f) (hf := hf)

end Tao2015

end MoltResearch
