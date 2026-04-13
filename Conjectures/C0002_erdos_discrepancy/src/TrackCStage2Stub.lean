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

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, produce a Stage-2 output consisting of a Stage-1 reduction output and an
unbounded fixed-step discrepancy witness along the reduced sequence.
-/
axiom stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f

/-- Deterministic name for the Stage-2 output (useful to keep later statements readable). -/
noncomputable abbrev stage2Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f :=
  stage2 (f := f) (hf := hf)

end Tao2015

end MoltResearch
