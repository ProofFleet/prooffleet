import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file houses the Stage-2 conjecture/axiom stub.

Keeping the stub separate lets `TrackCStage2.lean` remain mostly “API + wiring”, while the
non-verified analytic content stays isolated behind a dedicated import.
-/

namespace MoltResearch

namespace Tao2015

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, produce a Stage-1 reduction output and show that the reduced sequence
has unbounded discrepancy along its associated fixed step.

This is an axiom stub for now; it serves as the typed seam between Stage 1 (pure index gymnastics)
and later analytic/combinatorial stages.
-/
axiom stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f

end Tao2015

end MoltResearch
