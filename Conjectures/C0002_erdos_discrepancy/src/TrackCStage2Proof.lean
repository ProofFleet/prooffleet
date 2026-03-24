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

/-- Stage 2 yields some concrete parameters `d, m` such that the bundled offset discrepancy family
`discOffset f d m` is unbounded.

This existential packaging is often more convenient for later analytic stages than working
directly with the stage record fields.
-/
theorem stage2_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  simpa using
    (Stage2Output.exists_params_unboundedDiscOffset (f := f) (stage2 (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 2 already yields the global conclusion `¬ BoundedDiscrepancy f`.

This is a thin wrapper around the proved lemma `Stage2Output.notBoundedOriginal`.
-/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact Stage2Output.notBoundedOriginal (f := f) (stage2 (f := f) (hf := hf))

end Tao2015

end MoltResearch
