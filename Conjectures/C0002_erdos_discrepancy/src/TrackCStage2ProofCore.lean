import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 2 proof stub core (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains the minimal proved wrapper lemmas specialized to the deterministic Stage-2 output
`stage2Out`.

The larger collection of witness-form wrappers lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2ProofWitnesses`.

The Stage-2 conjecture stub (axiom) itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.
-/

namespace MoltResearch

namespace Tao2015

/-!
The Stage-2 conjecture stub (axiom) and the deterministic name `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

This file keeps only the core convenience wrappers.
-/

/-- Minimal consumer-facing Stage-2 consequence: the original sequence cannot have globally bounded
(discrepancy) once Stage 2 produces an unbounded fixed-step witness along the reduced sequence. -/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  simpa using
    (Stage2Output.notBoundedOriginal (f := f) (stage2Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `stage2_notBounded` via the global normal form lemma
`forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2
      (stage2_notBounded (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields unbounded discrepancy along the deterministic reduced
sequence `stage2_g` at the deterministic step size `stage2_d`.

This is just the `unbounded` field of `stage2Out`, rewritten to use the named projections.
-/
theorem stage2_unboundedDiscrepancyAlong (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) := by
  simpa [stage2_g, stage2_d] using (stage2Out (f := f) (hf := hf)).unbounded

/-- Minimal consumer-facing Stage-2 consequence: Stage 2 yields an unbounded bundled offset
discrepancy family `discOffset f d m` at the deterministic parameters produced by `stage2Out`. -/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) := by
  simpa [stage2_d, stage2_m] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Core-predicate form: Stage 2 yields unbounded fixed-step discrepancy along the reduced sequence,
re-expressed using `MoltResearch.UnboundedDiscrepancyAlong`.

This is a small convenience wrapper around the Track-C-local witness
`(stage2Out ...).unbounded`, using `Tao2015.unboundedDiscrepancyAlong_iff_core`.
-/
theorem stage2_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf))
      (stage2_d (f := f) (hf := hf)) := by
  exact
    (Tao2015.unboundedDiscrepancyAlong_iff_core (g := stage2_g (f := f) (hf := hf))
        (d := stage2_d (f := f) (hf := hf))).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `d > 0` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage2_unboundedDiscOffset`; some downstream stages prefer strict
positivity over `1 ≤ d`.
-/
theorem stage2_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine
    ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
      stage2_d_pos (f := f) (hf := hf), ?_⟩
  exact stage2_unboundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded. -/
theorem stage2_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine
    ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
      stage2_one_le_d (f := f) (hf := hf), ?_⟩
  exact stage2_unboundedDiscOffset (f := f) (hf := hf)

end Tao2015

end MoltResearch
