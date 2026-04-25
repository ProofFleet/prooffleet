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
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub`.
-/

namespace MoltResearch

namespace Tao2015

/-!
The Stage-2 conjecture stub (axiom) and the deterministic name `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub`.

This file keeps only the core convenience wrappers.
-/

/-- Minimal consumer-facing Stage-2 consequence: the original sequence cannot have globally bounded
(discrepancy) once Stage 2 produces an unbounded fixed-step witness along the reduced sequence. -/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  simpa using
    (Stage2Output.notBoundedOriginal (f := f) (stage2Out (f := f) (hf := hf)))

/-!
## Explicit-assumption variants

These are the non-typeclass analogues of the deterministic wrappers above, phrased in terms of the
explicit Stage-2 output constructor `stage2OutOf`.

They are useful when downstream developments want to run the Track-C pipeline under a verified
Stage-2 assumption without introducing a local typeclass instance via `letI`.
-/

/-- Explicit-assumption variant of `stage2_notBounded`. -/
theorem stage2OutOf_notBounded (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  simpa using
    (Stage2Output.notBoundedOriginal (f := f) (stage2OutOf inst (f := f) (hf := hf)))

/-- Explicit-assumption variant of `stage2_forall_hasDiscrepancyAtLeast`. -/
theorem stage2OutOf_forall_hasDiscrepancyAtLeast (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2OutOf inst (f := f) (hf := hf)))

/-- Explicit-assumption specialization of `stage2OutOf_forall_hasDiscrepancyAtLeast` at `C`. -/
theorem stage2OutOf_hasDiscrepancyAtLeast (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage2Output.hasDiscrepancyAtLeast (f := f) (stage2OutOf inst (f := f) (hf := hf)) C)

/-- Explicit-assumption variant of `stage2_unboundedDiscOffset`. -/
theorem stage2OutOf_unboundedDiscOffset (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    UnboundedDiscOffset f
      (stage2OutOf inst (f := f) (hf := hf)).d
      (stage2OutOf inst (f := f) (hf := hf)).m := by
  let out := stage2OutOf inst (f := f) (hf := hf)
  simpa [out] using (Stage2Output.unboundedDiscOffset (f := f) out)

/-- Explicit-assumption normal form: there is no uniform bound on the bundled offset discrepancy
family `discOffset f out.d out.m`, at the concrete parameters produced by `stage2OutOf`. -/
theorem stage2OutOf_not_exists_boundedDiscOffset (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (stage2OutOf inst (f := f) (hf := hf)).d
        (stage2OutOf inst (f := f) (hf := hf)).m B := by
  simpa using
    (Stage2Output.not_exists_boundedDiscOffset (f := f) (stage2OutOf inst (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

Design note: route this through the proved Stage-2 core API
`Stage2Output.forall_hasDiscrepancyAtLeast`, keeping this wrapper layer thin.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2Out (f := f) (hf := hf)))

/-- Specialization of `stage2_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem stage2_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage2Output.hasDiscrepancyAtLeast (f := f) (stage2Out (f := f) (hf := hf)) C)

/-- Consumer-facing shortcut: Stage 2 yields unbounded discrepancy along the deterministic reduced
sequence `stage2_g` at the deterministic step size `stage2_d`.

This is just the `unbounded` field of `stage2Out`, rewritten to use the named projections.
-/
theorem stage2_unboundedDiscrepancyAlong (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) := by
  simpa [stage2_g, stage2_d] using (stage2Out (f := f) (hf := hf)).unbounded

/-- Consumer-facing normal form: Stage 2 implies the reduced sequence is not bounded along its
fixed step size.

This is the boundedness-negation normal form of `stage2_unboundedDiscrepancyAlong`.
-/
theorem stage2_notBoundedReducedAlong (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancyAlong
        (stage2_g (f := f) (hf := hf))
        (stage2_d (f := f) (hf := hf)) := by
  -- Delegate to the proved Stage-2 core boundary API.
  simpa [stage2_g, stage2_d, Stage2Output.g, Stage2Output.d] using
    (Stage2Output.notBoundedReducedAlong (out := stage2Out (f := f) (hf := hf)))

/-- Minimal consumer-facing Stage-2 consequence: Stage 2 yields an unbounded bundled offset
discrepancy family `discOffset f d m` at the deterministic parameters produced by `stage2Out`.

Design note: route this through the small, proved Stage-2 core API (`Stage2Output.unboundedDiscOffset`)
rather than re-proving the transport step here.
-/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) := by
  simpa [stage2_d, stage2_m, Stage2Output.d, Stage2Output.m] using
    (Stage2Output.unboundedDiscOffset (f := f) (stage2Out (f := f) (hf := hf)))

/-- Consumer-facing normal form: there is no bound `B` with
`BoundedDiscOffset f (stage2_d ...) (stage2_m ...) B`.

This is the stable boundedness-negation normal form of `stage2_unboundedDiscOffset`.
-/
theorem stage2_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (stage2_d (f := f) (hf := hf))
        (stage2_m (f := f) (hf := hf)) B := by
  simpa [stage2_d, stage2_m, Stage2Output.d, Stage2Output.m] using
    (Stage2Output.not_exists_boundedDiscOffset (f := f) (stage2Out (f := f) (hf := hf)))

/-- Core-predicate form: Stage 2 yields unbounded fixed-step discrepancy along the reduced sequence,
re-expressed using `MoltResearch.UnboundedDiscrepancyAlong`.

Design note: we route this through the proved Stage-2 core API
`Stage2Output.unboundedDiscrepancyAlong_core` (in `TrackCStage2Core`) so that this file stays a
thin wrapper layer.
-/
theorem stage2_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf))
      (stage2_d (f := f) (hf := hf)) := by
  simpa [stage2_g, stage2_d, Stage2Output.g, Stage2Output.d] using
    (Stage2Output.unboundedDiscrepancyAlong_core (f := f) (stage2Out (f := f) (hf := hf)))

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

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `d > 0` such that there is
no bundled offset bound at those parameters.

Normal form:
`∃ d m, d > 0 ∧ ¬ ∃ B, BoundedDiscOffset f d m B`.

This is a strict-positivity variant of `stage2_exists_params_one_le_not_exists_boundedDiscOffset`.
-/
theorem stage2_exists_params_d_pos_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  refine
    ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
      stage2_d_pos (f := f) (hf := hf), ?_⟩
  exact stage2_not_exists_boundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that there is
no bundled offset bound at those parameters.

Normal form:
`∃ d m, 1 ≤ d ∧ ¬ ∃ B, BoundedDiscOffset f d m B`.

This is a minimal-entry convenience lemma for downstream stages that prefer to work with an
existential parameter packaging, without mentioning the deterministic projections
`stage2_d/stage2_m`.
-/
theorem stage2_exists_params_one_le_not_exists_boundedDiscOffset (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  refine
    ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
      stage2_one_le_d (f := f) (hf := hf), ?_⟩
  exact stage2_not_exists_boundedDiscOffset (f := f) (hf := hf)

end Tao2015

end MoltResearch
