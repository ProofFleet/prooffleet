import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2CoreExtras
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage4

/-!
# Track C regression examples: the frozen stage interface signatures compile

This file is **Conjectures-only** glue: compile-only `example` blocks pinning the *canonical*
downstream-facing lemmas listed in the "Stage interface signatures" section of
`Problems/tao2015_pipeline.md` (treat that list as frozen for consumers).

Each example consumes one canonical lemma by name — no `unfold`, no reaching into record
internals, no proof search — importing only the intended surfaces named on the card
(`TrackCStage2Core(+Extras)`, `TrackCStage3EntryMinimal`/`...EntryCore`, `TrackCStage4`).

If an example here breaks, a stage-boundary rename/behavior change leaked into the frozen
consumer surface; fix the boundary (or add a wrapper) and update the card, not just this file.
-/

namespace MoltResearch

namespace Tao2015

namespace StageSignatureExamples

variable [Stage2Assumption]

variable {f : ℕ → ℤ}

/-!
## Stage 2 (boundary record)
-/

-- Stage-2 core conclusion, by the canonical named lemma.
example (out : Stage2Output f) : ¬ BoundedDiscrepancy f :=
  out.notBoundedOriginal (f := f)

-- Stage-2 affine-tail witness family at the deterministic start index.
example (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) > B :=
  out.forall_exists_natAbs_apSumFrom_start_gt (f := f)

/-!
## Stage 3 (hard-gate consumer API)
-/

-- Stage-3 canonical surface statement.
example (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  stage3_notBounded f hf

-- Stage-3 pipeline-friendly existential packaging (`1 ≤ d` normal form).
example (hf : IsSignSequence f) : ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m :=
  stage3_exists_params_one_le_unboundedDiscOffset f hf

-- Stage-3 canonical witness normal form (`d ≥ 1`, positive-length witnesses).
example (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C :=
  stage3_forall_exists_d_ge_one_witness_pos f hf

/-!
## Stage 4 (boundary stub)
-/

-- Stage-4 canonical theorems, consumed through the thin entry point only.
example (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  stage4_notBounded f hf

example (hf : IsSignSequence f) : ∀ C : ℕ, HasDiscrepancyAtLeast f C :=
  stage4_forall_hasDiscrepancyAtLeast f hf

end StageSignatureExamples

end Tao2015

end MoltResearch
