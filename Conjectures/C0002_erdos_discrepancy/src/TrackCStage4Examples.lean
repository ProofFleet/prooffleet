import Conjectures.C0002_erdos_discrepancy.src.TrackCStage4

/-!
# Track C regression examples: Stage 4 consumes Stage 3 without unfolding

This file is **Conjectures-only** glue: compile-only `example` blocks checking that Stage 4 can
be built from, and can pass through, the Stage-3 boundary using **named lemmas only** — no
`unfold`, no reaching into `.out3`/`.out2` internals, no proof search.

It deliberately imports only the thin entry point
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage4`, so it also acts as a regression test
that the entry point re-exports everything a downstream consumer needs.

If an example here breaks, a Stage-3 or Stage-4 boundary rename/behavior change leaked out;
fix the boundary (or add a wrapper), not this file.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage4Examples

variable [Stage2Assumption]

variable {f : ℕ → ℤ}

/-!
## Constructing Stage 4 from Stage 3

Stage 4 is wiring: any Stage-3 output yields a Stage-4 output, and the Stage-3 conclusions are
available at the Stage-4 boundary by name.
-/

-- Stage 4 is constructible from an arbitrary Stage-3 output (no side conditions).
example (out3 : Tao2015.Stage3Output f) : Stage4Output f :=
  ⟨out3⟩

-- The Stage-3 core conclusion survives the boundary crossing, via named lemmas only.
example (out3 : Tao2015.Stage3Output f) : ¬ BoundedDiscrepancy f :=
  (Stage4Output.mk out3).notBounded

-- End-to-end through the hard gate: Stage-3 entry (`stage3Out`) → Stage 4 → surface statement.
example (hf : IsSignSequence f) : ∀ C : ℕ, HasDiscrepancyAtLeast f C :=
  stage4_forall_hasDiscrepancyAtLeast f hf

-- The Stage-3 output carried by `stage4Out` is the Stage-3 hard-gate output, by the named
-- simp lemma (not by unfolding `stage4`).
example (hf : IsSignSequence f) :
    (stage4Out (f := f) (hf := hf)).out3 = Tao2015.stage3Out (f := f) (hf := hf) :=
  stage4Out_out3 f hf

/-!
## Consuming Stage 4 downstream

A downstream stage should be able to take `out : Stage4Output f` and obtain the canonical
witness normal forms with a single named lemma each.
-/

-- Concrete-parameter offset unboundedness at the Stage-4 projections `out.d`, `out.m`.
example (out : Stage4Output f) : UnboundedDiscOffset f out.d out.m :=
  out.unboundedDiscOffset (f := f)

-- Existential packaging (`1 ≤ d` normal form), as later stages prefer to consume it.
example (out : Stage4Output f) : ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m :=
  out.exists_params_one_le_unboundedDiscOffset (f := f)

-- Nucleus witness normal form (`d ≥ 1`, positive-length witnesses).
example (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C :=
  out.forall_exists_d_ge_one_witness_pos (f := f)

-- Paper-notation witness normal form at the consumer-facing shortcut level.
example (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C :=
  stage4_forall_exists_sum_Icc_d_ge_one_witness_pos f hf

-- Stage-4 parameter projections agree definitionally with the carried Stage-2 parameters,
-- so no rewriting is needed to line up later-stage statements.
example (out : Stage4Output f) : out.d = out.out3.out2.d :=
  rfl

end Stage4Examples

end Tao2015

end MoltResearch
