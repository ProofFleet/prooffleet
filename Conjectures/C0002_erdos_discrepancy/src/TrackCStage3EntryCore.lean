import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

/-!
# Track C: Stage 3 entry point (hard-gate core)

This file is **Conjectures-only** glue.

It provides the minimal Stage-3 entry point API needed by the Track-C hard-gate target
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`:

- `stage3` / `stage3Out` : produce a `Stage3Output f` from a sign sequence `f`
- lightweight projections `stage3_d`, `stage3_g`, `stage3_m`
- the consumer-facing outputs `stage3_notBounded` and `stage3_forall_hasDiscrepancyAtLeast`

All additional Stage-3 convenience lemmas (witness forms, offset packaging, rewrite lemmas, etc.)
remain in `TrackCStage3Entry.lean` and `TrackCStage3Proof.lean`.
-/

namespace MoltResearch

namespace Tao2015

/-- Conjectures-only Stage 3 entry point: run Stage 2, then close the global goal via the proved
Stage-3 boundary lemma `Stage3Output.ofStage2Output`.

This is a definition (not an axiom): Stage 3 is non-stub glue on top of the Stage-2 axiom.
-/
noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  Stage3Output.ofStage2Output (f := f) (stage2Out (f := f) (hf := hf))

/-- Deterministic name for the Stage-3 output (useful to keep later statements readable). -/
noncomputable abbrev stage3Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  stage3 (f := f) (hf := hf)

/-- Convenience projection: the reduced step size produced by Stage 3. -/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_d (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is positive. -/
theorem stage3_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) > 0 := by
  simpa [stage3_d] using (stage2_d_pos (f := f) (hf := hf))

/-- Convenience lemma: the reduced step size produced by Stage 3 is nonzero. -/
theorem stage3_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) ≠ 0 := by
  exact Nat.ne_of_gt (stage3_d_pos (f := f) (hf := hf))

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  stage2_g (f := f) (hf := hf)

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_m (f := f) (hf := hf)

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the hard-gate core so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage3Out (f := f) (hf := hf)).notBounded

/-- Consumer-facing shortcut: the Stage-3 pipeline yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage3_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact Stage3Output.forall_hasDiscrepancyAtLeast (f := f) (stage3Out (f := f) (hf := hf))

/-- Consumer-facing witness form: Stage 3 yields

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This stays in the hard-gate core because it is a tiny wrapper around
`stage3_forall_hasDiscrepancyAtLeast` via `HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem stage3_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      ((stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C)

/-- Sharpened witness form: Stage 3 yields side conditions `d ≥ 1` and `n > 0`.

Normal form:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C`.

This is a tiny wrapper around `stage3_forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one_witness_pos`.
-/
theorem stage3_forall_exists_discrepancy_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one_witness_pos (f := f) (C := C)).1
      ((stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C)

end Tao2015

end MoltResearch
