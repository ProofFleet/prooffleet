import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 3 entry point (hard-gate core)

This file is **Conjectures-only** glue.

It provides the minimal Stage-3 entry point API needed by the Track-C hard-gate target
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`:

- `stage3` / `stage3Out` : produce a `Stage3Output f` from a sign sequence `f`
- `stage3_notBounded` : close the core goal `¬ BoundedDiscrepancy f`
- `stage3_forall_hasDiscrepancyAtLeast` : the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`
- `stage3_exists_params_one_le_unboundedDiscOffset` : existential packaging of the concrete Stage-2 parameters
  `∃ d m, 1 ≤ d ∧ UnboundedDiscOffset f d m`
- `stage3_forall_exists_discrepancy_gt` : discrepancy witness form
  `∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`
- `stage3_forall_exists_discrepancy_gt_witness_pos` : discrepancy witness form with `n > 0`
  `∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ discrepancy f d n > C`
- `stage3_forall_exists_d_ge_one_witness_pos` : the pipeline-friendly nucleus witness normal form
  `∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`
- `stage3_forall_exists_d_pos_witness_pos` : nucleus witness form with `d > 0`
  `∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`
- `stage3_forall_exists_d_ne_zero_witness_pos` : nucleus witness form with `d ≠ 0`
  `∀ C, ∃ d n, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`
- `stage3_forall_exists_sum_Icc_witness_pos` : paper-notation witness form
  `∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`
- `stage3_forall_exists_sum_Icc_d_ge_one_witness_pos` : paper-notation witness form with `d ≥ 1`
  `∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`

All additional projections and rewrite lemmas (e.g. `stage3_d`, `stage3_g`, `stage3_start`,
`stage3_g_eq`, ...) live in `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`.
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

/-- The Stage-2 output stored inside `stage3Out` is definitionally the Stage-2 output produced by
Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 2 and Stage 3.

We keep it in the hard-gate core so consumers don't need to import the larger Stage-3 convenience
layer `TrackCStage3Entry` just to access this definitional rewrite.
-/
@[simp] theorem stage3Out_out2 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2 = stage2Out (f := f) (hf := hf) := by
  rfl

/-- The Stage-1 reduction output stored inside `stage3Out` is definitionally the Stage-1 reduction
output produced by Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 1 and Stage 3.

We keep it in the hard-gate core so consumers don't need to import the larger Stage-3 convenience
layer `TrackCStage3Entry` just to access this definitional rewrite.
-/
@[simp] theorem stage3Out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2.out1 = (stage2Out (f := f) (hf := hf)).out1 := by
  rfl

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

/-- Specialization of `stage3_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem stage3_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C

/-- Stage 3 yields concrete Stage-2 parameters `d, m` (with `1 ≤ d`) such that the bundled offset
discrepancy family `discOffset f d m` is unbounded.

This is a thin wrapper around `Stage2Output.unboundedDiscOffset` applied to `stage3Out`.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.out2.d, out.out2.m, out.out2.one_le_d (f := f), ?_⟩
  exact out.out2.unboundedDiscOffset (f := f)

/-- Consumer-facing shortcut: Stage 3 yields the discrepancy witness form

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is obtained from `stage3_forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem stage3_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      ((stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C)

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 3 without importing the
larger Stage-3 output-lemma layer.
-/
theorem stage3_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Variant of `stage3_forall_exists_d_ge_one_witness_pos` with strict positivity for `d`.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.
-/
theorem stage3_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage3_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Variant of `stage3_forall_exists_d_pos_witness_pos` with the step-size condition written as
`d ≠ 0`.

Normal form:
`∀ C, ∃ d n, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.
-/
theorem stage3_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage3_forall_exists_d_pos_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  exact ⟨d, n, Nat.ne_of_gt hd, hn, hw⟩

/-- Consumer-facing shortcut: Stage 3 yields the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `stage3_forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem stage3_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Variant of `stage3_forall_exists_sum_Icc_witness_pos` writing the step-size side condition as
`d ≥ 1`.

This is often the most readable paper-notation witness form when `d : ℕ`.
-/
theorem stage3_forall_exists_sum_Icc_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos f).1
      (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Strengthened variant of `stage3_forall_exists_discrepancy_gt` with a positive-length witness.

Since `discrepancy f d 0 = 0`, any witness with `discrepancy f d n > C` can be taken with `n > 0`.
-/
theorem stage3_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases stage3_forall_exists_d_pos_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hw

-- (moved to `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`)

end Tao2015

end MoltResearch
