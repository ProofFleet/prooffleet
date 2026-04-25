import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2CoreExtras

/-!
# Track C: Stage 3 entry point (hard-gate core)

This file is **Conjectures-only** glue.

- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` contains the minimal Stage-3
  API needed by the Track-C hard-gate target
  `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`.
- This file adds a small collection of pipeline-friendly witness forms and existential packaging
  lemmas, without pulling in the larger convenience layer `TrackCStage3Entry`.

Beyond the tiny definitional rewrites about `stage3Out` in the minimal module
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal`, all additional convenience
projections and rewrite lemmas (e.g. `stage3_d`, `stage3_g`, `stage3_start`, `stage3_g_eq`, ...)
live in `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Core Stage-3 pipeline witnesses

These are proved (non-stub) lemmas that are often useful when shuttling statements between
Stages 2 and 3, without importing the larger convenience layer
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`.
-/

/-!
Definitional rewrite simp lemmas for `stage3Out` live in the minimal module
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal`.
-/

/-- Track C pipeline witness: Stage 3 yields unbounded fixed-step discrepancy along the reduced
sequence, expressed using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

The lemma with the canonical name `stage3_unboundedDiscrepancyAlong_core` lives in the minimal
entry-point module `TrackCStage3EntryMinimal` (it uses the bundled projections `.g` and `.d`).

This lemma is the same statement, but written using the explicit Stage-1 reduction fields
`out1.g` and `out1.d`; it is occasionally convenient when shuttling between Stage-2 and Stage-3
records.
-/
theorem stage3_unboundedDiscrepancyAlong_core_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (stage3Out (f := f) (hf := hf)).out1.g
      (stage3Out (f := f) (hf := hf)).out1.d := by
  simpa using (stage3Out (f := f) (hf := hf)).unboundedDiscrepancyAlong_core

/-- Consumer-facing normal form: Stage 3 implies the reduced sequence is not bounded along its
fixed step size.

This is the boundedness-negation normal form of the Stage-2 unboundedness witness stored in
`stage3Out ...`.
-/
theorem stage3_notBoundedReducedAlong (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancyAlong
        (stage3Out (f := f) (hf := hf)).out2.g
        (stage3Out (f := f) (hf := hf)).out2.d := by
  let out := stage3Out (f := f) (hf := hf)
  -- Delegate to the core Stage-3 boundary API.
  simpa [out] using (Stage3Output.notBoundedReducedAlong (f := f) out)

/-!
`stage3_unboundedDiscOffset` is already defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` (the hard-gate minimal layer).

We re-export it here by importing the minimal module, avoiding a duplicate declaration.
-/

/-!
`stage3_not_exists_boundedDiscOffset` is already defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` (the hard-gate minimal layer).

We re-export it here by importing the minimal module, avoiding a duplicate declaration.
-/

/-- Consumer-facing normal form: there is no uniform bound on `discOffset f d m` at the
deterministic Stage-2 parameters stored in `stage3Out`.

Negation normal form:
`¬ ∃ B, ∀ n, discOffset f d m n ≤ B`.
-/
theorem stage3_not_exists_forall_discOffset_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          discOffset f
            (stage3Out (f := f) (hf := hf)).out2.d
            (stage3Out (f := f) (hf := hf)).out2.m n ≤ B := by
  let out := stage3Out (f := f) (hf := hf)
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := by
    simpa [out] using stage3_unboundedDiscOffset (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f)
        (d := out.out2.d) (m := out.out2.m)).1
      hunb

/-- Consumer-facing normal form: there is no uniform bound on the bundled offset nuclei
`Int.natAbs (apSumOffset f d m n)` at the deterministic Stage-2 parameters stored in `stage3Out`.

Negation normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumOffset f d m n) ≤ B`.
-/
theorem stage3_not_exists_forall_natAbs_apSumOffset_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              (apSumOffset f
                (stage3Out (f := f) (hf := hf)).out2.d
                (stage3Out (f := f) (hf := hf)).out2.m n) ≤ B := by
  let out := stage3Out (f := f) (hf := hf)
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := by
    simpa [out] using stage3_unboundedDiscOffset (f := f) (hf := hf)
  exact
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumOffset_le (f := f)
        (d := out.out2.d) (m := out.out2.m)).1
      hunb

-- Note: `stage3_not_exists_forall_natAbs_apSumFrom_start_le` now lives in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` so the hard-gate minimal
-- Stage-3 entry point exposes this tail-nucleus normal form without importing Stage-2 core extras.

/-- Paper-notation normal form: there is no uniform bound on the shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` at the deterministic Stage-2 parameters stored in `stage3Out`.

Negation normal form:
`¬ ∃ B, ∀ n, Int.natAbs ((Icc (m+1) (m+n)).sum (fun i => f (i*d))) ≤ B`.
-/
theorem stage3_not_exists_forall_natAbs_sum_Icc_offset_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              ((Finset.Icc ((stage3Out (f := f) (hf := hf)).out2.m + 1)
                ((stage3Out (f := f) (hf := hf)).out2.m + n)).sum
                (fun i => f (i * (stage3Out (f := f) (hf := hf)).out2.d))) ≤ B := by
  let out := stage3Out (f := f) (hf := hf)
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := by
    simpa [out] using stage3_unboundedDiscOffset (f := f) (hf := hf)
  have hnb :
      ¬ ∃ B : ℕ,
          ∀ n : ℕ,
            Int.natAbs ((Finset.Icc (out.out2.m + 1) (out.out2.m + n)).sum (fun i => f (i * out.out2.d))) ≤ B :=
    (UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le (f := f)
        (d := out.out2.d) (m := out.out2.m)).1
      hunb
  simpa [out] using hnb


/-!
`stage3_exists_params_one_le_unboundedDiscOffset` is defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` (the hard-gate minimal layer).

We re-export it here by importing the minimal module, avoiding a duplicate declaration.
-/

-- Note: `stage3_exists_params_one_le_not_exists_boundedDiscOffset` is defined in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` (imported above).


/-- Variant of `stage3_exists_params_one_le_unboundedDiscOffset` with strict positivity for `d`.

Normal form:
`∃ d m, d > 0 ∧ UnboundedDiscOffset f d m`.
-/
theorem stage3_exists_params_d_pos_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  rcases stage3_exists_params_one_le_unboundedDiscOffset (f := f) (hf := hf) with ⟨d, m, hd, hU⟩
  refine ⟨d, m, ?_, hU⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Variant of `stage3_exists_params_one_le_not_exists_boundedDiscOffset` with strict positivity for
`d`.

Normal form:
`∃ d m, d > 0 ∧ ¬ ∃ B, BoundedDiscOffset f d m B`.
-/
theorem stage3_exists_params_d_pos_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  rcases stage3_exists_params_one_le_not_exists_boundedDiscOffset (f := f) (hf := hf) with
    ⟨d, m, hd, h⟩
  refine ⟨d, m, lt_of_lt_of_le Nat.zero_lt_one hd, h⟩


/-- Stage 3 yields concrete parameters `d, m` (with `1 ≤ d`) such that the bundled offset
sequence nuclei `apSumOffset f d m n` take arbitrarily large absolute values, with positive-length
witnesses.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ B, ∃ n, n > 0 ∧ Int.natAbs (apSumOffset f d m n) > B`.

This is the most pipeline-friendly witness-family form for consuming the Stage-2 output without
importing the larger Stage-2 convenience-lemma layer.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f d m n) > B) := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.out2.d, out.out2.m, out.out2.one_le_d (f := f), ?_⟩
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.out2.unboundedDiscOffset (f := f)
  intro B
  simpa using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f)
        (d := out.out2.d) (m := out.out2.m) hunb)
      B

/-- Stage 3 yields concrete parameters `d, m` (with `1 ≤ d`) such that the affine-tail nuclei
`apSumFrom f (m*d) d n` take arbitrarily large absolute values.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ C, ∃ n, Int.natAbs (apSumFrom f (m*d) d n) > C`.

This is a pipeline-friendly normal form derived directly from the Stage-2 offset-unboundedness
witness.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.out2.d, out.out2.m, out.out2.one_le_d (f := f), ?_⟩
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.out2.unboundedDiscOffset (f := f)
  intro C
  rcases
      (UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
            (f := f) (d := out.out2.d) (m := out.out2.m) hunb)
          C with
    ⟨n, _hnpos, hgt⟩
  exact ⟨n, hgt⟩

/-- Positive-length witness variant of `stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt`.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ C, ∃ n, n > 0 ∧ Int.natAbs (apSumFrom f (m*d) d n) > C`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.out2.d, out.out2.m, out.out2.one_le_d (f := f), ?_⟩
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.out2.unboundedDiscOffset (f := f)
  intro C
  simpa using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
          (f := f) (d := out.out2.d) (m := out.out2.m) hunb)
      C

/-- Paper-notation variant of `stage3_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos`.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ B, ∃ n, n > 0 ∧ Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d)) > B`.

Implementation note: this is just
`stage3_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos` rewritten using
`Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  rcases stage3_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos
      (f := f) (hf := hf) with ⟨d, m, hd, h⟩
  refine ⟨d, m, hd, ?_⟩
  intro B
  rcases h B with ⟨n, hnpos, hn⟩
  refine ⟨n, hnpos, ?_⟩
  simpa [Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using hn

/-- Stage 3 yields concrete parameters `d, m` (with `1 ≤ d`) such that the bundled offset discrepancy
family `discOffset f d m n` takes arbitrarily large values, with positive-length witnesses.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ B, ∃ n, n > 0 ∧ discOffset f d m n > B`.

This is the most pipeline-friendly witness-family normal form for consuming the Stage-2 output
without importing the larger Stage-2 convenience-lemma layer.
-/
theorem stage3_exists_params_one_le_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ discOffset f d m n > B) := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.out2.d, out.out2.m, out.out2.one_le_d (f := f), ?_⟩
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.out2.unboundedDiscOffset (f := f)
  intro B
  simpa using
    (UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos (f := f)
        (d := out.out2.d) (m := out.out2.m) hunb)
      B

-- (moved to `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal`)


-- Note: the nucleus witness form `stage3_forall_exists_d_ge_one_witness_pos` lives in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal`.

/-- Discrepancy-form variant of `stage3_forall_exists_d_ge_one_witness_pos`.

Normal form:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C`.
-/
theorem stage3_forall_exists_discrepancy_gt_d_ge_one_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases stage3_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf) C with
    ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hw

/-- Alias for `stage3_forall_exists_discrepancy_gt_d_ge_one_witness_pos`.

This keeps the older name (with the same statement) available in the hard-gate core layer.
-/
theorem stage3_forall_exists_discrepancy_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C := by
  simpa using stage3_forall_exists_discrepancy_gt_d_ge_one_witness_pos (f := f) (hf := hf)

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

/-!
Note: `stage3_forall_exists_discrepancy_gt_witness_pos` is already defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal`.

We avoid re-declaring it here so that `TrackCStage3EntryCore` can be imported alongside the
minimal entry-point module without name clashes.
-/

-- (also available via `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`)

end Tao2015

end MoltResearch
