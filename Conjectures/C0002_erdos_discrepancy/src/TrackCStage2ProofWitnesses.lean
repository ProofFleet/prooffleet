import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2ProofCore

/-!
# Track C: Stage 2 witness wrappers (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains additional witness-form convenience lemmas specialized to the deterministic Stage-2
output `stage2Out`.

These wrappers are intentionally kept out of `TrackCStage2ProofCore` so that lightweight imports
can depend on the Stage-2 core API without pulling in all witness normal forms.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Additional witness-form wrappers
-/

/-- Consumer-facing shortcut: Stage 2 yields the most pipeline-friendly global witness form:

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around `stage2_forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (stage2_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Variant of `stage2_forall_exists_d_ge_one_witness_pos` with the step-size condition written as
`d > 0`. -/
theorem stage2_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage2_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Variant of `stage2_forall_exists_d_pos_witness_pos` with the step-size condition written as
`d ≠ 0`. -/
theorem stage2_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage2_forall_exists_d_pos_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  exact ⟨d, n, Nat.ne_of_gt hd, hn, hw⟩

/-- Consumer-facing discrepancy witness form derived from Stage 2.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is obtained from `stage2_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem stage2_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      (stage2_hasDiscrepancyAtLeast (f := f) (hf := hf) C)

/-!
## Witnesses for the deterministic reduced locus

Stage 2 packages fixed-step unboundedness along the reduced sequence `stage2_g` at the reduced
step size `stage2_d`.

These two wrappers expose that field in the common inequality-direction normal forms.
-/

/-- Inequality-direction witness form of `stage2_unboundedDiscrepancyAlong`.

Normal form:
`∀ B, ∃ n, discrepancy (stage2_g f) (stage2_d f) n > B`.
-/
theorem stage2_forall_exists_reduced_discrepancy_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        discrepancy (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n > B := by
  have hunb :
      UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) :=
    stage2_unboundedDiscrepancyAlong (f := f) (hf := hf)
  exact
    (unboundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt'
        (g := stage2_g (f := f) (hf := hf)) (d := stage2_d (f := f) (hf := hf))).1
      hunb

/-- Positive-length witness form of `stage2_forall_exists_reduced_discrepancy_gt'`.

Since `discrepancy ... 0 = 0`, any witness for `discrepancy ... n > B` must have `n > 0`.
-/
theorem stage2_forall_exists_reduced_discrepancy_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧
          discrepancy (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n > B := by
  have hunb :
      UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) :=
    stage2_unboundedDiscrepancyAlong (f := f) (hf := hf)
  exact
    UnboundedDiscrepancyAlong.forall_exists_discrepancy_gt'_witness_pos
      (g := stage2_g (f := f) (hf := hf)) (d := stage2_d (f := f) (hf := hf)) hunb

/-- Consumer-facing tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail nuclei
`apSumFrom f (m*d) d n` at the concrete parameters produced by the conjecture stub `stage2Out`.

We derive this directly from the Stage-1 transport equivalence
`ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2_start, stage2_m, stage2_d] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt
        (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Negation-normal-form tail-nucleus statement: Stage 2 yields no uniform bound on the affine-tail
nuclei `Int.natAbs (apSumFrom f (m*d) d n)` at the concrete parameters produced by `stage2Out`.

This is often the most convenient form for contradiction arguments in later stages.
-/
theorem stage2_not_exists_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) ≤ B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_start, stage2_d, stage2_m] using
    (UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le (f := f)
        (d := stage2_d (f := f) (hf := hf))
        (m := stage2_m (f := f) (hf := hf))).1
      hunb

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumFrom_mul_gt`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.

This is a thin wrapper around the Conjectures-only normal-form lemma
`forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) > C := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_start, stage2_d, stage2_m] using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      hunb)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ C, ∃ n, Int.natAbs (apSumFrom f (m*d) d n) > C`.

This is a thin wrapper around `stage2_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage2_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
    stage2_one_le_d (f := f) (hf := hf), ?_⟩
  intro C
  simpa [stage2_start, stage2_m, stage2_d] using
    stage2_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (hf := hf) C

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values, with a
positive-length witness `n > 0`.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ C, ∃ n, n > 0 ∧ Int.natAbs (apSumFrom f (m*d) d n) > C`.

This is a thin wrapper around `stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
    stage2_one_le_d (f := f) (hf := hf), ?_⟩
  intro C
  simpa [stage2_start, stage2_m, stage2_d] using
    stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) (hf := hf) C

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`.

Normal form:
`∀ B, ∃ n, B < discOffset f d m n`,
where `d = stage2_d` and `m = stage2_m`.

This is definitionally just `stage2_unboundedDiscOffset`.
-/
theorem stage2_forall_exists_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        B < discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n := by
  exact stage2_unboundedDiscOffset (f := f) (hf := hf)

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`.

Normal form:
`∀ B, ∃ n, discOffset f d m n > B`,
where `d = stage2_d` and `m = stage2_m`.
-/
theorem stage2_forall_exists_discOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  intro B
  rcases stage2_forall_exists_discOffset_gt (f := f) (hf := hf) B with ⟨n, hn⟩
  exact ⟨n, (gt_iff_lt).2 hn⟩

/-- Negation-normal form: Stage 2 yields no uniform bound on the offset-nucleus `discOffset` at the
concrete parameters produced by the conjecture stub `stage2Out`.
-/
theorem stage2_not_exists_forall_discOffset_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n ≤ B := by
  have hunb :
      UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  -- Use the Track-C normal form lemma instead of duplicating the contradiction proof.
  exact
    (unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f)
        (d := stage2_d (f := f) (hf := hf))
        (m := stage2_m (f := f) (hf := hf))).1
      hunb

/-- Positive-length witness form of `stage2_forall_exists_discOffset_gt'`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧ discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  exact
    UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      hunb

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`, stated using the bundled offset nucleus.

Normal form:
`∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`,
where `d = stage2_d` and `m = stage2_m`.

This is a thin wrapper around the normal-form lemma
`iff_forall_exists_natAbs_apSumOffset_gt'`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_d, stage2_m] using
    (UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt' (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))).1
      hunb

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumOffset_gt'`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_d, stage2_m] using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      hunb)

/-- Paper-notation witness form: Stage 2 yields arbitrarily large shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` at the concrete parameters produced by the conjecture stub
`stage2Out`.

Normal form:
`∀ B, ∃ n, Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d)) > B`,
where `d = stage2_d` and `m = stage2_m`.

This is `stage2_forall_exists_natAbs_apSumOffset_gt'` rewritten using
`natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem stage2_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            ((Finset.Icc (stage2_m (f := f) (hf := hf) + 1) (stage2_m (f := f) (hf := hf) + n)).sum
              (fun i => f (i * stage2_d (f := f) (hf := hf)))) > B := by
  intro B
  rcases stage2_forall_exists_natAbs_apSumOffset_gt' (f := f) (hf := hf) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite `apSumOffset` into paper notation.
  simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      (n := n)] using
    hn

/-- Positive-length witness form of `stage2_forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem stage2_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            ((Finset.Icc (stage2_m (f := f) (hf := hf) + 1) (stage2_m (f := f) (hf := hf) + n)).sum
              (fun i => f (i * stage2_d (f := f) (hf := hf)))) > B := by
  intro B
  rcases stage2_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f := f) (hf := hf) B with
    ⟨n, hnpos, hn⟩
  refine ⟨n, hnpos, ?_⟩
  -- Rewrite `apSumOffset` into paper notation.
  simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      (n := n)] using
    hn

/-!
Consumer code should usually use `stage2Out` together with the general lemmas about `Stage2Output`
(from `TrackCStage2.lean` / `TrackCStage2Output.lean`).

We intentionally keep the proofs here as thin wrappers around Stage-1 transport contracts and
generic normal-form lemmas, specialized to the deterministic parameters coming from `stage2Out`.
-/

end Tao2015

end MoltResearch
