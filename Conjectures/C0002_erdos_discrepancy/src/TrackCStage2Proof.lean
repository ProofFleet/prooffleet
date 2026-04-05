import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file contains only the Stage-2 convenience projections/wrapper lemmas.

The Stage-2 conjecture stub (axiom) itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

Implementation note: we intentionally avoid importing the large Stage-2 convenience-lemma library
(`TrackCStage2Output.lean`).  The wrappers here are proved directly from the `Stage2Output` fields
plus the Stage-1 transport lemmas on `ReductionOutput`, and we only depend on the tiny proved core
lemmas in `TrackCStage2Core.lean`.
-/

namespace MoltResearch

namespace Tao2015

/-!
The Stage-2 conjecture stub (axiom) and the deterministic name `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

This file keeps only the convenience projections/wrapper lemmas.
-/

/-- Convenience projection: the reduced step size produced by Stage 2. -/
noncomputable abbrev stage2_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.d

/-- Convenience projection: the reduced sequence produced by Stage 2. -/
noncomputable abbrev stage2_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage2Out (f := f) (hf := hf)).out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 2. -/
noncomputable abbrev stage2_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.m

/-- The reduced sequence produced by Stage 2 is a sign sequence. -/
theorem stage2_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_g (f := f) (hf := hf)) := by
  simpa [stage2_g] using (stage2Out (f := f) (hf := hf)).out1.hg

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem stage2_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_g (f := f) (hf := hf) k =
      f (k + (stage2_m (f := f) (hf := hf)) * (stage2_d (f := f) (hf := hf))) := by
  simpa [stage2_g, stage2_m, stage2_d] using (stage2Out (f := f) (hf := hf)).out1.g_eq k

/-- Positivity of the reduced step size produced by Stage 2. -/
theorem stage2_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).out1.hd

/-- Convenience lemma: the reduced step size produced by Stage 2 is at least `1`. -/
theorem stage2_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage2_d (f := f) (hf := hf) := by
  simpa using (Nat.succ_le_iff).2 (stage2_hd (f := f) (hf := hf))

/-- Convenience lemma: the reduced step size produced by Stage 2 is nonzero. -/
theorem stage2_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_d (f := f) (hf := hf) ≠ 0 := by
  exact Nat.ne_of_gt (stage2_hd (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 already closes the core goal `¬ BoundedDiscrepancy f`.

This is a thin wrapper around the proved Stage-2 core lemma `Stage2Output.notBoundedOriginal`.
-/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact Stage2Output.notBoundedOriginal (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail nuclei
`apSumFrom f (m*d) d n` at the concrete parameters produced by the conjecture stub `stage2Out`.

We derive this directly from the Stage-1 transport equivalence on the bundled `ReductionOutput`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumFrom f
              (stage2_m (f := f) (hf := hf) * stage2_d (f := f) (hf := hf))
              (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2_m, stage2_d] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt
          (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Consumer-facing shortcut: Stage 2 yields an unbounded bundled offset discrepancy family
`discOffset f d m`, at the concrete parameters produced by the conjecture stub `stage2Out`.

This is a thin wrapper around the Stage-1 transport equivalence on the bundled `ReductionOutput`.
-/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) := by
  simpa [stage2_d, stage2_m] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-!
Consumer code should usually use `stage2Out` together with the general lemmas about `Stage2Output`
(from `TrackCStage2.lean` / `TrackCStage2Output.lean`).

We intentionally avoid duplicating wrapper lemmas here, so this file remains a pure conjecture stub
plus projections.
-/

end Tao2015

end MoltResearch
