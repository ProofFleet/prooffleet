import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file is **Conjectures-only**: it may rely on axiom stubs (notably the Stage-2 stub). Verified,
reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- Trivial base case: any sign sequence has discrepancy at least 0. -/
theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  exact IsSignSequence.hasDiscrepancyAtLeast_zero (hf := hf)

-- Tao 2015 proof skeleton lives in `Conjectures.C0002_erdos_discrepancy.src.Tao2015`.

/-- Erdős discrepancy theorem in boundedness-negation normal form.

This is the core Track C output: it is the minimal statement from which the usual witness forms
follow.
-/
theorem erdos_discrepancy_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  -- Delegate to the minimal Stage-3 entry-point API.
  exact Tao2015.stage3_notBounded (f := f) (hf := hf)

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is the usual surface statement `∀ C, HasDiscrepancyAtLeast f C` derived from the core
Track-C output `¬ BoundedDiscrepancy f`.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Delegate to the minimal Stage-3 entry-point API.
  exact Tao2015.stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)

/-!
Additional witness-form corollaries live in
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancyWitnesses`.

We keep this file minimal so the Track-C hard-gate build can compile quickly.
-/

end MoltResearch
