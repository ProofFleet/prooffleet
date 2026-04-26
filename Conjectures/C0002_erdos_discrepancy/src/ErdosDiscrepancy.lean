import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file is **Conjectures-only**: it may rely on axiom stubs (notably the Stage-2 stub). Verified,
reusable definitions belong in `MoltResearch/`.

Design goal: keep this module as small as possible so the Track‑C hard‑gate build compiles quickly.
Witness-form corollaries and additional packaging live in
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancyWitnesses`.
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

/-- Bridge lemma: the usual “unbounded discrepancy” surface statement is equivalent to negating the
boundedness predicate `BoundedDiscrepancy`.

This equivalence lives in the verified core as
`forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy`, but we restate it here so consumers of
this hard‑gate module can access it without hunting imports.
-/
theorem erdos_discrepancy_forall_hasDiscrepancyAtLeast_iff_notBounded (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ ¬ BoundedDiscrepancy f := by
  exact forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f

/-- Convenience direction of `erdos_discrepancy_forall_hasDiscrepancyAtLeast_iff_notBounded`.

This avoids rewriting with `.2` at the call site.
-/
theorem erdos_discrepancy_of_notBounded (f : ℕ → ℤ) (hnb : ¬ BoundedDiscrepancy f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact (erdos_discrepancy_forall_hasDiscrepancyAtLeast_iff_notBounded (f := f)).2 hnb

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is the usual surface statement `∀ C, HasDiscrepancyAtLeast f C` derived from the core
Track-C output `¬ BoundedDiscrepancy f`.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Convert from the core Track-C output `¬ BoundedDiscrepancy f`.
  have hnb : ¬ BoundedDiscrepancy f :=
    erdos_discrepancy_notBounded (f := f) (hf := hf)
  exact erdos_discrepancy_of_notBounded (f := f) hnb

/-- Specialization of `erdos_discrepancy` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem erdos_discrepancy_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (erdos_discrepancy (f := f) (hf := hf)) C

end MoltResearch
