import MoltResearch.Discrepancy

/-!
# Tao 2015: Erdős discrepancy theorem (proof skeleton)

This module is **Conjectures-only**: it may contain `sorry`.

Goal: turn the Tao 2015 proof into an explicit chain of named intermediate lemmas so we can
fill it in incrementally, while keeping the main theorem statement in
`Conjectures/C0002_erdos_discrepancy/src/ErdosDiscrepancy.lean` a clean composition.

Nothing in this file should be imported from `MoltResearch/` (verified substrate).
-/

namespace MoltResearch

/-!
## High-level plan (names match future lemma stubs)

Tao’s proof is nontrivial; the point of this skeleton is to make the *shape* of the argument
machine-checkable even before we have the details.

We target the boundedness normal form:

`¬ BoundedDiscrepancy f`

where `BoundedDiscrepancy f := ∃ B, ∀ d n, d>0 → |apSum f d n| ≤ B`.

The eventual development will likely introduce auxiliary notions (log-averages, multiplicative
models, etc.) in `Conjectures/` first, and only move stable definitions to `MoltResearch/` once
we’re confident they are reusable.
-/

/-- (Stub) A key reduction step in Tao 2015.

In a future development, this lemma will express the first major simplification/reduction of
an assumed bounded-discrepancy counterexample into a more structured object.

For now it is only a placeholder to make the proof outline explicit.
-/
theorem tao2015_reduction_step (f : ℕ → ℤ) (hf : IsSignSequence f)
    (hb : BoundedDiscrepancy f) : True := by
  sorry

/-- (Stub) A key analytic/combinatorial contradiction step in Tao 2015.

Given the structured object produced by `tao2015_reduction_step`, the proof eventually derives
an explicit contradiction.

This lemma is a placeholder for that second stage.
-/
theorem tao2015_contradiction_step (f : ℕ → ℤ) (hf : IsSignSequence f)
    (hb : BoundedDiscrepancy f) : False := by
  sorry

/-- Tao 2015: Erdős discrepancy, packaged as a “not bounded discrepancy” statement.

This is the mathematically substantial part and remains a conjecture stub in this repo.

The body is written as a proof skeleton (reduction step(s) + contradiction step(s)) so we can
refine it iteratively.
-/
theorem tao2015_not_boundedDiscrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  intro hb
  have _ : True := tao2015_reduction_step (f := f) (hf := hf) (hb := hb)
  exact tao2015_contradiction_step (f := f) (hf := hf) (hb := hb)

end MoltResearch
