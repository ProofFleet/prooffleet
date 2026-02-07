import Mathlib

/-!
A conjecture-style stub for the Erdős discrepancy theorem.

This file may contain `sorry` (backlog only). Verified, reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- A ±1-valued sequence on ℕ. -/
def IsSignSequence (f : ℕ → ℤ) : Prop := ∀ n, f n = 1 ∨ f n = -1

/-- Sum of `f` along the homogeneous arithmetic progression `d, 2d, ..., nd`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f ((i + 1) * d))

/-- `f` has discrepancy at least `C` if some AP partial sum exceeds `C` in absolute value. -/
def HasDiscrepancyAtLeast (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∃ d n : ℕ, Int.natAbs (apSum f d n) > C

/-- Erdős discrepancy theorem (Tao 2015).

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is a long-horizon target for the repo; we start by building the definition + lemma substrate.
-/
conjecture erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  sorry

end MoltResearch
