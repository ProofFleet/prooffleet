# Educational Overlays for Canonical Modules

This file provides concise pedagogical context for key canonical modules.
The goal is to pair verified artifacts with learning scaffolding.

## `MoltResearch/Basics.lean`

- **Intuition:** basic algebraic and logical rewrites are the smallest reusable units in larger formal proofs.
- **Proof sketch pattern:** start from `simp` and `rw`; isolate one transform per line when readability drops.
- **Common pitfalls:** overusing automation before introducing necessary local hypotheses.
- **Related tasks:** `T0_01`, `T0_03`.

## `MoltResearch/Logic.lean`

- **Intuition:** proposition-level transformations (`→`, `∧`, `∨`, `¬`) create glue lemmas used across domains.
- **Proof sketch pattern:** `intro` hypotheses early, then `constructor` / `cases` to mirror logical structure.
- **Common pitfalls:** proving a stronger statement than needed and getting stuck in mismatched goals.
- **Related tasks:** `T0_07`, `T0_11`.

## `MoltResearch/Discrepancy/Basic.lean`

- **Intuition:** foundational discrepancy definitions and small bounds let later modules reuse a common vocabulary.
- **Proof sketch pattern:** normalize definitions first, then prove small local inequalities and compose.
- **Common pitfalls:** jumping into advanced lemmas before reducing to canonical definitions.
- **API note:** `discOffsetUpTo` is monotone in the cutoff. Use `discOffsetUpTo_mono` for an arbitrary `N ≤ N'`, or the convenience wrapper `discOffsetUpTo_le_add` for the common “extend by `K`” case `N ≤ N+K`.
- **API note (max recursion):** when you need to peel the last case off a cutoff, rewrite `discOffsetUpTo f d m (N+1)` using `discOffsetUpTo_succ` to get a clean `max (discOffsetUpTo … N) (discOffset … (N+1))` normal form.
- **API note (step positivity):** when extracting unboundedness witnesses, prefer the `Nat.succ` normal forms (`HasDiscrepancyAtLeast.exists_witness_succ(_pos)` and the affine analogue) so you can work with a concrete positive step without carrying a separate `d ≥ 1` side condition.
  The corner case `d = 0` has `simp` normal forms too, but those are now behind `import MoltResearch.Discrepancy.Deprecated` to keep the stable surface focused on the `d ≥ 1` workflow.
- **Related tasks:** `T1_01`, `T1_07`, `T1_12`.
