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
- **Related tasks:** `T1_01`, `T1_07`, `T1_12`.
