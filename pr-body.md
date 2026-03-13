Card: Problems/erdos_discrepancy.md
Track: B
Checklist item: Swap start shift vs summand shift

Summary:
- Add the reverse-direction lemma for the existing normal form `apSumOffset_shift_add_add_offset_eq`, so rewrites can go either way without needing `.symm` at call sites.
- Add a stable-surface regression example in `MoltResearch.Discrepancy.NormalFormExamples`.

Notes:
- No new opportunistic lemmas; this is a coherence/compositionality refinement of an existing normal-form lemma family.
