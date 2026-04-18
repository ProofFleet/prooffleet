Notes and references for the Erdős discrepancy theorem live here.

## Track C pipeline skeleton (Conjectures/C0002)

Hard-gate build target:
- Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy

Key stage boundary modules:
- Stage 2 boundary record: Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary
  (defines Tao2015.Stage2Output)
- Stage 2 conjecture stub (the only non-verified assumption):
  Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub
  (axiom stage2, abbrev stage2Out)
- Stage 3 boundary record: Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
  (defines Tao2015.Stage3Output and derives notBounded)
- Stage 3 minimal entry point: Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal
  (defines stage3 and proves stage3_notBounded and stage3_forall_hasDiscrepancyAtLeast)

## Surface forms / equivalences (proved)

The core nucleus predicate is:
- `HasDiscrepancyAtLeast f C` (see `MoltResearch/Discrepancy/Basic.lean`).

Useful equivalences (prefer these over unfolding definitions):

- **Quantifier normal forms**
  - `HasDiscrepancyAtLeast_iff_exists_witness_pos`:
    `HasDiscrepancyAtLeast f C ↔ ∃ d n, d > 0 ∧ n > 0 ∧ …`

- **Paper interval-sum notation**
  - `apSum_eq_sum_Icc`:
    `apSum f d n = ∑ i ∈ Icc 1 n, f (i*d)`
  - `HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos`:
    `HasDiscrepancyAtLeast f C ↔ ∃ d n, d>0 ∧ n>0 ∧ |∑_{i=1}^n f(i*d)| > C`
  - `HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos`:
    same, but writing the step condition as `d ≥ 1`.

- **“Unbounded discrepancy” wrappers**
  - `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`
  - `forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos`

- **Structured witnesses (for composition)**
  - `HasDiscrepancyAtLeast.iff_nonempty_witness`
  - `HasDiscrepancyAtLeast.iff_nonempty_witnessPos`

## References

- Terence Tao, “The Erdős discrepancy problem” (2015)
