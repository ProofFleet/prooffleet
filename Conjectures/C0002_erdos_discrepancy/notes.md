Notes and references for the Erdős discrepancy theorem live here.

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
