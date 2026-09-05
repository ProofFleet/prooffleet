# Track R — R9: Codex run 10 final report (2026-09-05)

Verbatim final report of Codex run 10 (gpt-5.6-sol, brief `Problems/tao2015_r9_brief.md`), whose four commits
shipped as the R9 PR. R9 gives `SliceMeanSquareA2` the `[mrt]` `X₀` quantifier order (`∃ A₀, ∀ A₁ ≥ A₀, ∃ levels,
clauses for every `A ∈ [A₁, A₁²]`), restricts R6-8 to its consumed scale set `S(A, Q) = [A/⌈Q⌉ − 1, 3A]`, lets R7 choose
one level list per dyadic block (Prop invoked at `A₁ = A/(4⌈Q⌉+4)`), and keeps the endpoint pins byte-identical. See the
design report, "Finding E" (why the level list must depend on the scale) and "R9 as run". Commit hashes are the run's,
before cherry-pick.

---

# Track R — R9 final report (2026-09-05)

Branch: `vex/track-r-r9`

Base: `1c862bd99064fbf5a92c4c9371d81115fdbf05ab` (the checked-out `origin/main` at the
start of the run)

Head: `a2a08885`

Codex run: `https://chatgpt.com/codex/tasks/01a07307-ae45-71a0-b039-ff6372e9f8ad`

## Outcome

R9 is complete. `SliceMeanSquareA2` now has `[mrt]`'s `X₀` quantifier order:

```text
exists A0, 1 <= A0 and
  forall A1, A0 <= A1 -> exists levels,
    clauses for every A in [A1, A1^2].
```

The R6/R7 consumer chooses one level list per dyadic block. No level list is shared
between two blocks. The same list is used for both complement-density blocks and all
reindexed class/character mean-square calls belonging to that one block.

No `sorry`, `axiom`, `unsafe`, or instance of an `*Assumption` class was added. No
forbidden nucleus file was edited. The stop rule did not trigger: every consumer scale
fits inside the Prop window.

## Commits and statements

### `8e9ffaab` — Track R: give A2 an X0 scale window (#3044, R9-1)

Changed `SliceMeanSquareA2` after the window-length hypotheses to:

```lean
∃ A₀ : ℝ, 1 ≤ A₀ ∧
  ∀ A₁ : ℕ, A₀ ≤ A₁ →
    ∃ levels : List (Finset ℕ),
      (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
      (∀ P ∈ levels, ∀ p ∈ P, C * Real.log h ^ B < p) ∧
      (∀ A : ℕ, A₁ ≤ A → A ≤ A₁ ^ 2 → density_clause levels A) ∧
      (∀ A : ℕ, A₁ ≤ A → A ≤ A₁ ^ 2 → mean_square_clause levels A₀ h ε A)
```

The source contains the clauses in full. The module and declaration docstrings record
that `A₀` is chosen after `h`, while `levels` is chosen after the scale-window base
`A₁`.

### `cd8f9b65` — Track R: restrict R6 to its consumed scales (#3044, R9-2)

Added the exact finite scale window used by the consumer:

```lean
noncomputable def majorArcScaleSet (A : ℕ) (Q : ℝ) : Finset ℕ :=
  Finset.Icc (A / ⌈Q⌉₊ - 1) (3 * A)
```

Thus

```text
S(A,Q) = [A / ceil(Q) - 1, 3A] intersect Nat.
```

`majorArc_block_bound_restricted` now takes `Q`, the block start `A`, `q ≤ Q`, and
the mean-square clause only for `A' ∈ S(A,Q)`. In its proof the actual calls are at

```text
A' = (A + d * (k * h0)) / d - 1,
d = gcd(b,q), d | q, k < H / h0 + 2.
```

The inherited bounds give `A/q - 1 ≤ A'` and `A' + J ≤ 3A`; since
`q ≤ ceil(Q)`, every such `A'` lies in `S(A,Q)`.

### `2191fefe` — Track R: choose A2 levels per major-arc block (#3044, R9-3)

Added:

```lean
theorem density_scales_mem_majorArcScaleSet (A : ℕ) (Q : ℝ) :
    A ∈ majorArcScaleSet A Q ∧ 2 * A ∈ majorArcScaleSet A Q

theorem majorArcScaleSet_subset_A2_window (A : ℕ) (Q : ℝ) (hQ1 : 1 ≤ Q)
    (hA : 16 * (4 * ⌈Q⌉₊ + 4) ^ 2 ≤ A) :
    ∀ A' ∈ majorArcScaleSet A Q,
      A / (4 * ⌈Q⌉₊ + 4) ≤ A' ∧
        A' ≤ (A / (4 * ⌈Q⌉₊ + 4)) ^ 2
```

`exists_wrapper_params` now returns `Q`, `h₀`, and a global strength/block threshold
`M`; for every natural block start `A ≥ M` it returns a fresh `levels` with:

- prime levels and `Q < p`;
- density on `(A,2A]` and `(2A,4A]`;
- mean square at every `A' ∈ S(A,Q)`.

The exact internal threshold is

```text
D    := 4 * ceil(Q) + 4
N    := max (ceil(Aprop)) (ceil(256*Q/epsilon))
Mnat := D*N + 16*D^2
M    := (Mnat : Real),
```

where `Aprop` is the threshold returned by `SliceMeanSquareA2`. For a block `A ≥ M`,
the Prop is invoked at

```text
A1 := A / D.
```

The `D*N` summand gives `Aprop ≤ A1`; the `16D²` summand supplies the containment
lemma; and `N ≥ ceil(256Q/epsilon)` gives `2 ≤ (epsilon/(128Q))*M`. Mean-square
non-pretentiousness is transported from strength `M` down to `Aprop`, as in R8.

`good_block_total_le` takes the two density facts and the `S(A,Q)` mean-square family
for its own block. `block_total_le_trichotomy` receives that same per-block data.
`majorArc_bound_of_A2_of_le_one` handles small/bad blocks trivially and calls
`hblockData` only in the good branch, after proving `M ≤ Ab`; it then constructs the
coprimality fact from that block's own prime levels.

The external interface threshold remains exactly

```text
A0 := 8*(Q*M + 50 + 2*log(64/epsilon))
      + exp((6*log(2*L0) + 80)/epsilon)
      + 256*Q/epsilon,
L0 := ceil(Q*(6*H + 7*Q + M + 2)).
```

### `a2a08885` — Track R: preserve the A2 endpoint pins (#3044, R9-4)

The endpoint docstring records the new `X₀` order and per-block choice. The declarations
remain:

```lean
theorem edp_of_sliceMeanSquareA2 (hA2 : SliceMeanSquareA2) ...
theorem theorem18_of_sliceMeanSquareA2 (hA2 : SliceMeanSquareA2) ...
```

`TrackCAxiomAudit.lean` was not edited. Its existing guards compiled, and the complete
before/after direct-typecheck logs compare byte-for-byte equal (`cmp` exit 0). The two
requested pins remain:

```text
'MoltResearch.Tao2015.edp_of_sliceMeanSquareA2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'MoltResearch.Tao2015.theorem18_of_sliceMeanSquareA2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Findings

1. The exact mean-square consumer range is tighter than the brief's conservative
   `4A + O(1)` discussion. R6 invokes mean square only at starts in
   `[A/ceil(Q)-1,3A]`; the density clauses are invoked only at starts `A` and `2A`.
   The endpoint `4A` is the right endpoint of the second density interval, not a Prop
   scale. Consequently it suffices to prove `3A ≤ A1²`, which the stated
   `16D² ≤ A` guard provides.

2. Small and bad dyadic blocks may lie below `M`, so their level lists cannot be
   selected from the wrapper's `∀ A ≥ M` family. The final block loop prices those
   branches trivially first and selects `levels` only after the good-block branch proves
   `M ≤ Ab`. This is the necessary quantifier placement.

3. The density removal is genuinely per block: it uses the same block's clauses at
   starts `Ab` and `2Ab` and does not require levels to agree with either a preceding or
   following dyadic block.

4. During the run `origin/main` advanced by the documentation-only Finding-E/R9-brief
   commit. Per the ground rule, no rebase or merge was performed; this branch remains
   four commits ahead and one commit behind the moving remote-tracking branch.

## Verification

All requested checks passed:

| Command | Exit | Result |
|---|---:|---|
| `lake env lean .../TrackCStage5MajorArcA2.lean` | 0 | R9-1/R9-2 source typecheck |
| `lake build Conjectures....TrackCStage5MajorArcA2` | 0 | 8,019 jobs |
| `lake env lean .../TrackCStage5MajorArcMR.lean` | 0 | R9-3 source typecheck, no diagnostics |
| `lake build Conjectures....TrackCStage5MajorArcMR` | 0 | 8,077 jobs |
| `lake env lean .../TrackCStage5MajorArcEDP.lean` | 0 | endpoint source typecheck |
| `lake build Conjectures....TrackCStage5MajorArcEDP` | 0 | 8,101 jobs |
| `lake env lean .../TrackCAxiomAudit.lean` | 0 | all guards accepted |
| `cmp /tmp/r9-audit-before.log /tmp/r9-audit-after.log` | 0 | byte-identical audit output |
| `./scripts/forbid_sorry.sh` | 0 | clean |
| `./scripts/forbid_axiom_unsafe.sh` | 0 | clean |
| `./scripts/check_layering.sh` | 0 | clean |
| `python3 scripts/check_aggregator_coverage.py` | 0 | 180 modules; only two allowlisted examples unreachable |
| `lake build MoltResearch.DiscrepancyAnalytic Conjectures` | 0 | 8,184 jobs; audit built |
| `git diff --check 1c862bd9..HEAD` | 0 | clean |

The full build emitted only pre-existing linter/deprecation warnings, including the
deprecated arithmetic-function import in `TrackCAxiomAudit.lean`.

## Final state

Changed committed files:

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcA2.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcMR.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcEDP.lean`

`CODEX_REPORT.md` is intentionally uncommitted. No push, merge, or rebase was performed.
