# The Erdős discrepancy theorem: release candidate and Palomar submission

This document records the release of the repository's formalization of the Erdős discrepancy
theorem: what is claimed, how the claim was checked, how anyone can check it again, and what is
left to decide before publication. The structured provenance record is
[`formalization.yaml`](../formalization.yaml); the statement of record is
[`PalomarEDP/Challenge.lean`](../PalomarEDP/Challenge.lean).

Status on 27 September 2026: **release candidate prepared; not published; not submitted to
Palomar.** The repository is private. Section 7 records the maintainer's decisions so far and lists
those that remain.

## 1. The claim

For every `f : ℕ → ℤ` with `f n = 1 ∨ f n = -1` for all `n`, and every natural number `C`, there
are `d ≥ 1` and `n` with `|f(d) + f(2d) + ⋯ + f(nd)| > C`:

```lean
theorem EDP.erdos_discrepancy
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1) :
    ∀ C : ℕ, ∃ d n : ℕ,
      0 < d ∧
      C < Int.natAbs ((Finset.range n).sum (fun i => f ((i + 1) * d)))
```

This is Corollary 1.2 of Terence Tao, *The Erdős discrepancy problem*, Discrete Analysis 2016:1
(arXiv:1509.05363). It is a formalization of a published result. It makes no claim of a new proof,
of priority, or of endorsement by Tao, Palomar or anyone else.

| Item | Value |
| --- | --- |
| Statement of record | `EDP.erdos_discrepancy` in `PalomarEDP/Challenge.lean` (imports `Mathlib` only) |
| Proof | `EDP.erdos_discrepancy` in `PalomarEDP/Solution.lean`, by `MoltResearch.erdos_discrepancy f hf` |
| Development's theorem | `MoltResearch.Tao2015.erdos_discrepancy_unconditional : IsSignSequence f → ¬ BoundedDiscrepancy f` |
| Comparator configuration | `comparator.json`: one theorem, no definition holes, axioms `propext`, `Quot.sound`, `Classical.choice` |
| Axioms used | `propext`, `Classical.choice`, `Quot.sound` (pinned by `#guard_msgs` in `Solution.lean` and `TrackCAxiomAudit.lean`) |
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | tag `v4.35.0-rc2`, commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Licence | Apache-2.0 (canonical text in `LICENSE`) |

## 2. Statement review

The Challenge was written for this release and checked against Tao's Corollary 1.2 by the agent
that prepared the packaging (Claude Opus 5.5, in Claude Code). Sean Huver, the maintainer, reviewed
it on 27 September 2026. `formalization.yaml` records this as the author's own check
(`review.status: self-assessed`), not an independent review. Another reviewer needs only
`PalomarEDP/Challenge.lean` (under 60 lines, Mathlib only) and Tao's introduction. The agent's
checks:

| Question | Answer |
| --- | --- |
| Is `f` arbitrary? | Yes. The only hypothesis is `hf`, that every value is `1` or `-1`; there is no multiplicativity or other structure. |
| Is the progression `d, 2d, …, nd` with `d` positive? | Yes. `Finset.range n` is `{0, …, n-1}`, and the summand at `i` is `f ((i + 1) * d)`; `0 < d` is part of the conclusion. |
| May `d` and `n` depend on the threshold? | Yes: `∀ C, ∃ d n`. |
| Is the conclusion strict excess over every threshold? | Yes: `C < |…|` for every `C : ℕ`, which is `sup = ∞`; the absolute value is `Int.natAbs`, so the comparison is in `ℕ`. |
| Does indexing by `ℕ` rather than the positive integers change anything? | No. `hf` also constrains `f 0`, but `d ≥ 1` means `f 0` is never evaluated, and every sequence on the positive integers extends to `ℕ` by either value at `0`. |
| Degenerate cases | `n = 0` gives the empty sum `0`, which never exceeds `C`, so witnesses have `n ≥ 1` as in Tao's `sup_{n,d ∈ ℕ}` with `ℕ = {1, 2, …}`. |
| Hidden premises or definitions? | None. The Challenge has no `variable`, no instance argument, no project definition, and `comparator.json` has no definition holes. |
| Does it match the development's statement? | Yes, mechanically: the Solution proves it by applying `MoltResearch.erdos_discrepancy`, whose definitions (`IsSignSequence`, `apSum`, `HasDiscrepancyAtLeast`) unfold to exactly this expression. |
| Independent cross-check | The development also proves, verbatim, the Formal Conjectures project's separately written statement of Erdős Problem 67 (`MoltResearch.Erdos67.erdos_67`: real-valued `±1` sequences, a real threshold `C > 0`, sums over `Finset.Icc 1 m`). |

## 3. Baseline and toolchain migration

**Baseline.** `main` at `f4aacd377a5e88678cd8188f8232fcba7dfb459b` (8 September 2026), Lean
`v4.28.0`, Mathlib `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`). CI run
[34258675841](https://github.com/ProofFleet/prooffleet/actions/runs/34258675841) on that commit was
green: it builds every target in `scripts/ci_targets.txt`, and `TrackCAxiomAudit.lean` pins the
axiom footprint of the flagship theorems. Measured before any change:

- `lake build` alone builds only the default `MoltResearch` library. The CI contract is
  `scripts/ci_targets.txt`: the default library, six standalone audit and regression modules, the
  `Solutions` library, the whole `Tasks` and `Conjectures` backlog, and `DiscrepancyUpstream`.
- `scripts/check_aggregator_coverage.py`: 213 of 215 `MoltResearch` modules are compiled by CI;
  `EndpointSimpExamples` and `PaperSimpExamples` are allowlisted as not compiling (outside the
  EDP proof).
- The source gates all passed. No `sorry`, `admit`, `axiom` or `unsafe` occurs in the code of any
  tree; `native_decide` occurs 24 times, all in `Conjectures/C0004_erdos461_smooth`, outside the
  proof.
- The statement has no hypothesis classes; its axioms are `propext`, `Classical.choice` and
  `Quot.sound`.

**Choice of toolchain.** Palomar requires `leanprover/lean4:v4.35.0-rc2` or later
(`PalomarSubmission/toolchains.json` at `a59f25bd`), because that is where `lake comparator` and the
bundled NanoDa and con-ron kernels appear. The project uses exactly `v4.35.0-rc2`, the version
Palomar's template and its verifier's compatibility fixture exercise. Mathlib's tag
`v4.35.0-rc2` resolves to `065356127b1dc0016f66b7283ce0ce2c4055aa55`, whose `lean-toolchain` is
exactly `leanprover/lean4:v4.35.0-rc2`, and the manifest repeats Mathlib's own pins for all eight
transitive dependencies. `v4.35.0-rc3` (24 September) differs from rc2 by three runtime
reference-count fixes and a Lake option for path dependencies; moving to it, or to `v4.35.0` when
released, is a one-line change plus a manifest update.

**What the migration changed.** No theorem statement, definition or hypothesis changed; every
edit is to a proof or an import. The categories are listed in section 9.

## 4. What the proof depends on

The import closure overstates what the proof uses: the public wrapper imports the stable-surface
aggregators, which pull in most of `MoltResearch/`. `scripts/edp_dependency_closure.lean`
measures the *declaration* closure instead, meaning every constant reachable from
`MoltResearch.erdos_discrepancy` through the constants its type and proof mention. That is what
the kernel checks and what Comparator exports. Measured on commit `0df23b99`:

| | Constants in the closure |
| --- | ---: |
| Mathlib | 67,088 |
| Lean core (`Init`) | 7,976 |
| Batteries, Aesop | 197 |
| This repository (`MoltResearch.*`, `Conjectures.*`) | 5,962 |
| **Total** | **81,223** |

| Part of the repository | Modules used by the proof | Lines in those modules |
| --- | ---: | ---: |
| `MoltResearch/` | 135 of 215 | 129,698 of 158,180 |
| `Conjectures/C0002_erdos_discrepancy/` | 173 of 222 | 42,603 of 55,261 |
| `Conjectures/C0001`, `C0003`–`C0006` (other problems) | 0 of 25 | 0 of 4,808 |
| `Tasks/`, `Solutions/` (onboarding exercises) | 0 of 85 | 0 of 636 |
| **Total** | **308 of 547** | **172,301 of 218,885** |

The declarations the proof uses span 97,813 source lines. Another 48 modules are imported by the
proof's modules but contribute no declaration to it:
- the superseded Littlewood route and the all-frequency Matomäki–Radziwiłł module;
- several unused `SliceA2` variants;
- the general discrepancy API (offset, affine, reindexing and similar wrappers) that the stable
  surface re-exports.

The rest of the repository is related library material, onboarding exercises, and research on
other problems.

Regenerate with `lake env lean scripts/edp_dependency_closure.lean` after building `Conjectures`.

## 5. How to check it yourself

Requirements: Git, `elan` (installs the pinned Lean), about 10 GB of disk for `.lake`, and Python 3
with PyYAML for the metadata check. The Comparator step needs Linux with bubblewrap; everything
else also runs on macOS.

```bash
git clone https://github.com/ProofFleet/prooffleet && cd prooffleet
git checkout <candidate SHA>
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
~/.elan/bin/lake exe cache get          # Mathlib's official prebuilt cache; the project builds from source
make ci                                 # source gates + every CI target (includes the audit pins and PalomarEDP)
python3 scripts/check_palomar_submission.py   # Palomar's toolchain-free intake rules
./scripts/verify-comparator.sh          # Linux + bubblewrap: lake comparator with NanoDa and con-ron
```

For the metadata check with Palomar's own validator and the upstream schema, as CI runs it:

```bash
git clone https://github.com/PalomarRegistry/PalomarSubmission /tmp/ps && git -C /tmp/ps checkout a59f25bd8a66bf6faf3a4f4260d412989c0185ea
git clone https://github.com/mathlib-initiative/formalization.yaml /tmp/fy && git -C /tmp/fy checkout 99c678e569c7c4c0772db297c5ddd5e4c9b6322e
python3 scripts/check_palomar_submission.py --palomar-submission /tmp/ps --formalization-schema /tmp/fy
```

The `Palomar` workflow (`.github/workflows/palomar.yml`) runs the intake checks and the sandboxed
Comparator on GitHub's Linux runners; dispatch it with `fresh: true` to build the project from
source. Once the repository is public, the `Palomar preflight` workflow runs Palomar's own verifier
at a pinned commit: that is the closest predictor of Palomar's mechanical verdict.

These steps use Mathlib's official olean cache, as Palomar does; none of them rebuilds Mathlib
from source.

## 6. Verification record

A commit cannot record the results of checking itself. The results for a specific candidate SHA
(the fresh-clone build, the CI runs and the Linux Comparator run) are therefore recorded in the
pull request that proposes it and in the release notes. This table records what was checked
while the release was prepared, on 26 and 27 September 2026, on the tree that became the candidate.

| Check | Command | Environment | Result |
| --- | --- | --- | --- |
| Baseline CI on `f4aacd37` (Lean v4.28.0) | GitHub Actions `CI` | ubuntu-latest | green (run 34258675841, 8 Sept.) |
| Baseline source gates on `f4aacd37` | the six gate scripts run by CI | macOS 26, local | all pass; 2 allowlisted uncompiled modules |
| Every CI target on v4.35.0-rc2 | `lake build $(scripts/ci_targets.txt)` | macOS arm64, 12 cores, local | 0 errors, with the fixes in section 9 applied as blanket guards |
| Minimizing the guards | every file whose guards were reduced, recompiled against that build | local | all 310 files compile |
| Axiom pins | `TrackCAxiomAudit.lean`, `PalomarEDP/Solution.lean` (`#guard_msgs`) | same build | hold: `propext`, `Classical.choice`, `Quot.sound` |
| Challenge compiles on its own | `PalomarEDP.Challenge` target | same build | one `sorry` warning, as intended |
| Source gates | `forbid_sorry.sh`, `forbid_axiom_unsafe.sh`, `check_layering.sh`, `check_aggregator_coverage.py`, `check_interfaces.py`, `check_task_metadata_coverage.py` | local | pass |
| Intake rules and metadata | `scripts/check_palomar_submission.py` with PalomarSubmission `a59f25bd` and formalization.yaml `99c678e5` | local | 0 failures, 0 warnings |
| Licence text | SHA-256 of `LICENSE` | local | canonical Apache-2.0 text |
| Declaration closure | `scripts/edp_dependency_closure.lean` | local | section 4 |

### Results for commit `0df23b99`

`0df23b99e3043a84bc2acb0a8458295bbf0cf17e` is the last commit that changed any Lean, Lake or
Palomar file. Later commits touch only CI and documentation.

| Check | Environment | Result |
| --- | --- | --- |
| Fresh clone at the SHA, `lake exe cache get`, build of every CI target from source | macOS 26.6 arm64, 12 cores | success, 0 errors, 54 min (Mathlib from its cache) |
| `make ci` in that clone | same | success |
| `scripts/check_palomar_submission.py` with Palomar's validator and the upstream schema | same | 0 failures, 0 warnings |
| Six source gates | same | pass |
| `lake comparator --inadvisably-no-sandbox` (development check) | same | accepted: Lean kernel, NanoDa, con-ron (79,620 declarations) |
| `Palomar` workflow, run [36288498533](https://github.com/ProofFleet/prooffleet/actions/runs/36288498533) on the PR merge ref (same tree) | Ubuntu 24.04 x86_64, bubblewrap 0.9.0, Lean v4.35.0-rc2 | intake and Licensee (Apache-2.0) pass; sandboxed `lake comparator`, cold build: **accepted** by Lean's kernel, NanoDa and con-ron (79,620 declarations), exit 0, 101 min |
| `CI` workflow, run [36288498532](https://github.com/ProofFleet/prooffleet/actions/runs/36288498532) | GitHub-hosted ubuntu-latest | infrastructure failure: `no space left on device` at module 9341 of 9483; no compile error. Fixed by reclaiming disk before `.lake` is populated (`.github/workflows/ci.yml`) |

Checks for any later candidate SHA, reported with it:

1. a fresh clone at the SHA, `lake exe cache get`, and a from-source build of every CI target;
2. `make ci` and the metadata check in that clone;
3. the `CI` and `Palomar` workflows on GitHub. `Palomar` runs the sandboxed `lake comparator` with
   the NanoDa and con-ron kernels on Linux and keeps the log as an artifact;
4. once the repository is public, the `Palomar preflight` workflow.

A local `lake comparator --inadvisably-no-sandbox` run on macOS is a development check only; the
sandboxed Linux run is the one that counts.

## 7. Decisions before publication

These belong to the maintainer. Decided on 27 September 2026:

- **Name.** ProofFleet, with the repository slug `prooffleet` in lower case. The private repository
  has been `ProofFleet/prooffleet` since 26 September 2026 (see [`rename.md`](rename.md)); which
  repository becomes the public one depends on item 1 below.
- **Statement review.** Sean Huver reviewed `PalomarEDP/Challenge.lean` (section 2); recorded in
  `formalization.yaml` under `review`.
- **Authorship.** Sean Huver is the only author and responsible maintainer in
  `formalization.yaml`. Palomar reserves those fields for people, and the agents are credited under
  `automation`, where `Vex` and `JvN` are described as agent identities whose models are not
  recorded. An ORCID can still be added.

Still open; nothing below has been done:

1. **How to publish.** The repository's history contains a personal phone number, in an April 2026
   ops note that an agent wrote into the README: it was there from commit `94d46b9b` (17 April
   2026) until `2f8c666d` (8 September 2026) removed it, and it stays in every commit in between.
   The same day, the squash of #3732 briefly restored the old README and #3739 removed the number
   again. A scan of every object on all 215 branches found it in no other file and in no commit
   message; pull-request refs and issue or pull-request text were not searched. Making this
   repository public as it is would publish the number. There are two routes:
   - **Redacted snapshot (recommended; the documented route in [`RELEASING.md`](../RELEASING.md)).**
     `scripts/publish_snapshot.sh` pushes a copy of `main` and the tags, with the history passed
     through `git filter-repo --replace-text`, to a separate public repository. The redaction file
     `~/.config/moltresearch/snapshot_replacements.txt` is not on the machine that prepared this
     release, so the maintainer must supply it. Consequences: the public commit SHAs differ from
     the private ones, so Palomar is given the snapshot's SHA; issues and pull-request discussions
     stay private; and a name must be chosen for the public repository. If it should be
     `ProofFleet/prooffleet`, first rename the private one (for example to `prooffleet-dev`). The
     old `moltresearch` redirect keeps following the private repository, but links to
     `ProofFleet/prooffleet` would then open the public one.
   - **Rewrite in place.** Remove the number from this repository's history
     (`git filter-repo --replace-text`, then force-push every branch), ask GitHub Support to purge
     cached views and pull-request refs, which a rewrite cannot reach, then make the repository
     public. This keeps issues, pull requests and one repository identity. It invalidates every
     clone and every pinned SHA, and the number may also appear in issue or pull-request text.
2. **Submitting to Palomar** (section 8), after publication and a passing preflight on the exact
   commit.
3. **Registering** after reading Palomar's review. Registration is permanent public record.
4. **Announcing** to colleagues. Nothing has been sent.

## 8. Submitting to Palomar

Recheck the live requirements first: [Palomar's policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[the submission host's protocol](https://submit.palomar-registry.org/llms.txt) and
[`toolchains.json`](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json).
This release was prepared against PalomarPolicy `792c7c0b` (17 September 2026), PalomarSubmission
`a59f25bd` (25 September 2026) and PalomarTemplate `cb5c79b6` (23 September 2026).

1. Publish the candidate (section 7, item 1) and confirm that the exact commit and every pinned
   dependency can be fetched without credentials.
2. Run the `Palomar preflight` workflow on that commit (Actions → Palomar preflight → Run
   workflow). It runs Palomar's own verifier at PalomarSubmission `a59f25bd` with
   `mode: full` and `execution_profile: palomar-standard-v1`. Submit only after its report says
   `status: pass`.
3. Submit through the host's API, not the browser form. The maintainer must first agree the
   inputs, including the relationship answer, which is recorded permanently:
   - repository: the public repository; commit: its full 40-character SHA;
   - `comparator_config_path`: `comparator.json`;
   - `authorization_relationship`: `maintainer` ("I am a responsible author or maintainer").
   Ownership of the repository is then proved with a `palomar-verify-<challenge>` tag at the
   commit plus a secret gist, both deleted immediately afterwards. The returned access token is a
   credential: it reads the private review and can register.
4. Poll `GET /api/submission` at a human pace until the mechanical run and the review finish, then
   show the maintainer the review from `GET /api/review`.
5. Register (`POST /register` with the review's digest) only on the maintainer's explicit
   instruction, after they have seen the review and what registration publishes. Then confirm the
   registry record exists before announcing anything.

What Palomar provides: a durable record of the checked statement and proof, and an automated
editorial review. It does not establish novelty, replace expert peer review, or endorse the
project.

## 9. Migration details and known limitations

### What changed in the Lean sources

Every change is to a proof or an import. No theorem statement, definition or hypothesis changed, and
the axiom pins, which were not edited, still hold. The migration touches 71 files (+223/−239 lines).
By cause:

- **`simpa … using e` now closes at reducible transparency** (Lean v4.35; `using!` restores the
  earlier default-transparency check). 68 `simpa` calls that relied on unfolding an ordinary
  definition at that step now say `using!`; most compare `disc` with `discrepancy`.
- **Mathlib's `convert` now closes side goals at reducible transparency** and with
  `sameFun := true` (`Convert.CheapConfig`); `convert!` keeps the earlier behaviour. 13 calls whose
  leftover goals equate a function with a composition (`(fun v => g (v / ρ)) = g ∘ …`) now use
  `convert!`.
- **Earlier beta-reduction during elaboration**: goals no longer contain `(fun x => …) a`, so 25
  `dsimp only` / `simp only []` / `simp only` steps whose only effect was to beta-reduce made no
  progress (an error) and were removed. For the same reason a `rw` using a hypothesis stated as an
  explicit redex was restated in reduced form.
- **`isDefEq` no longer raises implicit arguments to default transparency** (the old behaviour is
  behind `backward.isDefEq.respectTransparency`, which this migration does not use). Where a
  rewrite relied on it, the proof now uses the lemma directly:
  - `Circle.norm_coe` instead of `rw [norm_eq_of_mem_sphere]`;
  - `Finset.mem_image.mp`/`.mpr` for images built with `⟨_, _⟩ : Nat.Primes`;
  - `add_left_injective 1` as the injectivity proof of an embedding;
  - binder types on the lambdas inside two `change` targets, where their absence had become a
    heartbeat timeout;
  - `simp [Homeomorph.subRight]` without unfolding `Homeomorph.mulLeft₀`.
- **Mathlib renames and removed deprecations**:
  - `Finset.prod_le_prod`, `prod_lt_prod` and `prod_le_one` (the ordered-semiring forms) are now
    `…₀`, and the unprimed names mean the monoid lemmas;
  - `Finset.range_eq_Ico` is now pointwise;
  - `integral_fintype` and `zero_le` take their arguments implicitly;
  - `intervalIntegral.intervalIntegrable_const` moved to the root namespace;
  - `Measure.isProbabilityMeasure_map` became an instance;
  - the plain name `Finset.antidiagonal` now resolves to the `IsPWO` construction, so the proof
    uses `Finset.HasAntidiagonal.antidiagonal`;
  - `Finset.sum_inter_add_sum_diff` → `…_sdiff`; `fderiv_deriv` → `fderiv_apply_one_eq_deriv`;
  - `DirichletCharacter.eq_one_iff_conductor_eq_one` no longer takes the `≠ 0` argument;
  - `Mathlib.NumberTheory.ArithmeticFunction` was split (`.Misc` provides `cardFactors`);
  - names deprecated before v4.28 and since removed are replaced by their successors:
    `Nat.pow_le_iff_le_log`, `div_add_div_same`, `mul_le_mul_left'`/`right'`, `Int.ediv_add_emod`,
    `Nat.Coprime.mul` and `Finset.filter_union_filter_neg_eq`/`disjoint_filter_filter_neg`.
- **Other upstream changes**:
  - Borel–Carathéodory now assumes `re ≤ M` rather than `re < M`, so the existing `<` bound is
    weakened before it is passed in;
  - `Continuous.pow` now produces a Pi-power function, so two integrability arguments state the
    pointwise form;
  - `norm_num` now evaluates `|π|` itself;
  - `field_simp` needs an explicit cast-nonvanishing hypothesis in one place;
  - a `Fact p.Prime` local instance that changed the instance path `simp` found was unused and was
    deleted.

Deprecation warnings (`push_neg`, `if_pos`/`if_neg`, `Finset.prod_le_prod'` and others) remain:
they do not affect correctness, and removing them is a separate cleanup.

### Known limitations

- The Palomar preflight (Palomar's own verifier) cannot run until the repository is public; the
  local and CI Comparator runs are rehearsals of it, not substitutes.
- No person has reviewed the statement of record (section 2) or the proof; `formalization.yaml`
  says so.
- The Hilbert-space version of the theorem (Tao's Theorem 1.1) and any explicit discrepancy bound
  are not formalized. Some constants in the proof are existential.
- Outside the proof: two regression modules do not compile (`scripts/uncompiled_allowlist.txt`),
  `Conjectures/C0004_erdos461_smooth` uses `native_decide`, and some docstrings in
  `Conjectures/C0002_erdos_discrepancy/src/` still describe inputs as unproved interfaces that now
  have instances (for example `Interfaces/LargeValues.lean` and
  `TrackCStage5VinogradovKorobov.lean`).
- `Problems/sources/tao2015_statements.md` transcribes the papers from their ar5iv renderings and has
  not been checked against the published PDFs by a person.
