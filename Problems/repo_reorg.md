# Problem Card: repository reorganization and CI economics

Status: active

## 0. One-line pitch

Make the substrate reusable by more than one problem: move the general analytic mathematics out
from under `MoltResearch/Discrepancy/`, and make CI fast and honest enough to carry several
campaigns at once.

## 1. Why

`MoltResearch/` is ~107k lines, and most of it is general analytic number theory — zeta and the
zero-free region, the Selberg sieve, Halász, entropy, characters — that was built for the Tao
2015 pipeline but lives under an EDP-specific path. A second problem card cannot import that work
without dragging EDP in with it.

Two supporting problems had to be fixed first: CI could not sustain the merge rate, and the
`*Assumption` interfaces that carry the proof's conditionality had no mechanical review.

## 2. Status

**Done and merged** — CI economics (#3500, #3501):

| | before | after |
|---|---|---|
| build-cache entry | 2.39 GB, ~57 s save | 114 MB, ~10 s |
| entries in the 10 GB budget | ~4 | ~85 |
| deps-cache save | failed silently every run | succeeds, verified |
| main-push CI | 4.6 min median, 20% of runs 22–25 min | warm runs ~1m40s–2m30s |
| violation reported after | ~90 s | ~5 s |

**Not started** — the rehome itself. No file has moved; `MoltResearch/Analytic/` does not exist.

## 3. Evidence behind the design choices

Keep these; they are why the decisions below should not be relitigated from scratch.

- **The slow tail was cache staleness, not compile cost.** Two commits each touching *only*
  `WindowAssembly.lean` built in **1m28s** and **23m05s**. The slow one rebuilt `RieszCapstone`
  (541 s), `HalaszAssembly` (198 s), `HalaszComplex` (101 s) — all of which `WindowAssembly`
  *imports*, so editing it cannot invalidate them. The restored cache simply held stale oleans.
- **The runner is disk-bound.** Measured at save time: 72 G disk, **1.8 G free (98% full)**,
  `.lake/packages` 6.9 G, `.lake/build` 1.3 G. A 6.9 G tree cannot be tarred into 1.8 G, so the
  deps cache had been failing on every run — silently, because `actions/cache/save` only warns.
  Inodes were 13% used, so that was never the cause.
- **The deps cache is worth keeping.** `lake exe cache get` takes **2m30s**, because it clones
  Mathlib's source as well as fetching oleans, against ~60 s to restore the archive.
- **Change-scoped CI was measured and rejected.** ~60 s of a warm run is cache restores that
  happen whatever targets are selected, so scoping cannot touch the tail; it would help only
  docs-only PRs, while adding a path for a PR to merge green having skipped what it broke.
- **`MultiplicativeC` is the rehome's choke point.** `scripts/gen_move_manifest.py` reports **47
  modules movable today, 79 with the split modelled** (`--assume-split`). That single import edge
  gates 37 modules — the whole pretentious/Halász stack.

## 4. Decomposition (PR-sized items)

Quote a checkbox verbatim in a PR's `Checklist item:` line.

### Phase 0 — hygiene (no toolchain needed for 0.3; 0.1–0.2 edit Lean)

- [ ] 0.1: delete `TrackCStage2Stub.lean` and its 8 importers, tick the endgame card box
- [ ] 0.2: extend `forbid_axiom_unsafe.sh` to `Conjectures/` with an empty allowlist (needs 0.1)
- [x] 0.3: `scripts/ci_targets.txt` as the single source of truth for the CI target set

### Phase C — CI economics

- [x] C0: cache freshness reporting, `df`/`df -i` diagnostics, save verification for both caches
- [x] C1: split the cache at the immutability boundary (`.lake/packages` vs `.lake/build`)
- [x] C1b: reclaim runner disk before saves, gated to runs that actually save
- [x] C1c: run the toolchain-free grep gates before elan and the caches
- [ ] C3: key PR cache runs off `github.event.pull_request.head.sha` — on `pull_request` events
      `github.sha` is an ephemeral merge commit, so the staleness metric prints `?` on PRs
- [ ] C4: investigate the heavy modules (`RieszCapstone` alone is 541 s) — split, profile with
      `set_option profiler`, or move to a larger runner

### Phase R — rehome (waits for the MR leg; R2 needs a Lean toolchain)

Target layout, inside the existing `MoltResearch` lean_lib so no lakefile change is needed:
`MoltResearch/Analytic/{Zeta,PrimeCounts,Sieve,Pretentious,Characters,Probability,Windows}/`,
each with its own aggregator surface. All 143 `Discrepancy/` files declare exactly
`namespace MoltResearch`, so the move is `git mv` plus import rewrites — no proof edits.

- [x] R1: `scripts/gen_move_manifest.py` computes the move set from the import graph
- [ ] R2: split `MultiplicativeC.lean` — it is Mathlib-only except its line-1 import and the tail
      (`norm_sum_Icc_intCast_eq_natAbs_apSum_one`, `CompletelyMultiplicative.toC`,
      `IsSignSequence.unimodularC`), which moves to a new `MultiplicativeCBridge.lean`
- [ ] R3: the big-bang move PR, under an announced merge freeze, manifest regenerated at freeze
      time (the tree grows 1–3 modules/day, so a pre-computed manifest is stale)
- [ ] R4: one week of drain — in-flight PRs rebase via the manifest
- [ ] R5: tighten — drop the transition shim from `Discrepancy.lean`, delete
      `DiscrepancyAnalytic.lean`, make the guard scripts hard gates

### Phase I — interface review (CI-mechanical only; no human approval step)

- [x] I0: `scripts/check_interfaces.py` — citations, registry coverage, instance-honesty
- [x] I0b: fix three stale "no instance may be declared" docstrings (VinogradovKorobov,
      PrimeQuadrupleCount, PrimeBlockMajorArc — each contradicted by an unconditional instance)
- [ ] I1: extract the 13 `*Assumption` classes into `Conjectures/<card>/src/Interfaces/`,
      burning down `scripts/interface_location_allowlist.txt`
- [ ] I2: add the 6 classes missing from `Problems/sources/tao2015_statements.md`, and a citation
      for `LittlewoodLBoundAssumption` — **transcribe from the papers, not from the Lean
      docstrings**, since that registry exists precisely to be the text interfaces are diffable
      against
- [ ] I3: flip `check_interfaces.py` to `--strict`; require an `Interface-Review:` PR field and a
      same-PR registry update whenever an interface changes

## 5. Blocked work, and what unblocks it

Everything here needs a Lean toolchain and Mathlib cache. Ranked by value:

1. **Dead simp lemmas in `EndpointSimp.lean`.** `apSumOffset_succ_succ` and its siblings are
   keyed on `Nat.succ n`, which simp normalises to `n + 1` — so they compile (their own proofs go
   through `simpa … using` the base lemma) but plausibly can never fire downstream. If that is
   right, proofs written expecting them have been relying on something else, and the endpoint
   simp surface is weaker than it looks. Confirm with `set_option trace.simp` on one of the
   examples in `scripts/uncompiled_allowlist.txt`.
2. **The two allowlisted regression files.** `EndpointSimpExamples` and `PaperSimpExamples` have
   never compiled. Fixing them means strengthening the endpoint simp surface, or restating the
   examples against goals it genuinely handles — *not* rewriting `by simp` to `by exact`, which
   would make each example a tautology and destroy what it tests.
3. Items 0.1, 0.2, R2, I1 above.

## 6. Conventions this card depends on

- The CI metadata gate hard-fails any PR touching `MoltResearch/` without
  `Card: Problems/repo_reorg.md` and a `Checklist item:` matching a checkbox above **exactly**.
  The rehome moves ~79 files under `MoltResearch/`, so this card is a prerequisite for it.
- `scripts/check_aggregator_coverage.py` requires every `MoltResearch/**/*.lean` to be compiled
  by some CI target. A new module goes in its aggregator, or — if it must stay outside the stable
  surface (opt-in simp modules, compile-only regression files) — in `scripts/ci_targets.txt`.
- `scripts/check_layering.sh` will enforce that `MoltResearch/Analytic/` never imports
  `MoltResearch.Discrepancy.*` once the move lands. It is a no-op until then, by design.
