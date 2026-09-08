# Problem Card: harness hardening (what we adopt from LeanMarathon, and what we keep)

Status: active (opened 2026-09-08, after campaign #3044 closed)

## 0. One-line pitch

Seven tooling items that turn three of the repo's prose rules into mechanical gates (worker scope, frozen statements,
interface hygiene), make "does this lemma advance the flagship theorem" a computed fact, and give cards with
dependencies a scheduler and a blocked-report protocol — so that the next campaign can run agents concurrently on a
card with real dependencies between items. Everything here is scripts/CI/docs; no Lean statement changes.

## 1. Why (the comparison, in one paragraph)

A review against LeanMarathon (blueprint-graph scheduler, patch tool that freezes the target's type, Blueprinter /
Target-Reviewer / Worker / Refiner roles, prose-vs-elaborated dependency checks) found our distinctive strength to be
conditional milestones — unfinished mathematics enters as a source-linked `*Assumption` class carried in the theorem's
type, main is sorry-free at every commit, a deep prerequisite becomes its own campaign — and our weaknesses to be
exactly the things prose cannot enforce: worker scope, statement drift, and target relevance. Our own record agrees:
all eleven design findings of campaign #3044 and the one card defect of the upstreaming pilot were caught by a worker's
stop-report, none by tooling. We keep the interfaces and the card-as-plan; we adopt the mechanical containment.

## 2. Rules for this card (read with `AGENTS.md`)

- One item per agent at a time (a draft recorded as blocked does not count); one item per PR; claim by branch
  `hh/<id>-<name>` + draft PR titled `<id>: <item name>` before writing code; check `gh pr list --state open --search "<id>"`.
- Edit only the item's listed deliverables. Items that touch `.github/workflows/ci.yml` or `Makefile` add **one line**
  each in the pre-allocated place (see Setup) so concurrent items do not conflict.
- A gate lands in **warning mode first** (prints `::warning::`, exits 0) with a one-line switch to strict; the flip to
  strict is a separate one-line PR after the warning has been quiet on main for a day.
- Every script has a `--self-test` that runs on a fixture and is exercised by the gate runner.
- Respect `after:` prerequisites: do not start an item whose `after:` items are unticked.
- PR metadata: `Card: Problems/harness_hardening.md`, `Track: N/A`, `Checklist item: <verbatim>`.

## 3. Decomposition (mergeable sub-tasks)

- [ ] Setup: gate runner — `.github/workflows/ci.yml` gets two steps, "Pre-build gates" (runs every `scripts/gates.d/pre/*.sh` in name order, before the toolchain install) and "Post-build gates" (runs every `scripts/gates.d/post/*.sh` after the build); `make ci` runs the same; `scripts/gates.d/README.md` states the contract (a gate is a bash script; `GATE_STRICT=1` makes warnings fail; PR context via `$GITHUB_EVENT_PATH` when present, skip cleanly otherwise). Deliverables: `.github/workflows/ci.yml`, `Makefile`, `scripts/gates.d/README.md`, `scripts/gates.d/pre/.keep`, `scripts/gates.d/post/.keep`.

- [ ] H-1: Path-scope gate (after: Setup) — `scripts/gates.d/pre/10-pr-scope.sh`: if the PR body's `Checklist item:` names an item whose card text contains `Deliverable in \`<path>\`` or `Deliverables: \`<path>\`, …` clauses, every file changed by the PR must be one of those paths or the card file itself; otherwise the gate is silent. No override line: a PR that needs more files must be a different item or `Checklist item: N/A`, which makes the exception visible. This is the pilot's "edit only your leaf" rule made mechanical. Deliverables: `scripts/gates.d/pre/10-pr-scope.sh`, `scripts/gates.d/fixtures/scope/`.

- [ ] H-2: Frozen-statement gate (after: Setup) — `scripts/frozen_targets.txt` lists fully qualified declarations whose **statements** may not change silently: `MoltResearch.IsSignSequence`, `MoltResearch.apSum`, `MoltResearch.BoundedDiscrepancy`, `MoltResearch.erdos_discrepancy`, `MoltResearch.erdos_discrepancy_notBounded`, `MoltResearch.Tao2015.erdos_discrepancy_unconditional`, and every `*Assumption` class. `scripts/FrozenTargets.lean` (run with `lake env lean`) prints each name with its elaborated type (`pp.explicit true`, `pp.universes true`) and `scripts/frozen_targets.snapshot` is the committed output; `scripts/gates.d/post/60-frozen-targets.sh` diffs them and fails unless the PR body carries `Frozen-target change: <name> — <reason>` **and** updates the snapshot. This is LeanMarathon's type freeze at declaration granularity: statement changes become explicit Refiner-style PRs. Deliverables: `scripts/frozen_targets.txt`, `scripts/FrozenTargets.lean`, `scripts/frozen_targets.snapshot`, `scripts/gates.d/post/60-frozen-targets.sh`.

- [ ] H-3: Flagship dependency closure — `scripts/DepClosure.lean` walks the constants reachable from `MoltResearch.Tao2015.erdos_discrepancy_unconditional` (types and values, like `Lean.CollectAxioms` but collecting every constant) and maps them to modules; `scripts/report_closure.py` writes `reports/flagship_closure.md`: modules in the closure and modules under `MoltResearch/` and `Conjectures/C0002_erdos_discrepancy/src` that are **not**, per directory, plus declarations under `MoltResearch/` referenced by no other declaration anywhere (the unused-lemma list). The first deliverable is the measurement, committed; a warning-mode gate that reports **new** orphan modules introduced by a PR follows in a second PR. Deliverables: `scripts/DepClosure.lean`, `scripts/report_closure.py`, `reports/flagship_closure.md`, `scripts/gates.d/post/70-orphans.sh`.

- [ ] H-4: Interface linter to strict — clear the seven current findings: a `Source:` line and a registry entry for `Stage2Assumption` (now an axiom-free compatibility interface; cite `Conjectures/C0002_erdos_discrepancy/notes.md`) and `LittlewoodLBoundAssumption`, and registry entries in `Problems/sources/tao2015_statements.md` for `MatomakiRadziwillAssumption`, `PrimeBlockMajorArcAssumption`, `PrimeQuadrupleCountAssumption`; then flip `python3 scripts/check_interfaces.py --strict` in `.github/workflows/ci.yml` (one line, separate PR). Deliverables: the five interface files' docstrings, `Problems/sources/tao2015_statements.md`, `.github/workflows/ci.yml` (the one line).

- [ ] H-5: Item-dependency check (after: H-3) — `scripts/check_item_dependencies.py`: for a card item that says "proved from `File.lean` (`lemma_a`, `lemma_b`)", the deliverable file's declarations must have `lemma_a` and `lemma_b` in their dependency closure; report cited-but-unused and used-but-uncited (any `MoltResearch.*` constant in the closure not named by the item). Warning mode, run on `Problems/nucleus_upstreaming.md` first. This is LeanMarathon's prose-citation vs elaborated-dependency agreement check, applied to cards. Deliverables: `scripts/check_item_dependencies.py`, `scripts/gates.d/post/75-item-deps.sh`.

- [ ] H-6: Ready-item scheduler — extend `scripts/next_card_item.py`: `--ready` lists the unchecked items of a card whose `(after: …)` prerequisites are all ticked and which have no open PR titled `<id>:` (via `gh pr list`, skipped offline); `--claim <id> --name <name>` creates the branch `<prefix>/<id>-<name>` and the draft PR with the metadata body filled from the card; `--self-test` runs on a fixture card. The generic agent prompt then becomes "run `--ready`, `--claim`, work, `gh pr ready`, repeat". This is LeanMarathon's scheduler for our cards: dependencies as `after:` text on the item, dispatch by whoever asks. Deliverables: `scripts/next_card_item.py`, `scripts/gates.d/fixtures/card/`.

- [ ] H-7: Blocked-report protocol — `Problems/BLOCKED_TEMPLATE.md` (the exact obstruction; the precise statement believed false or unprovable, with the reason; what was tried; the smallest input that would unblock) and `scripts/blocked_prs.py` listing open draft PRs whose body contains a `Blocked:` line — the conductor's card-repair queue. `AGENTS.md` "If you get stuck" points at the template. The stop-report is the mechanism that caught all twelve specification errors to date; this makes its format uniform and its queue visible. Deliverables: `Problems/BLOCKED_TEMPLATE.md`, `scripts/blocked_prs.py`, `AGENTS.md`.

## 4. Order and what is deliberately not adopted

Order: Setup → {H-1, H-2, H-4, H-6, H-7} concurrently → H-3 → H-5. Five items are independent once Setup lands, so this
card is itself the second concurrent run (tooling this time); H-3 → H-5 is the first dependency edge an agent will
have to respect via `after:`.

Not adopted: a custom patch server (our unit of containment is the PR diff plus H-1/H-2, which needs no daemon);
per-role agents (Blueprinter/Worker/Refiner) as fixed identities — the roles exist here as PR kinds (a card PR, an
item PR, a `Frozen-target change:` PR) and any agent may open any kind; `sorry` placeholders in the verified tree —
unfinished mathematics stays an `*Assumption` class in the theorem's type, because that is what keeps main sorry-free
and the open obligations enumerable.

## 5. References

- The comparison that prompted this card (an external review, 2026-09-08) and the assessment in the session log.
- `Problems/nucleus_upstreaming_report.md` — the pilot whose findings 1–4 map onto H-7, H-6, H-6, H-1.
- `Problems/tao2015_a1_r6r7_design_report.md` — Findings E.1–E.8, V-1–V-4 (specification errors caught by stop-reports).
