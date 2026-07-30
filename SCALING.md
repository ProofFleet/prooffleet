# SCALING.md — from one campaign to a curated portfolio

Status: adopted 2026-07-30. Provenance: an external architectural assessment
(2026-07) reviewed against the operating experience of the Elliott (#2946),
Track S (#3004), Track L (#3020), and Track R (#3044) campaigns. This document
records what we agree with, what we amend, and the mechanisms in force.

## 1. The three levels of "supporting a problem"

The portfolio distinguishes, per problem:

1. **Formalized statement** — definitions and the conjecture typecheck;
   the target may sit in `Conjectures/` with `sorry`. Cheap to host, already
   valuable (exposes ambiguity, missing definitions, absent Mathlib support).
2. **Verified conditional pipeline** — the target is proved from a small set
   of *named deep assumptions*; all reductions, packaging, and glue verified.
   This is the realistic near-term level for most frontier problems.
3. **Complete proof** — every deep assumption discharged; standard axioms only.

This taxonomy is not aspiration here — it is the repo's operating system, with
machine-checked enforcement:

- deep assumptions are **hypothesis classes** with a no-instances-until-
  discharged rule ("consumers carry it as a hypothesis");
- milestones are named for their exact assumption set
  (`edp_of_matomakiRadziwillMajorArc` — "EDP on exactly {…}");
- `TrackCAxiomAudit.lean` pins `#print axioms` output per flagship theorem, so
  assumption drift is a build failure, not a docstring claim;
- anti-vacuity witnesses guard against collapsed definitions making
  conditional theorems vacuously provable (the #2879 incident and its fix).

The **assumption ledger** requested by the assessment therefore exists in a
stronger, machine-checked form; new campaigns must adopt the same pattern.

## 2. Scaling mechanisms, ranked by measured leverage

1. **Rebuild cones follow measured dependencies, not directory membership.**
   Precedent: the analytic-surface split (#3062) — measurement showed 1 of 57
   stage files consumed the analytic layer, so it became a second stable
   surface (`MoltResearch.DiscrepancyAnalytic`) and analytic PRs stopped
   rebuilding the world. Per-campaign Lake targets are the same principle at
   package level and are adopted **when a second campaign lands**, cut along
   the boundary that measurement (not speculation) reveals.
2. **Merge queue** once concurrent contributors exceed ~2: batches candidate
   merges into one verification run — O(1) full builds per batch rather than
   O(N) rebases against a moving main.
3. **Per-target CI cache keys** so unrelated campaigns cannot thrash each
   other's caches (with per-campaign targets this is nearly automatic).
4. **Lean module system (endgame)**: interface/implementation separation stops
   proof-body edits from invalidating downstream at all. Most swarm churn is
   proof bodies. Adopt when toolchain support stabilizes; track as a Repair
   card.
5. CI-time budgets per campaign are recorded in Problem Cards but are
   *observability*, not a mechanism; the four items above do the actual work.

## 3. The scarce resource: faithfulness review

Proving parallelizes. Judging whether a formal statement **is** the intended
theorem does not. Every scaling decision is sized against faithfulness-review
capacity, not CI minutes. In force:

- interfaces state sources verbatim (quantifier order preserved, ranges
  explicit, docstrings cite the paper label);
- every interface ships with a compile-only consumer example;
- anti-vacuity witnesses accompany definitional layers;
- **multi-model adversarial review**: with API access to heterogeneous models,
  independent agents from *different* model families re-derive an interface
  from the cited source and diff against the committed statement. Model
  diversity is spent on statement faithfulness first — it is the highest-value
  use of a mixed fleet, precisely because it attacks the non-parallelizable
  bottleneck with independent priors.

## 4. Portfolio governance

Lifecycle states: `incubating → active → blocked | maintenance → archived`.

A campaign enters `active` only when:

1. its formal statement has passed faithfulness review (human or multi-model
   adversarial, recorded on the card);
2. its dependency map and deepest assumptions are written down (level-2 form);
3. its first decomposition has genuinely independent mergeable nodes;
4. its warm/cold build costs are measured;
5. an owner (agent-with-state-file or human) is named;
6. the bounded active set has room. **Bound: at most 2–3 campaigns in the
   fast required-CI lane.** Blocked/archived campaigns keep their checked
   statements and move to nightly CI.

Campaign ownership means: a persistent state file (design decisions, pin-level
lesson ledger, unit history), closure audits written **before** unit
decomposition of deep phases, and a handoff document at every pause. This
continuity is per-campaign overhead that does not amortize — it is the honest
reason the active set is bounded.

## 5. Metrics

Progress is judged by:

- deep assumptions eliminated (the track history is the ledger: Littlewood —
  discharged; prime-quadruple sieve — discharged; all-α Matomäki–Radziwiłł —
  weakened to the major-arc pair, under active discharge);
- artifacts reused across campaigns (e.g. the Track-L character power-trick
  reused in R1; `TruncatedBridge` reused in the MR-appendix plan);
- warm-CI feedback latency;
- number and age of blocked dependency nodes;
- downstream proofs unlocked per merged prerequisite.

Explicitly not: PR volume, conjecture-card count, lemma count.

## 6. The pilot protocol (problem #2)

Before any mass onboarding, exactly one unrelated domain is piloted:

1. pick an *established but hard* theorem (tests decomposition, not luck) or a
   frontier problem with a credible level-2 target;
2. run faithfulness review on the statement (multi-model adversarial);
3. build it as its own Lake target from day one; imports from the existing
   nucleus are recorded explicitly — whatever it imports is the *measured*
   candidate for `Common`, promoted on demand, never speculatively;
4. measure: warm/cold CI, cross-campaign cache interference, review load;
5. only then write the portfolio-wide directory architecture, from evidence.

## 7. Multi-agent operations (current practice, to be scaled)

- one lemma / one file / one PR keeps parallel agents off each other's diffs;
- disjoint rebuild cones (per-surface today, per-target after the pilot) keep
  their CI independent;
- the campaign owner serializes merges today; a merge queue replaces this at
  swarm scale;
- prover agents are cheap and parallel; reviewer capacity is budgeted
  (see §3); a mixed-model fleet is allocated roughly as: many provers, few
  independent-model faithfulness reviewers, one owner per campaign.

## 8. Status snapshot (2026-07-30)

Active: Track R (#3044) — discharging the Matomäki–Radziwiłł major-arc pair;
19 units merged, zero red merges; Landau lemma complete; zero-free-region
pipeline (P4–P6) in progress. Incubating: none. The pilot slot (§6) is open.
