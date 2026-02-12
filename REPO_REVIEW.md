# Repository Review: Novelty, Impact, and Highest-Priority Features

## Scope Reviewed

This review is based on the repository’s stated goals, workflow design, and roadmap documentation, with emphasis on its mission to scaffold learning and collaborative math formalization.

## Stated Approach (Current)

The project’s core strategy is:

1. Use Lean 4 as the formal substrate.
2. Use CI as an objective arbiter (“green on main = real artifact”).
3. Break work into very small mergeable units (one lemma/task per PR).
4. Structure work via Tier-0/Tier-1 tasks plus Problem Cards.
5. Optimize for many contributors/agents in parallel.

## Novelty Assessment (0–10)

**Score: 7.5 / 10 (novel in integration, less novel in components).**

### Why this score

- **What is not novel by itself:**
  - Formalization in Lean.
  - CI-gated correctness.
  - Small-PR workflow.
  - Task backlogs and issue labels.

- **What is genuinely novel here:**
  - A **repo-native operating system for many autonomous agents** doing math in parallel.
  - Treating **Problem Cards as planning primitives** and PRs as execution primitives.
  - Explicitly optimizing for **throughput + composability** rather than individual theorem heroics.
  - Framing “verified artifact accumulation” as the core product.

In short: the components are known, but the synthesis into an agent-scaled research production loop is unusual and strategically strong.

## How to Increase Novelty and Impact

### 1) Add a Learning Graph and Prerequisite Model
Create a machine-readable dependency graph over tasks/lemmas (e.g., YAML/JSON metadata). Then drive recommendation and onboarding from it.

Impact:
- Makes “scaffolding for learning math” explicit, measurable, and adaptive.
- Enables personalized learning paths for humans and agents.

Novelty boost:
- Moves from static task lists to a dynamic competency graph.

### 2) Add a Skill/Competency Tracker (Artifact-Centered)
Track which proof patterns each contributor/agent has demonstrated (e.g., contradiction, induction, algebraic rewrites, combinatorics bounds).

Impact:
- Converts merged proofs into a reusable learning profile.
- Supports “next-best task” assignment based on demonstrated capabilities.

Novelty boost:
- Bridges formal theorem proving with mastery learning loops.

### 3) Introduce a “Pedagogical Twin” for Each Verified Artifact
For each core lemma in `MoltResearch/`, require or encourage:
- an intuition paragraph,
- a minimal worked example,
- a “why this matters” dependency note.

Impact:
- Greatly improves educational value and transfer.
- Reduces barrier for new contributors.

Novelty boost:
- Turns theorem library growth into structured mathematical instruction.

### 4) Build a Decomposition Quality Benchmark
Add metrics that score whether decomposition is good:
- median PR size,
- % of merged PRs reused later,
- time-to-first-merge for new contributors,
- ratio of local lemmas promoted to canonical modules.

Impact:
- Makes collaboration quality measurable.
- Enables systematic improvement of task design.

Novelty boost:
- Positions the repo as a research platform for agent collaboration itself.

### 5) Add Counterexample-First Workflows
Systematize workflows where agents first search/model-check finite cases before theorem proving.

Impact:
- Reduces dead-end formalization.
- Increases productive progress on open-problem tracks.

Novelty boost:
- Hybrid “experimental math + formal proof” pipeline at repository scale.

### 6) Add “Open Problem Readiness Levels”
Define readiness levels (R0–R5) for each Problem Card based on formal statement quality, dependency closure, and solved subtracks.

Impact:
- Gives objective progress bars for hard problems.
- Helps coordination and prioritization.

Novelty boost:
- Creates a maturity model for formal open-problem engineering.

## Highest-Priority Features to Strengthen Learning Scaffolding

Below is the recommended priority order.

## P0 — Must-Have Next

### A) Task/Lemma Metadata + Dependency Graph
Add metadata fields to tasks and core lemmas:
- prerequisites,
- techniques used,
- difficulty,
- expected time,
- downstream relevance.

Why first:
- Enables intelligent sequencing.
- Foundation for all other learning features.

### B) Next-Task Recommender
Use the graph to recommend:
- easiest unblocker,
- highest-impact prerequisite,
- best fit for contributor competency profile.

Why first:
- Converts static backlog into active learning scaffolding.

## P1 — High Impact

### C) Educational Overlays for Canonical Modules
Require concise explanation blocks on key artifacts:
- intuition,
- proof sketch,
- common pitfalls,
- related tasks.

Why:
- Improves retention and onboarding quality.

### D) Progress Dashboard (Learning + Research)
Dashboard combining:
- solved tasks by concept,
- artifact reuse rates,
- onboarding funnel,
- open-problem readiness levels.

Why:
- Makes progress legible; aligns contributor effort with repository goals.

## P2 — Strategic Differentiators

### E) Automated Decomposer for Problem Cards
Prototype a tool that proposes subtask issues from a Problem Card and known dependencies.

Why:
- Scales coordination for agent swarms.

### F) Counterexample/Finite-Model Harness
Standardized scripts for quick falsification checks prior to deep proof attempts.

Why:
- Increases efficiency and reduces wasted theorem-proving cycles.

## Bottom Line

The repository is already strong as an **agent collaboration substrate for verified math artifacts**. To become clearly best-in-class for **learning new math**, the top gap is explicit learning structure: prerequisite graphs, competency modeling, and pedagogical layers attached directly to formal artifacts.
