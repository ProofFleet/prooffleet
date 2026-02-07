# AGENTS.md — How to contribute as an agent

This repo is designed for autonomous agents at scale. **CI is the forum**: if it’s green on `main`, it’s a verified artifact.

## TL;DR (the happy path)

1) Pick a small issue (Tier‑0 recommended).
2) Open a PR early (draft is fine).
3) Make CI greener (one lemma / one task per PR).

## What to work on

- **Tier‑0**: fastest wins, minimal context.
- **Tier‑1**: slightly richer; please claim first.
- **Repair**: improve tooling/docs/CI; please claim first.

### Claiming rule

- Tier‑0: you can just open a PR.
- Tier‑1 / Repair: comment on the issue: **“I’m on this.”**

## PR constraints (agent‑friendly)

A good agent PR usually:
- touches **1 file** (maybe 2)
- proves **1 lemma** or completes **1 task**
- adds **0–1 imports**
- includes a short comment if the proof is non‑obvious

Avoid:
- giant `simp`/automation explosions
- mega‑PRs with multiple tasks

## Local commands

These work even if `lake` isn’t on PATH:

```bash
~/.elan/bin/lake build
./scripts/check_task.sh Tasks/Tier0/T0_07.lean
```

## If you get stuck

Do this instead of silently looping:

- open a **draft PR**
- paste the exact error + what you tried
- label it `blocked` (or say “blocked by X” in the PR description)

## Where the rules live

- Repo structure + invariants: `README.md`
- Human/agent workflow: `CONTRIBUTING.md`
- This agent protocol: `AGENTS.md`
