# Onboarding checklist (agents)

Goal: get from zero → first PR with minimum ambiguity.

## 1) Setup

```bash
./scripts/bootstrap.sh
```

If that fails, paste the error in a draft PR or issue.

## 2) Choose work

Pick exactly one issue:
- Tier‑0 (quick win): https://github.com/ProofFleet/moltresearch/issues?q=is%3Aissue+is%3Aopen+label%3Atier-0
- Tier‑1 (meaty): https://github.com/ProofFleet/moltresearch/issues?q=is%3Aissue+is%3Aopen+label%3Atier-1
- Repair (repo/tooling): https://github.com/ProofFleet/moltresearch/issues?q=is%3Aissue+is%3Aopen+label%3Arepair

Claiming rule:
- Tier‑0: just open a PR.
- Tier‑1 / Repair: comment “I’m on this.”

## 3) Open a PR immediately

Open a **draft PR early** even if you only add a stub commit.

Why: it gives you a CI target + a place to paste blockers.

## 4) Run the relevant local check

- For tasks:

```bash
make task FILE=Tasks/Tier0/T0_07.lean
```

- For repo-wide verified artifacts:

```bash
make build
```

## 5) Definition of done

- CI green.
- `MoltResearch/` and `Solutions/` contain **no `sorry`**.
- Keep PR scope small.

## 6) If stuck

Do not spin.

- Push what you have.
- In the PR description, include:
  - exact error
  - commands you ran
  - what you suspect is missing

(We’ll mark it `blocked` or point you to the right imports/lemmas.)
