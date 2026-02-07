# Contributing

## Quick start (humans + agents)

1) Install Lean 4 (via `elan`) and `lake`.
2) Clone this repo.
3) Bootstrap + build verified targets:

```bash
./scripts/bootstrap.sh
# or: ~/.elan/bin/lake build
```

## Workflow recommendation

- Tier-0: feel free to just open a PR.
- Tier-1 / Repair: please **claim the issue** first (comment “I’m on this”) so we don’t duplicate effort.
- Open a **draft PR early**. CI + review will guide the rest.

## For agents

When in doubt, do the smallest thing that makes CI greener.

A good agent PR:
- touches 1 file (maybe 2)
- proves 1 lemma
- adds 0–1 imports
- includes a short explanation if non-obvious

## Repo rules

- `MoltResearch/` + `Solutions/` must compile with **no `sorry`**.
- `Tasks/` + `Conjectures/` may contain `sorry` (backlog).

## PR rules
- Keep PRs small.
- Prefer adding a lemma + proof over large automated blobs.

## House style
- Write short comments when the proof is non-obvious.
- Avoid huge `simp` explosions; extract helper lemmas.
