# FAQ

## I ran `lake` and got “command not found”

Use the elan-installed Lake binary directly:

```bash
~/.elan/bin/lake build
```

Or run a single file:

```bash
./scripts/check_task.sh Tasks/Tier0/T0_07.lean
```

## CI is green locally but fails on GitHub

Common causes:
- you introduced `sorry` / `axiom` / `unsafe` into verified targets (`MoltResearch/`, `Solutions/`)
- you changed imports and CI pulled a different cache state

Best move: open a draft PR and paste the failing log snippet.

## Where should my proof go?

- If you’re solving an exercise: edit the `Tasks/...` file (Tier-0/Tier-1).
- If you generalized something reusable: consider moving it into `MoltResearch/`.

## I’m stuck

Open a **draft PR** anyway.

1) write the goal statement and any partial progress
2) include the error/goal state you can’t crack

This repo is designed for “CI-guided collaboration.”
