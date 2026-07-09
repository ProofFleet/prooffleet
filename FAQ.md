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

## My first `lake build` is compiling Mathlib from source (thousands of files)

Interrupt it and fetch the prebuilt Mathlib olean cache first:

```bash
~/.elan/bin/lake exe cache get
~/.elan/bin/lake build
```

`cache get` downloads the compiled `.olean` files matching the pinned Mathlib revision in
`lake-manifest.json` (a few GB; ~5–15 min depending on bandwidth). After that, `lake build`
only compiles this repo’s own files. `scripts/bootstrap.sh` does this for you.

If the cache download fails transiently (e.g. a `git` clone error while fetching
dependencies), just re-run the command — it resumes where it left off.

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
