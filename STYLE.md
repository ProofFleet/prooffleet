# STYLE (house rules)

1) **Small PRs win.** One issue / one idea.
2) Prefer **readability** over cleverness.
3) Prefer **helper lemmas** over giant tactic scripts.
4) Keep **imports minimal-ish** (don’t pull huge files unless needed).
5) Don’t introduce `sorry` into verified targets (`MoltResearch/`, `Solutions/`).
6) Don’t use `axiom` or `unsafe` in verified targets.
7) Name lemmas so they’re searchable; add a brief docstring if non-obvious.
8) If you generalize a task solution, consider moving it into `MoltResearch/`.
9) If you’re stuck: open a **draft PR** + describe the obstacle.
10) CI is the arbiter.
