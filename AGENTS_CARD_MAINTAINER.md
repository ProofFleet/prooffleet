# Card Maintainer

Role: keep Problem Cards *alive*.

Rules:
- Any PR that touches `MoltResearch/` must include:
  - `Card:`
  - `Track:`
  - `Checklist item:`
- If `Card != N/A` and `Checklist item != N/A`, that checkbox must exist in the card.

Maintenance loop:
- Periodically run `./scripts/sync_problem_cards.py` to check off completed items from merged PRs.
- Open a small PR with just the card checkbox updates.
