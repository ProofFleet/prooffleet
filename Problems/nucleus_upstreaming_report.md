# Nucleus upstreaming pilot — run report (2026-09-08)

Card: `Problems/nucleus_upstreaming.md`. This is the record of the first run in which several agents worked one card concurrently
with the card and CI as the only coordination: no per-item briefs, no conductor-written code, no code review.

## 1. What was tested

The repository's operating claim is "CI is the forum": a Problem Card decomposed into independent checkbox items, each with a
pre-allocated leaf file, should let N agents work it at once with no coordination beyond (a) claiming by draft PR and (b) CI on
`main`. The Track R campaign (#3044, closed today) was run by one conductor writing briefs for one Codex worker at a time; this run
asks whether the substrate holds up when the conductor does nothing but merge.

Setup (one PR, `c1e7…` → `#3711`-era main): the card with six items (UP-1..UP-6, each a Mathlib-idiom restatement of a result the
campaign proved in repository-specific form), six empty leaf files under `MoltResearch/Discrepancy/Upstream/`, one aggregator
`MoltResearch/DiscrepancyUpstream.lean`, one line in `scripts/ci_targets.txt`. Three Codex agents (`gpt-5.6-sol`, reasoning
effort `high`, names ada/bob/cyd) were launched at 07:14Z in three git worktrees with the same generic prompt: read `AGENTS.md`
and the card, pick an unclaimed item, claim it, implement only your leaf, run the listed checks, mark the PR ready, take another;
if blocked, keep the draft open and write the exact obstruction in the PR body. The conductor merged on green and ticked boxes.

## 2. Timeline (UTC)

| time | event |
|---|---|
| 07:14 | three agents launched |
| 07:15:47 | bob opens draft #3712 (UP-3) |
| 07:15:56 | ada opens draft #3713 (UP-3) — claim race, 9 s apart |
| 07:16:23 | ada closes #3713 (detected bob's earlier claim), moves on |
| 07:17:00 | ada opens draft #3714 (UP-1) |
| 07:18:21 | cyd opens draft #3715 (UP-2) |
| 07:20:05 | ada opens draft #3716 (UP-5) — UP-1 left as a blocked draft |
| 07:20:25 | #3712 (UP-3) ready |
| 07:21:11 | bob opens draft #3717 (UP-6) |
| 07:23:16 | #3712 merged (`c12b378f`) |
| 07:24:17 / 07:25:26 / 07:25:46 | #3716 (UP-5), #3717 (UP-6), #3715 (UP-2) ready |
| 07:24:57 | ada opens draft #3719 (UP-4) |
| 07:26:14 / 07:27:48 / 07:28:04 | #3716, #3715, #3717 merged (`fa93cab1`, `24edf5c2`, `17e48159`) |
| 07:26:56 / 07:27:59 | cyd, bob exit (no unclaimed items left) |
| 07:29:32 | #3719 (UP-4) ready |
| 07:30:02 | ada exits |
| 07:33:53 | #3719 merged (`a1ff8bb2`) |

## 3. Metrics

| measure | value |
|---|---|
| items merged / items on the card | 5 / 6 |
| wall-clock, launch → last merge | 19.9 min |
| agent wall-clock (launch → last agent exit) | 16 min |
| per-item agent time (draft opened → ready) | 4.2, 4.3, 4.6, 4.6, 7.4 min |
| merge conflicts / rebases needed | 0 / 0 |
| CI runs on pilot branches, all green | 12 / 12 |
| first-submission CI pass on the final content | 5 / 5 |
| CI duration per run (min:sec) | 1:54 – 3:57; median ≈ 2:35 |
| files touched per merged PR | 1 (its own leaf), 314 added lines in total, 0 deletions |
| conductor-written briefs / code / review comments | 0 / 0 / 0 |
| conductor actions | 6 squash-merges (5 items + 1 tick PR), this close-out PR |
| card defects found by agents | 1 (UP-1, recorded in #3714) |
| claim races | 1 (UP-3, resolved by the loser in 27 s) |

Serial comparison (estimate, not measured): a single agent would need the sum of the per-item times, about 25 min of agent time,
plus one CI wait and merge per item that it cannot overlap with its own next item without the conductor, so roughly 35–40 min for
the same five items. The measured 20 min is bounded below by the conductor's merge latency (2–4.4 min per PR) and by three agents
sharing six items; more agents on this card would not have helped much, more items would.

## 4. Protocol findings

1. **The card can be wrong, and the agent is the one who finds out.** UP-1 asked for a two-sided Mertens-first restatement from
   two named files. The tree has only the upper bound (`sum_log_div_primesBelow_le_sharp`) and an *unweighted* lower bound
   (`log_log_le_sum_one_div_primesBelow`); no weighted lower bound exists anywhere in `MoltResearch/`. ada did exactly what the
   rules ask: kept the draft (#3714), wrote the exact obstruction in the body, took another item. The card is now corrected
   (UP-1a restatement, UP-1b new proof). This is the same failure class as Findings E.1–E.7 and V-1–V-4 of Track R (a
   conductor-written specification that is false or under-supplied), caught the same way, by the worker's stop report.
2. **The one-item-at-a-time rule was not enforced by anything.** ada held the blocked UP-1 draft while claiming UP-5 and later UP-4.
   This was the right behaviour; the rule text was wrong. Fixed on the card: a blocked draft does not count as active.
3. **Claim races exist and are cheap.** "Check `gh pr list` then open a draft" has a window of a few seconds; two agents hit it on
   UP-3. The loser noticed on its next check and closed within half a minute. At this scale no lock is needed; at tens of agents a
   first-come label or a claim file would be worth adding.
4. **Pre-allocated leaves made conflicts impossible by construction.** No PR touched a shared file; the aggregator and the CI
   target were wired by the setup PR. This is the design choice that carries the weight, and it costs the conductor one setup PR
   per card.
5. **CI was the only reviewer and it was enough for this class of item.** Every gate (no `sorry`/`axiom`/`unsafe`, layering,
   aggregator coverage, PR metadata, build of the changed cone only) ran in under four minutes per PR, so the agents' own local
   checks plus CI closed the loop without a human or conductor reading Lean.

## 5. What this does and does not show

It shows: with a card whose items are independent and whose leaves are pre-allocated, three agents worked concurrently with
zero coordination cost, zero conflicts and a 100 % first-pass CI rate, and the one defective item was detected and reported
rather than worked around. It does not show: behaviour under dependencies between items (none here), at tens of agents, or on
items that need new mathematics rather than restatements (UP-1b is the first such item and is open). Those are the next
experiments.
