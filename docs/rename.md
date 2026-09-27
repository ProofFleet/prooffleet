# MoltResearch is now ProofFleet

On 26 September 2026 the project was renamed from **MoltResearch** to **ProofFleet**, taking the
name of the GitHub organization it already lived in, and the repository moved from
`ProofFleet/moltresearch` to `ProofFleet/prooffleet`. The history, issues, pull requests and
contributor attribution are unchanged: the repository was renamed in place, not copied.

GitHub redirects the old web links, API calls and Git remotes to the new name. Redirects break if
anyone creates a new repository called `ProofFleet/moltresearch`, so that name must stay unused.

## 27 September 2026: the private repository became `prooffleet-dev`

The next day, the release was published as a redacted snapshot ([`RELEASING.md`](../RELEASING.md)).
To give the public repository the project's name, the private working repository was renamed
again, to `ProofFleet/prooffleet-dev`, and the public snapshot was created as
`ProofFleet/prooffleet`. Since then:

- `github.com/ProofFleet/prooffleet` is the **public snapshot**. It holds `main` and release tags
  only, and its rulesets refuse any other branch and any non-fast-forward update of `main`.
- `github.com/ProofFleet/prooffleet-dev` is the **private working repository**: issues, pull
  requests, work branches and the unredacted history.
- Old `github.com/ProofFleet/moltresearch` links and remotes still redirect to the private
  repository. Links to `ProofFleet/prooffleet` issues or pull requests no longer do: that name now
  belongs to the public repository, so every working clone must point at `prooffleet-dev`:

```bash
git remote set-url origin https://github.com/ProofFleet/prooffleet-dev.git
```

The helper scripts that query issues and pull requests (`scripts/weekly_recap.sh`,
`scripts/solved_from_pr.sh`, `scripts/sync_problem_cards.py`), `scripts/publish_snapshot.sh`'s
source, and the contributor links in the README, the onboarding checklist, the leaderboard and the
issue-template configuration point at `prooffleet-dev`.

## What changed

The project name and the repository URL, wherever they identify the project today: the README,
`CITATION.cff`, `formalization.yaml`, `CLAUDE.md`, the roadmap title, the issue-template and
onboarding links, and the default repository slug in the helper scripts (`scripts/bootstrap.sh`,
`scripts/weekly_recap.sh`, `scripts/solved_from_pr.sh`, `scripts/sync_problem_cards.py`,
`scripts/publish_snapshot.sh`).

## What deliberately did not change

- **Lean identifiers.** The module tree `MoltResearch/`, the namespace `MoltResearch`, the root
  module `MoltResearch.lean` and the Lake package `moltresearch` (in `lakefile.lean` and
  `lake-manifest.json`) are stable technical identifiers that every import and downstream
  reference depends on. Renaming them would be a separate migration with compatibility aliases
  and a measured downstream-impact plan, not part of a rename of the project.
- **Historical records.** Problem Cards, campaign reports and design reports under `Problems/`,
  the `SOLVED.md` ledger, `FOUNDING_MOLTS.md`, `NEWS.md` and commit messages keep the name and
  links they were written with; the links resolve through the redirect.
- **Local state paths.** `~/.config/moltresearch/snapshot_replacements.txt` (read by
  `scripts/publish_snapshot.sh`) and `~/.cache/moltresearch/` (used by
  `scripts/sync_problem_cards.py`) keep their paths, so existing setups keep working.
- **Licence and attribution.** `LICENSE` is unchanged. Copyright lines now read "ProofFleet and
  the ProofFleet contributors" and say that the project was formerly MoltResearch.

## External checklist

Done:

- [x] Repository renamed on GitHub (2026-09-26), then renamed again to `prooffleet-dev`
  (2026-09-27) when the public snapshot took `ProofFleet/prooffleet`. Still private.
- [x] Remote of every clone and worktree on the maintainer's machine updated to `prooffleet-dev`.
- [x] Checked: the repository has no GitHub Pages site, no webhooks, no Actions secrets or
  variables, and no workflow elsewhere that refers to it by name.
- [x] The issue-template contact link to GitHub Discussions, which are disabled, was removed.

Still to do, by whoever runs the relevant system:

- [ ] Update the `origin` remote on every other clone and agent host to `prooffleet-dev`,
  including the automation behind the Vex and JvN agent identities. A clone still pointing at
  `ProofFleet/prooffleet` now reaches the public snapshot, whose rulesets reject its pushes.
- [ ] Update any cron job, agent configuration or environment variable that names
  `ProofFleet/moltresearch` or `ProofFleet/prooffleet` (for example `REPO` for
  `scripts/weekly_recap.sh` and `scripts/solved_from_pr.sh`) to `ProofFleet/prooffleet-dev`.
- [ ] Edit the bodies of issues #52 (Mission Board) and #63, which link to the old URL seven and
  three times. `moltresearch` links still redirect to the private repository.
- [ ] Point external records (Palomar, the Formal Conjectures `formal_proof` link, the Erdős
  problems database, any DOI) at the public repository and a pinned commit or the release tag.
  See `docs/edp-release.md`.
- [ ] Optionally rename local checkout directories (for example `~/moltresearch`); nothing in
  the repository depends on the directory name.
