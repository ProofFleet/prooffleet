# Releasing a public snapshot

The working repository is private and its history contains things that were never meant for
publication (an old ops note with a phone number). Rather than rewriting this repository's history
(which GitHub's pull-request refs would preserve anyway), releases are published as a **separate
public repository** produced by `scripts/publish_snapshot.sh`: a bare clone of this repository's
`main` and tags, passed through a redaction filter, then pushed. Re-running the script refreshes it.

## Steps

1. Make sure `main` is green and carries `LICENSE` (Apache-2.0), `CITATION.cff` and the README
   license section.
2. Tag the release here: `git tag -a vX.Y.Z -m "..." && git push origin vX.Y.Z`. The Erdős
   discrepancy milestone is tagged `v1.0.0-edp` (see the tag message for what it certifies).
3. Redaction rules live outside the repository, in
   `~/.config/moltresearch/snapshot_replacements.txt` (git-filter-repo `--replace-text` format, one
   `literal==>replacement` per line). Never commit that file.
4. Dry run: `scripts/publish_snapshot.sh --dry-run` — clones, filters, verifies every redacted
   literal is absent from every commit, pushes nothing.
5. Publish: `PUBLIC_REPO=OWNER/NAME scripts/publish_snapshot.sh --create` the first time,
   without `--create` afterwards.
6. External links (formal-conjectures `formal_proof`, the Erdős problems database, Zenodo) must
   point at the **public** repository, pinned to a commit or tag, never at this one.

## What a release certifies

`make ci` green on the tagged commit: every target in `scripts/ci_targets.txt` builds, no
`sorry`/`axiom`/`unsafe` anywhere under `MoltResearch/` or `Solutions/`, and the audit pins in
`Conjectures/C0002_erdos_discrepancy/src/TrackCAxiomAudit.lean` hold (`erdos_discrepancy` and
`erdos_discrepancy_unconditional` depend on `[propext, Classical.choice, Quot.sound]` only).
Anyone can re-check with `./scripts/bootstrap.sh && make ci` on the pinned toolchain.
