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
   discrepancy release is to be tagged `v1.0.0-edp`; no release tag existed as of 2026-09-26.
   Add `version` and `date-released` to `CITATION.cff` in the tagged commit.
3. Redaction rules live outside the repository, in
   `~/.config/moltresearch/snapshot_replacements.txt` (git-filter-repo `--replace-text` format, one
   `literal==>replacement` per line). Never commit that file.
4. Dry run: `scripts/publish_snapshot.sh --dry-run` — clones, filters, verifies every redacted
   literal is absent from every commit, pushes nothing.
5. Publish: `PUBLIC_REPO=OWNER/NAME scripts/publish_snapshot.sh --create` the first time,
   without `--create` afterwards.
6. External links (formal-conjectures `formal_proof`, the Erdős problems database, Zenodo, the
   Palomar registry) must point at the **public** repository, pinned to a commit or tag, never at
   this one. A snapshot rewrites history, so its commit SHAs differ from this repository's: pin
   the snapshot's SHA.

The Palomar submission of the Erdős discrepancy theorem has its own checklist, verification
record and decision list in [`docs/edp-release.md`](docs/edp-release.md). The repository was
renamed from `moltresearch` to `prooffleet` on 2026-09-26 ([`docs/rename.md`](docs/rename.md));
the redaction file keeps its historical path.

## What a release certifies

`make ci` green on the tagged commit: every target in `scripts/ci_targets.txt` builds, no
`sorry`/`axiom`/`unsafe` anywhere under `MoltResearch/`, `Solutions/` or `PalomarEDP/` (apart
from the Challenge's one statement hole), and the audit pins in
`Conjectures/C0002_erdos_discrepancy/src/TrackCAxiomAudit.lean` hold (`erdos_discrepancy` and
`erdos_discrepancy_unconditional` depend on `[propext, Classical.choice, Quot.sound]` only, as
does `EDP.erdos_discrepancy` in `PalomarEDP/Solution.lean`).
Anyone can re-check with `./scripts/bootstrap.sh && make ci` on the pinned toolchain.
