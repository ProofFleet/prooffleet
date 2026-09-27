#!/usr/bin/env bash
# Produce (or refresh) the public, licensed snapshot of this repository.
#
# The working repository stays where it is; the snapshot is a separate public repository whose
# history is this repository's history passed through a redaction filter (git-filter-repo
# --replace-text), so that anything that must not be published (an old ops note with a phone
# number, say) is replaced in every commit rather than only in the current tree. Only `main` and
# the release tags are pushed: no PR refs, no work branches.
#
# Since 2026-09-27 the working repository is ProofFleet/prooffleet-dev (private) and the snapshot
# is ProofFleet/prooffleet (public). Rulesets on the public repository reject any branch other than
# `main` and any non-fast-forward update of it, so a working clone pushed there by mistake is refused.
#
# Usage:
#   PUBLIC_REPO=ProofFleet/prooffleet scripts/publish_snapshot.sh [--dry-run]
#   PUBLIC_REPO=OWNER/NAME scripts/publish_snapshot.sh [--create] [--dry-run]
#
#   --create    create $PUBLIC_REPO as a public GitHub repository first (gh repo create)
#   --dry-run   build the filtered mirror and report, but push nothing
#
# Redactions are read from $SNAPSHOT_REPLACEMENTS (default ~/.config/moltresearch/snapshot_replacements.txt),
# one `literal==>replacement` per line in git-filter-repo's --replace-text format. The file is
# deliberately NOT part of the repository: it contains the very strings that must not be published.
# Requires: git, gh (authenticated), git-filter-repo (pip install --user git-filter-repo).
set -euo pipefail

SOURCE_REPO="${SOURCE_REPO:-https://github.com/ProofFleet/prooffleet-dev.git}"
PUBLIC_REPO="${PUBLIC_REPO:-}"
REPLACEMENTS="${SNAPSHOT_REPLACEMENTS:-$HOME/.config/moltresearch/snapshot_replacements.txt}"
CREATE=0; DRY=0
for a in "$@"; do case "$a" in --create) CREATE=1;; --dry-run) DRY=1;; *) echo "unknown flag $a" >&2; exit 2;; esac; done

command -v git-filter-repo >/dev/null || { echo "git-filter-repo not found (pip install --user git-filter-repo; ensure ~/.local/bin is on PATH)" >&2; exit 1; }
[[ -f "$REPLACEMENTS" ]] || { echo "redaction file not found: $REPLACEMENTS" >&2; exit 1; }
if [[ "$DRY" == 0 && -z "$PUBLIC_REPO" ]]; then echo "PUBLIC_REPO=OWNER/NAME is required unless --dry-run" >&2; exit 2; fi
if [[ -n "$PUBLIC_REPO" && "${SOURCE_REPO%.git}" == "https://github.com/$PUBLIC_REPO" ]]; then
  echo "SOURCE_REPO and PUBLIC_REPO are the same repository ($PUBLIC_REPO)" >&2; exit 2
fi

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
echo "== cloning $SOURCE_REPO (bare: branches and tags only, no PR refs)"
git clone -q --bare "$SOURCE_REPO" "$WORK/mirror.git"
cd "$WORK/mirror.git"
# BSD wc (macOS) pads its count with spaces; strip them before comparing.
count() { wc -l | tr -d '[:space:]'; }
echo "== filtering history with $(count < "$REPLACEMENTS") redaction rule(s)"
git filter-repo --replace-text "$REPLACEMENTS" --force >/dev/null
echo "== verifying every redacted literal is gone from every commit"
while IFS= read -r rule; do
  [[ -z "$rule" || "$rule" == \#* ]] && continue
  lit="${rule%%==>*}"; lit="${lit#literal:}"
  n="$(git log --all --oneline -S"$lit" | count)"
  if [[ "$n" != 0 ]]; then echo "REDACTION FAILED: '$lit' still in $n commit(s)" >&2; exit 1; fi
done < "$REPLACEMENTS"
echo "   ok: $(git rev-list --all | count) commits, $(git tag | count) tags, main at $(git rev-parse --short main)"
if [[ "$DRY" == 1 ]]; then echo "== dry run: nothing pushed"; exit 0; fi

if [[ "$CREATE" == 1 ]]; then
  echo "== creating public repository $PUBLIC_REPO"
  gh repo create "$PUBLIC_REPO" --public --description "ProofFleet public snapshot: collaborative mathematical research with machine-checked proofs (Lean 4), including a formalization of the Erdős discrepancy theorem" >/dev/null
fi
echo "== pushing main and tags to $PUBLIC_REPO"
git push -q "https://github.com/$PUBLIC_REPO.git" "+refs/heads/main:refs/heads/main"
git push -q "https://github.com/$PUBLIC_REPO.git" --tags --force
echo "== done: https://github.com/$PUBLIC_REPO"
