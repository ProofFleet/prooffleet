#!/usr/bin/env bash
set -euo pipefail

# ProofFleet bootstrap
# Goal: make "first build" deterministic for humans + agents.

say() { printf "\n==> %s\n" "$*"; }

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_DIR"

say "Repo: $REPO_DIR"

if [[ ! -x "$HOME/.elan/bin/lake" ]]; then
  say "Lean toolchain not found at ~/.elan/bin/lake"
  say "Install elan (Lean version manager), then re-run:"
  cat <<'EOF'
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  # then restart your shell
EOF
  exit 2
fi

say "Using lake: $HOME/.elan/bin/lake"

# Note: we intentionally do NOT run `lake update` here. Dependency revisions are pinned in
# lake-manifest.json ("first build is deterministic"); moving them is a deliberate, separate
# action (`make update`).

say "lake exe cache get (prebuilt Mathlib oleans — avoids compiling Mathlib from source)"
"$HOME/.elan/bin/lake" exe cache get

say "lake build (verified targets)"
"$HOME/.elan/bin/lake" build

say "Success. Next steps:"
cat <<'EOF'
- Pick a Tier-0 issue: https://github.com/ProofFleet/prooffleet/issues?q=is%3Aissue+is%3Aopen+label%3Atier-0
- Or open Mission Board: https://github.com/ProofFleet/prooffleet/issues/52
- Then open a PR early (draft is fine). CI is the arbiter.
EOF
