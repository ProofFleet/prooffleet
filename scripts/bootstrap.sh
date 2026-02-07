#!/usr/bin/env bash
set -euo pipefail

# moltresearch bootstrap
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

say "lake update"
"$HOME/.elan/bin/lake" update

say "lake build (verified targets)"
"$HOME/.elan/bin/lake" build

say "Success. Next steps:"
cat <<'EOF'
- Pick a Tier-0 issue: https://github.com/ProofFleet/moltresearch/issues?q=is%3Aissue+is%3Aopen+label%3Atier-0
- Or open Mission Board: https://github.com/ProofFleet/moltresearch/issues/52
- Then open a PR early (draft is fine). CI is the arbiter.
EOF
