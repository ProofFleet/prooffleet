#!/usr/bin/env bash
set -euo pipefail

# Preflight checks for MoltResearch contributors.
# Fast by default. Run with --ci to also run `make ci`.

DO_CI=0
if [[ "${1:-}" == "--ci" ]]; then
  DO_CI=1
fi

fail=0
say_ok()   { echo "OK: $*"; }
say_warn() { echo "WARN: $*"; }
say_err()  { echo "ERROR: $*"; fail=1; }

REPO_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$REPO_ROOT"

# Toolchain
LAKE="$HOME/.elan/bin/lake"
if [[ -x "$LAKE" ]]; then
  say_ok "lake found at $LAKE"
else
  say_err "lake not found at $LAKE (install elan, or set up Lean toolchain)"
fi

if command -v git >/dev/null 2>&1; then
  say_ok "git: $(git --version)"
else
  say_err "git not found"
fi

if command -v make >/dev/null 2>&1; then
  say_ok "make found"
else
  say_err "make not found"
fi

# GitHub auth (optional but recommended)
if command -v gh >/dev/null 2>&1; then
  if gh auth status -h github.com >/dev/null 2>&1; then
    say_ok "gh authenticated"
  else
    say_warn "gh installed but not authenticated (PR automation will not work). Run: gh auth login"
  fi
else
  say_warn "gh not installed (fine for local-only work)"
fi

# Quick sanity build (optional)
if [[ "$DO_CI" == "1" ]]; then
  echo "Running: make ci (this may take a while)"
  make ci
  say_ok "make ci passed"
else
  echo "Tip: run './scripts/preflight.sh --ci' to run full CI-equivalent checks locally."
fi

if [[ "$fail" == "1" ]]; then
  echo "Preflight failed." >&2
  exit 1
fi

echo "Preflight OK."
