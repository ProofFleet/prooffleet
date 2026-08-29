#!/usr/bin/env bash
# Forbid `axiom` / `unsafe` declarations in the verified trees.
#
# The check is comment-aware. A plain line-anchored grep also matches prose that happens to
# begin a wrapped docstring line with the word "axiom" — e.g. TrackCStage5Core.lean's
# "axiom audit pins the footprint to standard axioms" — and identifier shape does not
# discriminate, since "audit" is itself a valid identifier. So we track Lean block-comment
# depth (`/- … -/`, which includes `/-!` and `/--`) and only consider lines that begin
# outside a comment.
#
# Usage: forbid_axiom_unsafe.sh [tree ...]   (default: the verified trees)

set -uo pipefail

trees=("$@")
if [ "${#trees[@]}" -eq 0 ]; then
  trees=(MoltResearch Solutions)
fi

allowlist="scripts/axiom_allowlist.txt"

hits=$(
  find "${trees[@]}" -name '*.lean' -type f -print0 2>/dev/null |
    xargs -0 -r awk '
      FNR == 1 { depth = 0 }
      {
        line = $0
        # A declaration must start outside any block comment.
        if (depth == 0 && line ~ /^[[:space:]]*(axiom|unsafe)[[:space:]]/) {
          printf "%s:%d:%s\n", FILENAME, FNR, line
        }
        # Update block-comment depth: count "/-" openers and "-/" closers.
        rest = line
        while ((i = index(rest, "/-")) > 0) { depth++; rest = substr(rest, i + 2) }
        rest = line
        while ((i = index(rest, "-/")) > 0) { depth--; rest = substr(rest, i + 2) }
        if (depth < 0) depth = 0
      }
    '
)

# Drop allowlisted declarations (file:line entries, one per line, # comments allowed).
if [ -n "$hits" ] && [ -f "$allowlist" ]; then
  while IFS= read -r raw; do
    entry="${raw%%#*}"
    entry="$(printf '%s' "$entry" | tr -d '[:space:]')"
    [ -z "$entry" ] && continue
    hits=$(printf '%s\n' "$hits" | grep -v "^${entry}:" || true)
  done < "$allowlist"
fi

if [ -n "$hits" ]; then
  printf '%s\n' "$hits" >&2
  echo "ERROR: found axiom/unsafe in verified targets: ${trees[*]}" >&2
  exit 1
fi

echo "forbid_axiom_unsafe: OK (${trees[*]})"
exit 0
