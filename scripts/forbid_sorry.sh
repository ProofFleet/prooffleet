#!/usr/bin/env bash
set -euo pipefail

fail=0

grep -RIn --line-number --exclude-dir=Tasks --exclude-dir=Conjectures "\bsorry\b" MoltResearch Solutions && {
  echo "ERROR: found 'sorry' in verified targets" >&2
  fail=1
} || true

# PalomarEDP/ (the Palomar registry statement and its proof) is held to the same rule, with one
# exception: PalomarEDP/Challenge.lean states the theorem of record with exactly one deliberate
# hole, which Comparator matches against PalomarEDP/Solution.lean. The exception covers that one
# file and that one token; a second hole, or a hole anywhere else under PalomarEDP/, fails.
challenge=PalomarEDP/Challenge.lean
if [ -d PalomarEDP ]; then
  grep -RIn --line-number "\bsorry\b" PalomarEDP | grep -v "^${challenge}:" && {
    echo "ERROR: found 'sorry' in PalomarEDP/ outside ${challenge}" >&2
    fail=1
  } || true
  holes=$( (grep -o -w sorry "$challenge" 2>/dev/null || true) | wc -l | tr -d ' ')
  if [ "$holes" != 1 ]; then
    echo "ERROR: ${challenge} must contain exactly one 'sorry' (the statement hole); found ${holes}" >&2
    fail=1
  fi
fi

exit "$fail"
