#!/usr/bin/env bash
# Library layering invariants.
#
# Two properties this repo relies on but has never enforced:
#
#   1. The analytic layer (`MoltResearch/Analytic/`) is general mathematics and must not
#      depend on the Erdős-discrepancy nucleus (`MoltResearch/Discrepancy/`). The dependency
#      runs one way only, so a future problem card can import the analytic stack without
#      dragging EDP in. (No-op until the rehome lands; it locks the invariant in advance.)
#
#   2. The backlog trees are import leaves: nothing outside `Tasks/`, `Solutions/` or
#      `Conjectures/` imports them, and they do not import each other. This is what makes
#      change-scoped CI sound — a PR touching only `Conjectures/` cannot break a target that
#      CI skipped, because no skipped target can depend on it.
#
# Pure grep; runs in about a second, no Lean toolchain required.

set -uo pipefail

fail=0

# 1. Analytic must not depend on Discrepancy.
if [ -d MoltResearch/Analytic ]; then
  if hits=$(grep -RIn --include='*.lean' -E '^import MoltResearch\.Discrepancy' \
      MoltResearch/Analytic/ 2>/dev/null); then
    echo "ERROR: MoltResearch/Analytic must not import MoltResearch.Discrepancy.*" >&2
    echo "$hits" >&2
    fail=1
  fi
fi

# 2a. Nothing outside a backlog tree may import Tasks.* or Conjectures.*
#     (`Tasks/` importing `Tasks.` and `Conjectures/` importing `Conjectures.` is fine.)
if hits=$(grep -RIn --include='*.lean' -E '^import (Tasks|Conjectures)\.' \
    MoltResearch Solutions 2>/dev/null); then
  echo "ERROR: nothing outside the backlog trees may import Tasks.* / Conjectures.*" >&2
  echo "$hits" >&2
  fail=1
fi

# 2b. Nothing may import Solutions.* (the root Solutions.lean entrypoint aside).
if hits=$(grep -RIn --include='*.lean' -E '^import Solutions\.' \
    MoltResearch Tasks Conjectures 2>/dev/null); then
  echo "ERROR: nothing may import Solutions.*" >&2
  echo "$hits" >&2
  fail=1
fi

if [ "$fail" -eq 0 ]; then
  echo "check_layering: OK"
fi

exit "$fail"
