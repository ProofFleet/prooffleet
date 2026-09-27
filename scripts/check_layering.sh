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

# 3. The Palomar statement surface (PalomarEDP/, see docs/edp-release.md) is a leaf with fixed
#    imports.
#    - PalomarEDP/Challenge.lean is the statement a reader audits, and Palomar rejects any
#      project file in its import closure: it may import Mathlib only.
#    - PalomarEDP/Solution.lean may import Mathlib, the nucleus and the public EDP wrapper, and
#      never the Challenge: both declare `EDP.erdos_discrepancy`.
#    - PalomarEDP/ holds exactly those two modules, and nothing imports either of them.
#    Solution.lean is the one file outside the backlog trees that imports one of them (rule 2a).
#    That stays sound because it is itself named in scripts/ci_targets.txt: a Conjectures change
#    that breaks it fails CI directly.
if [ -d PalomarEDP ]; then
  if hits=$(grep -n -E '^import ' PalomarEDP/Challenge.lean |
      grep -v -E '^[0-9]+:import Mathlib(\.[A-Za-z0-9_.]+)?[[:space:]]*$'); then
    echo "ERROR: PalomarEDP/Challenge.lean may import Mathlib only" >&2
    echo "$hits" >&2
    fail=1
  fi
  if hits=$(grep -n -E '^import ' PalomarEDP/Solution.lean |
      grep -v -E '^[0-9]+:import (Mathlib(\.[A-Za-z0-9_.]+)?|MoltResearch(\.[A-Za-z0-9_.]+)?|Conjectures\.C0002_erdos_discrepancy\.src\.ErdosDiscrepancy)[[:space:]]*$'); then
    echo "ERROR: PalomarEDP/Solution.lean may import Mathlib, MoltResearch.* and" \
      "Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy only" >&2
    echo "$hits" >&2
    fail=1
  fi
  if extra=$(find PalomarEDP -type f ! -path PalomarEDP/Challenge.lean ! -path PalomarEDP/Solution.lean |
      grep .); then
    echo "ERROR: PalomarEDP/ must contain only Challenge.lean and Solution.lean" >&2
    echo "$extra" >&2
    fail=1
  fi
  if hits=$(grep -RIn --include='*.lean' -E '^import PalomarEDP' \
      MoltResearch Solutions Tasks Conjectures PalomarEDP ./*.lean 2>/dev/null); then
    echo "ERROR: nothing may import PalomarEDP.*" >&2
    echo "$hits" >&2
    fail=1
  fi
fi

if [ "$fail" -eq 0 ]; then
  echo "check_layering: OK"
fi

exit "$fail"
