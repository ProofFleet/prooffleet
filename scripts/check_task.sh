#!/usr/bin/env bash
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: scripts/check_task.sh <path-to-lean-file>" >&2
  exit 2
fi

FILE="$1"

# Use elan-installed lake even if it's not on PATH.
LAKE="${LAKE:-$HOME/.elan/bin/lake}"

if [ ! -x "$LAKE" ]; then
  echo "error: lake not found at $LAKE (set LAKE=/path/to/lake)" >&2
  exit 1
fi

# Typecheck the file inside the project environment.
"$LAKE" env lean "$FILE"

echo "OK: $FILE"
