#!/usr/bin/env bash
set -euo pipefail

# Create a new Problem Card + matching Conjectures skeleton.
#
# Usage:
#   ./scripts/new_problem_card.sh <slug> "<Title>"
# Example:
#   ./scripts/new_problem_card.sh abc-conjecture "ABC Conjecture"

if [[ $# -lt 2 ]]; then
  echo "usage: scripts/new_problem_card.sh <slug> \"<Title>\"" >&2
  exit 2
fi

SLUG="$1"; shift
TITLE="$*"

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_DIR"

# sanitize slug into a Lean-friendly directory name (no hyphens)
LEAN_SLUG="${SLUG//-/_}"

NEXT=$(python3 - <<'PY'
import re
from pathlib import Path

conj = Path('Conjectures')
pat = re.compile(r'^C(\d{4})_')
nums=[]
if conj.exists():
  for p in conj.iterdir():
    if p.is_dir():
      m=pat.match(p.name)
      if m:
        nums.append(int(m.group(1)))

n = (max(nums) + 1) if nums else 1
print(f"{n:04d}")
PY
)

CARD_PATH="Problems/${SLUG}.md"
CONJ_DIR="Conjectures/C${NEXT}_${LEAN_SLUG}"

mkdir -p "Problems" "$CONJ_DIR/src"

if [[ -e "$CARD_PATH" ]]; then
  echo "error: $CARD_PATH already exists" >&2
  exit 1
fi

export SLUG TITLE NEXT CARD_PATH CONJ_DIR
python3 - <<'PY'
import os
from pathlib import Path

slug = os.environ['SLUG']
title = os.environ['TITLE']
next_id = os.environ['NEXT']
card_path = Path(os.environ['CARD_PATH'])
conj_dir = Path(os.environ['CONJ_DIR'])
lean_stub = conj_dir / 'src' / 'Main.lean'

card_path.write_text(f"""# Problem Card: {title}

Status: draft

## 0. One-line pitch

(Why this problem matters / why it’s interesting.)

## 1. Natural language statement

(Write the cleanest statement you can.)

## 2. Formalization target (Lean)

Goal: a *type-correct* Lean statement.

- Target file: `{lean_stub.as_posix()}` (backlog; may contain `sorry`)
- Reusable definitions should land in `MoltResearch/`

## 3. Dependencies

- Definitions needed:
  - ...
- Lemmas likely needed:
  - ...

## 4. Decomposition (mergeable sub-tasks)

- [ ] Formalize definitions (land in `MoltResearch/` if reusable)
- [ ] Prove prerequisite lemmas (land in `MoltResearch/`)
- [ ] Create small intermediate claims (provable)
- [ ] Optional: computational exploration / counterexamples

Each item should specify:
- file(s) to touch
- command to run (`make build` or `make task FILE=...`)
- definition of done

## 5. References / links

- Papers:
- Notes:
- Related theorems:

## 6. Notes / gotchas
""", encoding='utf-8')

(conj_dir / 'card.md').write_text(
    f"""# C{next_id} — {title}

See `Problems/{slug}.md`.
""",
    encoding='utf-8'
)

(conj_dir / 'notes.md').write_text(
    "Notes and references live here.\n",
    encoding='utf-8'
)

lean_stub.write_text(
    """import Mathlib

/-!
Conjecture/backlog stub.

This file may contain `sorry`. Reusable, verified artifacts belong in `MoltResearch/`.
-/

namespace MoltResearch

-- TODO: add a clean type-correct Lean statement + decomposition helpers.

end MoltResearch
""",
    encoding='utf-8'
)
PY

echo "Created:"
echo "- $CARD_PATH"
echo "- $CONJ_DIR"
