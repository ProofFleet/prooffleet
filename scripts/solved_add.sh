#!/usr/bin/env bash
set -euo pipefail

# Append entries to SOLVED.md.
# Usage:
#   scripts/solved_add.sh <tier> <task> <pr_url> <author>
# Example:
#   scripts/solved_add.sh tier-0 T0_07 https://github.com/ProofFleet/moltresearch/pull/52 alice

if [ $# -ne 4 ]; then
  echo "usage: $0 <tier-0|tier-1> <task> <pr_url> <author>" >&2
  exit 2
fi

tier="$1"
task="$2"
pr="$3"
author="$4"

case "$tier" in
  tier-0) header="## Tier-0" ;;
  tier-1) header="## Tier-1" ;;
  *) echo "unknown tier: $tier" >&2; exit 2 ;;
esac

if [ ! -f SOLVED.md ]; then
  echo "error: SOLVED.md not found" >&2
  exit 1
fi

line="- ${task} → ${pr} → ${author}"

# Don’t duplicate.
if grep -Fqx "$line" SOLVED.md; then
  echo "already present: $line"
  exit 0
fi

python3 - <<PY
from pathlib import Path
p = Path('SOLVED.md')
lines = p.read_text().splitlines()
header = "${header}"
insert = "${line}"

out=[]
i=0
inserted=False
while i < len(lines):
  out.append(lines[i])
  if lines[i].strip() == header:
    # Insert right after header and any blank line(s)
    j=i+1
    while j < len(lines) and lines[j].strip()=="":
      out.append(lines[j]); j+=1
    out.append(insert)
    inserted=True
    # copy remainder from j
    out.extend(lines[j:])
    break
  i+=1

if not inserted:
  out.append("")
  out.append(header)
  out.append("")
  out.append(insert)

p.write_text("\n".join(out)+"\n")
print('added:', insert)
PY
