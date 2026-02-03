#!/usr/bin/env bash
set -euo pipefail

# Add SOLVED.md entries for tasks closed by a PR.
# Usage:
#   scripts/solved_from_pr.sh <pr_number>
# Example:
#   scripts/solved_from_pr.sh 51

if [ $# -ne 1 ]; then
  echo "usage: $0 <pr_number>" >&2
  exit 2
fi

PR="$1"
REPO="${REPO:-ProofFleet/moltresearch}"

# Pull PR info via gh api (avoid gh pr edit quirks).
json=$(gh api repos/$REPO/pulls/$PR)
url=$(python3 - <<PY
import json
j=json.loads('''$json''')
print(j['html_url'])
PY
)
user=$(python3 - <<PY
import json
j=json.loads('''$json''')
print(j['user']['login'])
PY
)
body=$(python3 - <<PY
import json
j=json.loads('''$json''')
print(j.get('body') or '')
PY
)

# naive parse: look for T0_XX or T1_XX in body
python3 - <<PY
import re, sys
body = sys.argv[1]
seen=set()
for m in re.findall(r"\bT[01]_[0-9]{2}\b", body):
  seen.add(m)
print('\n'.join(sorted(seen)))
PY "$body" > /tmp/solved_tasks.txt

if [ ! -s /tmp/solved_tasks.txt ]; then
  echo "No tasks detected in PR body. Edit PR body to mention e.g. T0_07 and re-run." >&2
  exit 1
fi

while read -r task; do
  if [[ "$task" =~ ^T0_ ]]; then
    ./scripts/solved_add.sh tier-0 "$task" "$url" "$user"
  elif [[ "$task" =~ ^T1_ ]]; then
    ./scripts/solved_add.sh tier-1 "$task" "$url" "$user"
  fi
done < /tmp/solved_tasks.txt

echo "Done. Commit SOLVED.md."
