#!/usr/bin/env bash
set -euo pipefail

# Generate a weekly recap stub for NEWS.md using merged PR titles.
# Usage:
#   scripts/weekly_recap.sh [since]
# Example:
#   scripts/weekly_recap.sh 2026-02-01

REPO="${REPO:-ProofFleet/moltresearch}"
SINCE="${1:-7 days ago}"

# Requires gh auth.

python3 - <<PY
import datetime, subprocess, json, os
repo=os.environ.get('REPO','ProofFleet/moltresearch')
since=os.environ.get('SINCE', '7 days ago')

# gh search with merged: and merged:> is annoying; use API with pulls? easiest: list PRs and filter.
cmd=['gh','pr','list','--repo',repo,'--state','merged','--limit','50','--json','number,title,mergedAt,url']
raw=subprocess.check_output(cmd,text=True)
prs=json.loads(raw)

def parse_dt(s):
    return datetime.datetime.fromisoformat(s.replace('Z','+00:00'))

cut = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=7)
# allow explicit ISO date
try:
    if len(since)==10 and since[4]=='-' and since[7]=='-':
        cut=datetime.datetime.fromisoformat(since+'T00:00:00+00:00')
except Exception:
    pass

items=[p for p in prs if p.get('mergedAt') and parse_dt(p['mergedAt'])>=cut]
print('## '+datetime.date.today().isoformat())
for p in sorted(items, key=lambda x: x['mergedAt']):
    print(f"- #{p['number']}: {p['title']} ({p['url']})")
PY
