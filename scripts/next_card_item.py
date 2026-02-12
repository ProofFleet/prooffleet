#!/usr/bin/env python3
"""Print the next unchecked checklist item from a Problem Card.

Usage:
  ./scripts/next_card_item.py --card Problems/erdos_discrepancy.md --track B

Outputs the raw checkbox text (without the leading "- [ ] ").
If none found, prints "N/A".

This is intentionally dumb and stable: we rely on headings of the form:
  ### Track A — ...
  ### Track B — ...
  ### Track C — ...
"""

from __future__ import annotations

import argparse
import re
import sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--card", required=True)
    ap.add_argument("--track", required=True, choices=["A", "B", "C"])
    args = ap.parse_args()

    with open(args.card, "r", encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()

    # Find the start of the requested Track section.
    track_re = re.compile(rf"^###\s+Track\s+{re.escape(args.track)}\b")
    start = None
    for i, ln in enumerate(lines):
        if track_re.match(ln.strip()):
            start = i + 1
            break

    if start is None:
        print("N/A")
        return 0

    # Scan until next Track heading.
    next_track_re = re.compile(r"^###\s+Track\s+[ABC]\b")
    for ln in lines[start:]:
        if next_track_re.match(ln.strip()):
            break
        m = re.match(r"^-\s*\[\s*\]\s+(.*)\s*$", ln)
        if m:
            item = m.group(1).strip()
            if item:
                print(item)
                return 0

    print("N/A")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
