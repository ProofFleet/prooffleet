#!/usr/bin/env python3
"""Sync Problem Card checkboxes from merged PR metadata.

We require PR bodies to begin with:
  Card: Problems/<card>.md | N/A
  Track: A|B|C | N/A
  Checklist item: <exact checkbox text> | N/A

If Card != N/A and Checklist item != N/A, this script will mark the matching checkbox
`- [ ] <text>` as checked `- [x] <text>` in that card.

Designed to be run periodically (cron). It batches updates into a single PR.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone


def sh(cmd: list[str], check=True) -> str:
    p = subprocess.run(cmd, check=check, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return p.stdout


def parse_header(body: str) -> dict[str, str]:
    # Normalize CRLF.
    lines = body.replace("\r\n", "\n").split("\n")
    out = {"card": "", "track": "", "item": ""}
    for line in lines[:40]:
        m = re.match(r"^Card:\s*(.*)\s*$", line, flags=re.I)
        if m and not out["card"]:
            out["card"] = m.group(1).strip()
            continue
        m = re.match(r"^Track:\s*(.*)\s*$", line, flags=re.I)
        if m and not out["track"]:
            out["track"] = m.group(1).strip()
            continue
        m = re.match(r"^Checklist item:\s*(.*)\s*$", line, flags=re.I)
        if m and not out["item"]:
            out["item"] = m.group(1).strip()
            continue
    return out


def iso_to_dt(s: str) -> datetime:
    # GitHub gives e.g. 2026-02-12T12:53:54Z
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    return datetime.fromisoformat(s).astimezone(timezone.utc)


def mark_checkbox(card_path: str, item_text: str) -> bool:
    """Return True if file changed."""
    with open(card_path, "r", encoding="utf-8", errors="replace") as f:
        src = f.read()

    # Exact match on the checkbox line.
    unchecked = f"- [ ] {item_text}"
    checked = f"- [x] {item_text}"

    if checked in src:
        return False
    if unchecked not in src:
        return False

    dst = src.replace(unchecked, checked, 1)
    with open(card_path, "w", encoding="utf-8") as f:
        f.write(dst)
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="ProofFleet/moltresearch")
    ap.add_argument("--state-file", default=os.path.expanduser("~/.cache/moltresearch/problem-card-sync.json"))
    ap.add_argument("--limit", type=int, default=50)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    os.makedirs(os.path.dirname(args.state_file), exist_ok=True)
    last_ts = None
    if os.path.exists(args.state_file):
        try:
            with open(args.state_file, "r", encoding="utf-8") as f:
                last_ts = json.load(f).get("lastMergedAt")
        except Exception:
            last_ts = None

    # Pull merged PRs.
    raw = sh([
        "gh", "pr", "list",
        "--repo", args.repo,
        "--state", "merged",
        "--limit", str(args.limit),
        "--json", "number,mergedAt,body,url",
    ])
    prs = json.loads(raw)

    # Sort oldest->newest
    prs.sort(key=lambda pr: pr.get("mergedAt") or "")

    changed_files: set[str] = set()
    newest = last_ts

    for pr in prs:
        merged_at = pr.get("mergedAt")
        if not merged_at:
            continue
        if last_ts and merged_at <= last_ts:
            continue

        hdr = parse_header(pr.get("body") or "")
        card = hdr["card"]
        item = hdr["item"]

        if not card or card.upper() == "N/A" or not item or item.upper() == "N/A":
            newest = merged_at
            continue

        if not os.path.exists(card):
            # Card moved or typo; skip.
            newest = merged_at
            continue

        if mark_checkbox(card, item):
            changed_files.add(card)

        newest = merged_at

    if newest and newest != last_ts and not args.dry_run:
        with open(args.state_file, "w", encoding="utf-8") as f:
            json.dump({"lastMergedAt": newest}, f)

    if args.dry_run:
        print(json.dumps({"changed": sorted(changed_files), "lastMergedAt": newest, "previous": last_ts}, indent=2))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
