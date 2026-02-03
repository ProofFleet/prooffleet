#!/usr/bin/env python3
from __future__ import annotations

import re
from pathlib import Path

text = Path('SOLVED.md').read_text()

sections = {
    'tier-0': re.split(r"^##\s+Tier-0\s*$", text, flags=re.M)[1] if '## Tier-0' in text else "",
    'tier-1': re.split(r"^##\s+Tier-1\s*$", text, flags=re.M)[1] if '## Tier-1' in text else "",
}

def count_lines(s: str) -> int:
    return sum(1 for line in s.splitlines() if line.strip().startswith('- '))

for k in ['tier-0','tier-1']:
    print(f"{k} {count_lines(sections.get(k,''))}")
