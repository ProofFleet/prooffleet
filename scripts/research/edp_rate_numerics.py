#!/usr/bin/env python3
"""Reproduce finite-scale numerics for the Erdős discrepancy-rate card.

The script evaluates

    D(x) = max_{d*m <= x} |sum_{k=1}^m f(k*d)|

for two kinds of data:

* modified quadratic-character sequences for p = 3, 5, 7, 11; and
* published finite low-discrepancy witnesses, followed by the period-9 lift
  of Le Bras--Gomes--Selman.

The finite witnesses are read from version-pinned arXiv source bundles and
checked against pinned SHA-256 digests.  NumPy is the only non-stdlib
dependency.  No SAT solver or uncommitted data file is needed.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import math
import re
import sys
import tarfile
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence, TextIO

try:
    import numpy as np
except ImportError as exc:  # pragma: no cover - exercised only without the dependency
    raise SystemExit("edp_rate_numerics.py requires NumPy") from exc


KONEV_URL = "https://export.arxiv.org/e-print/1405.3097v2"
KONEV_SHA256 = "f0a74969c7228733e208afcd3818bbaa60151de0d81431c19b41f01bf721943d"
LE_BRAS_URL = "https://export.arxiv.org/e-print/1407.2510v1"
LE_BRAS_SHA256 = "07fbdd98908a9bc61c9cd7ece416689b9dc375032c9323c14a17602e422347f7"

# The eight nonzero residue classes in one period-9 lift block.  Position 9j
# receives the j-th term of the input sequence.
WALTERS_MOD9_BLOCK = np.asarray([1, -1, -1, 1, -1, 1, 1, -1], dtype=np.int8)
SIGN_RE = re.compile(r"(?<![A-Za-z])[+-](?![A-Za-z])")


@dataclass(frozen=True)
class Record:
    family: str
    sequence: str
    x: int
    discrepancy: int
    d: int
    m: int

    @property
    def ratio(self) -> float:
        return self.discrepancy / math.log(self.x)


def fetch_or_read(path: Path | None, url: str, expected_sha256: str) -> bytes:
    """Read an arXiv bundle locally or download it, then enforce its digest."""
    if path is None:
        request = urllib.request.Request(
            url, headers={"User-Agent": "moltresearch-edp-rate-numerics/1.0"}
        )
        with urllib.request.urlopen(request, timeout=120) as response:
            payload = response.read()
    else:
        payload = path.read_bytes()
    actual = hashlib.sha256(payload).hexdigest()
    if actual != expected_sha256:
        origin = str(path) if path is not None else url
        raise ValueError(
            f"source digest mismatch for {origin}: expected {expected_sha256}, got {actual}"
        )
    return payload


def tar_member_text(payload: bytes, member_name: str) -> str:
    """Return one UTF-8 member from a compressed arXiv source bundle."""
    with tarfile.open(fileobj=io.BytesIO(payload), mode="r:*") as archive:
        member = archive.extractfile(member_name)
        if member is None:
            raise ValueError(f"arXiv source bundle has no {member_name!r}")
        return member.read().decode("utf-8")


def signs_to_array(text: str, expected_length: int) -> np.ndarray:
    """Parse standalone '+'/'-' tokens into a one-based int8 array."""
    tokens = SIGN_RE.findall(text)
    if len(tokens) != expected_length:
        raise ValueError(f"expected {expected_length} signs, parsed {len(tokens)}")
    sequence = np.empty(expected_length + 1, dtype=np.int8)
    sequence[0] = 0
    sequence[1:] = np.fromiter(
        (1 if token == "+" else -1 for token in tokens),
        dtype=np.int8,
        count=expected_length,
    )
    return sequence


def load_konev_lisitsa_1160(payload: bytes) -> np.ndarray:
    """Extract the discrepancy-2 witness from arXiv:1405.3097v2 Appendix B."""
    text = tar_member_text(payload, "jArx.tex")
    marker = r"\noindent{}{\tt"
    if marker not in text:
        raise ValueError("could not find the 1160-term appendix marker")
    return signs_to_array(text.split(marker, 1)[1], 1160)


def load_le_bras_gomes_selman_127645(payload: bytes) -> np.ndarray:
    """Extract the completely multiplicative witness from arXiv:1407.2510v1."""
    return signs_to_array(tar_member_text(payload, "sequence127645.tex"), 127_645)


def legendre_table(p: int) -> np.ndarray:
    """The Legendre symbol modulo the small odd prime p, as an int8 table."""
    table = np.full(p, -1, dtype=np.int8)
    table[0] = 0
    for residue in range(1, p):
        table[residue] = 1 if pow(residue, (p - 1) // 2, p) == 1 else -1
    return table


def modified_character(p: int, at_p: int, length: int) -> np.ndarray:
    """Build f(p^v*m) = at_p^v * (m|p), for p not dividing m.

    The Borwein--Choi--Coons sequence lambda_p is at_p=+1.  For p=3,
    at_p=-1 is the improved Walters sequence.
    """
    if at_p not in (-1, 1):
        raise ValueError("at_p must be -1 or +1")
    table = legendre_table(p)
    indices = np.arange(length + 1, dtype=np.int32)
    sequence = table[indices % p]
    sequence[0] = 0
    del indices

    power = p
    at_power = at_p
    while power <= length:
        reduced = np.arange(1, length // power + 1, dtype=np.int32)
        reduced = reduced[reduced % p != 0]
        sequence[power * reduced] = at_power * table[reduced % p]
        if power > length // p:
            break
        power *= p
        at_power *= at_p
    if not np.all(np.abs(sequence[1:]) == 1):
        raise AssertionError("modified-character generator produced a non-sign value")
    return sequence


def period9_lift_prefix(sequence: np.ndarray, target_length: int) -> np.ndarray:
    """Return the requested prefix of the Le Bras--Gomes--Selman period-9 lift."""
    source_length = len(sequence) - 1
    if target_length > 9 * source_length:
        raise ValueError("period-9 lift requested beyond the available source sequence")
    lifted = np.empty(target_length + 1, dtype=np.int8)
    lifted[0] = 0
    for residue, value in enumerate(WALTERS_MOD9_BLOCK, start=1):
        lifted[residue::9] = value
    multiples = target_length // 9
    lifted[9 : 9 * multiples + 1 : 9] = sequence[1 : multiples + 1]
    return lifted


def is_completely_multiplicative(
    sequence: np.ndarray,
) -> tuple[bool, tuple[int, int] | None]:
    """Check f(ab)=f(a)f(b) for every product represented by a finite sequence."""
    length = len(sequence) - 1
    for a in range(1, length + 1):
        values = sequence[a : length + 1 : a]
        expected = sequence[a] * sequence[1 : length // a + 1]
        mismatch = np.flatnonzero(values != expected)
        if mismatch.size:
            return False, (a, int(mismatch[0]) + 1)
    return True, None


def prefix_records(
    name: str, sequence: np.ndarray, checkpoints: Sequence[int]
) -> list[Record]:
    """Compute D(x) by the d=1 reduction for a completely multiplicative sequence."""
    partial_abs = np.abs(np.cumsum(sequence[1:], dtype=np.int32))
    prefix_max = partial_abs.copy()
    np.maximum.accumulate(prefix_max, out=prefix_max)
    records: list[Record] = []
    for x in checkpoints:
        discrepancy = int(prefix_max[x - 1])
        m = int(np.argmax(partial_abs[:x] == discrepancy)) + 1
        records.append(Record("modified character", name, x, discrepancy, 1, m))
    return records


def exact_discrepancy_records(
    name: str, sequence: np.ndarray, checkpoints: Sequence[int]
) -> list[Record]:
    """Exhaustively compute D(x), splitting the (d,m) hyperbola at sqrt(max x).

    This enumerates every pair d*m <= max(checkpoints).  The two vectorized
    halves are d <= sqrt(N), scanned by d, and d > sqrt(N), scanned by m.
    """
    if not checkpoints:
        return []
    if tuple(checkpoints) != tuple(sorted(set(checkpoints))):
        raise ValueError("checkpoints must be strictly increasing")
    limit = checkpoints[-1]
    if limit > len(sequence) - 1:
        raise ValueError("checkpoint exceeds sequence length")

    split = math.isqrt(limit)
    count = len(checkpoints)
    best = np.zeros(count, dtype=np.int32)
    best_d = np.zeros(count, dtype=np.int32)
    best_m = np.zeros(count, dtype=np.int32)

    # Small steps: one cumulative sum gives every m for this d.
    for d in range(1, split + 1):
        partial_abs = np.abs(np.cumsum(sequence[d : limit + 1 : d], dtype=np.int32))
        prefix_max = partial_abs.copy()
        np.maximum.accumulate(prefix_max, out=prefix_max)
        for index, x in enumerate(checkpoints):
            m_limit = x // d
            if m_limit and prefix_max[m_limit - 1] > best[index]:
                discrepancy = int(prefix_max[m_limit - 1])
                best[index] = discrepancy
                best_d[index] = d
                best_m[index] = int(np.argmax(partial_abs[:m_limit] == discrepancy)) + 1

    # Large steps: sums[d] is updated from length m-1 to length m in bulk.
    first_large_d = split + 1
    sums = np.zeros(limit + 1, dtype=np.int32)
    for m in range(1, limit // first_large_d + 1):
        last_d = limit // m
        sums[first_large_d : last_d + 1] += sequence[
            m * first_large_d : m * (last_d + 1) : m
        ]
        current_abs = np.abs(sums[first_large_d : last_d + 1])
        prefix_max = current_abs.copy()
        np.maximum.accumulate(prefix_max, out=prefix_max)
        for index, x in enumerate(checkpoints):
            checkpoint_last_d = x // m
            if (
                checkpoint_last_d >= first_large_d
                and prefix_max[checkpoint_last_d - first_large_d] > best[index]
            ):
                discrepancy = int(prefix_max[checkpoint_last_d - first_large_d])
                best[index] = discrepancy
                best_d[index] = first_large_d + int(
                    np.argmax(
                        current_abs[: checkpoint_last_d - first_large_d + 1]
                        == discrepancy
                    )
                )
                best_m[index] = m

    records = [
        Record(
            "finite construction", name, x, int(best[i]), int(best_d[i]), int(best_m[i])
        )
        for i, x in enumerate(checkpoints)
    ]
    for record in records:
        if record.d * record.m > record.x:
            raise AssertionError("reported witness lies outside d*m <= x")
        witness_sum = int(
            sequence[record.d : record.d * record.m + 1 : record.d].sum(dtype=np.int32)
        )
        if abs(witness_sum) != record.discrepancy:
            raise AssertionError(
                "reported witness does not attain the reported discrepancy"
            )
    return records


def brute_discrepancy(sequence: np.ndarray, x: int) -> int:
    """Small reference implementation used only by the internal self-test."""
    best = 0
    for d in range(1, x + 1):
        total = 0
        for m in range(1, x // d + 1):
            total += int(sequence[d * m])
            best = max(best, abs(total))
    return best


def self_test(sequence: np.ndarray) -> None:
    """Compare the hyperbola algorithm with brute force on a small prefix."""
    checkpoints = [10, 64, 200]
    fast = exact_discrepancy_records("self-test", sequence, checkpoints)
    slow = [brute_discrepancy(sequence, x) for x in checkpoints]
    if [record.discrepancy for record in fast] != slow:
        raise AssertionError(
            f"exact discrepancy self-test failed: {fast!r} != {slow!r}"
        )


def decade_checkpoints(max_x: int) -> list[int]:
    checkpoints: list[int] = []
    x = 10
    while x <= max_x:
        checkpoints.append(x)
        x *= 10
    if not checkpoints or checkpoints[-1] != max_x:
        checkpoints.append(max_x)
    return checkpoints


def construction_ladder(
    base_name: str, base: np.ndarray, max_x: int
) -> Iterable[tuple[str, np.ndarray]]:
    """Yield full period-9 lifts, followed by a final prefix exactly at max_x."""
    level = 0
    if len(base) - 1 > max_x:
        current = base[: max_x + 1].copy()
        base_name = f"{base_name}; prefix"
    else:
        current = base
    while True:
        length = len(current) - 1
        yield (
            base_name if level == 0 else f"{base_name}; period-9 lift^{level}",
            current,
        )
        if length >= max_x:
            return
        target = min(9 * length, max_x)
        current = period9_lift_prefix(current, target)
        level += 1


def collect_records(args: argparse.Namespace) -> tuple[list[Record], list[str]]:
    if args.max_x < 10:
        raise ValueError("--max-x must be at least 10")

    konev_payload = fetch_or_read(args.konev_source, KONEV_URL, KONEV_SHA256)
    le_bras_payload = fetch_or_read(args.le_bras_source, LE_BRAS_URL, LE_BRAS_SHA256)
    konev = load_konev_lisitsa_1160(konev_payload)
    le_bras = load_le_bras_gomes_selman_127645(le_bras_payload)

    self_test(konev)
    complete, mismatch = is_completely_multiplicative(le_bras)
    if not complete:
        raise AssertionError(
            f"127645-term witness fails multiplicativity at {mismatch}"
        )

    provenance = [
        f"Konev--Lisitsa source: {KONEV_URL}",
        f"Konev--Lisitsa SHA-256: {KONEV_SHA256}",
        f"Le Bras--Gomes--Selman source: {LE_BRAS_URL}",
        f"Le Bras--Gomes--Selman SHA-256: {LE_BRAS_SHA256}",
        "127645-term finite multiplicativity check: passed",
        "exact-discrepancy brute-force self-test through x=200: passed",
    ]

    records: list[Record] = []
    checkpoints = decade_checkpoints(args.max_x)
    for p in (3, 5, 7, 11):
        for at_p in (1, -1):
            sequence = modified_character(p, at_p, args.max_x)
            sign_name = "+1" if at_p == 1 else "-1"
            records.extend(
                prefix_records(f"p={p}, f(p)={sign_name}", sequence, checkpoints)
            )

    for base_name, base in (
        ("Konev--Lisitsa 1160", konev),
        ("Le Bras--Gomes--Selman 127645", le_bras),
    ):
        for name, sequence in construction_ladder(base_name, base, args.max_x):
            x = len(sequence) - 1
            records.extend(exact_discrepancy_records(name, sequence, [x]))

    return records, provenance


def print_markdown(
    records: Sequence[Record], provenance: Sequence[str], stream: TextIO
) -> None:
    print("## Provenance and checks", file=stream)
    for line in provenance:
        print(f"- {line}", file=stream)
    print("\n## Results", file=stream)
    print("| family | sequence | x | D(x) | d | m | D(x) / ln(x) |", file=stream)
    print("|---|---|---:|---:|---:|---:|---:|", file=stream)
    for record in records:
        print(
            f"| {record.family} | {record.sequence} | {record.x} | "
            f"{record.discrepancy} | {record.d} | {record.m} | {record.ratio:.6f} |",
            file=stream,
        )


def print_csv(
    records: Sequence[Record], provenance: Sequence[str], stream: TextIO
) -> None:
    for line in provenance:
        print(f"# {line}", file=stream)
    writer = csv.writer(stream)
    writer.writerow(["family", "sequence", "x", "D(x)", "d", "m", "D(x)/ln(x)"])
    for record in records:
        writer.writerow(
            [
                record.family,
                record.sequence,
                record.x,
                record.discrepancy,
                record.d,
                record.m,
                f"{record.ratio:.9f}",
            ]
        )


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-x",
        type=int,
        default=10_000_000,
        help="largest scale (default: 10000000)",
    )
    parser.add_argument(
        "--konev-source",
        type=Path,
        help="optional local copy of the arXiv:1405.3097v2 source bundle",
    )
    parser.add_argument(
        "--le-bras-source",
        type=Path,
        help="optional local copy of the arXiv:1407.2510v1 source bundle",
    )
    parser.add_argument("--format", choices=("markdown", "csv"), default="markdown")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        records, provenance = collect_records(args)
    except (OSError, ValueError, tarfile.TarError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if args.format == "markdown":
        print_markdown(records, provenance, sys.stdout)
    else:
        print_csv(records, provenance, sys.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
