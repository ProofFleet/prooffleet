#!/usr/bin/env python3
"""Reproducible search for Erdős 461 smooth-component collisions.

For a fixed ``t``, equality of two smooth parts in an interval of length
``t`` is periodic.  The period used here is

    product(p**ceil(log_p(t)) for primes p < t).

Indeed, a collision involving p-adic valuation at least ceil(log_p(t))
would make the difference of the two integers divisible by a number at
least t.  Truncated valuations below that threshold are determined by the
residue modulo the displayed period.  Thus an exhaustive pass over this
period gives a genuine global minimum.  When the period is too large, the
script reports only the best value found by deterministic structured and
pseudorandom searches.

The script uses only the Python standard library.

Passing ``--obstruction-profiles`` switches from the minimum search to exact
Hall-defect profiles for the ``t=8, n=1255`` counterexample and for the
highly-divisible-center family.  Those profiles are computed by dynamic
programming over all possible left-subset sizes and distinct neighborhoods.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from functools import lru_cache
from typing import Iterable


def primes_below(limit: int) -> list[int]:
    """Return all primes strictly below ``limit``."""
    if limit <= 2:
        return []
    sieve = bytearray(b"\x01") * limit
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit - 1) + 1):
        if sieve[p]:
            sieve[p * p : limit : p] = b"\x00" * ((limit - 1 - p * p) // p + 1)
    return [p for p in range(2, limit) if sieve[p]]


def collision_period(t: int, primes: Iterable[int] | None = None) -> int:
    """A period for the equality pattern of t-smooth parts."""
    period = 1
    for p in primes if primes is not None else primes_below(t):
        power = p
        while power < t:
            power *= p
        period *= power
    return period


def smooth_part(m: int, primes: Iterable[int]) -> int:
    """Product of the prime powers in ``m`` supported on the given primes."""
    if m <= 0:
        raise ValueError("smooth_part is evaluated only on positive integers")
    result = 1
    remaining = m
    for p in primes:
        while remaining % p == 0:
            result *= p
            remaining //= p
    return result


def interval_parts(n: int, t: int, primes: list[int]) -> list[int]:
    return [smooth_part(n + offset, primes) for offset in range(1, t + 1)]


def component_count(n: int, t: int, primes: list[int]) -> int:
    return len(set(interval_parts(n, t, primes)))


def exact_minimum(t: int, period: int, primes: list[int]) -> tuple[int, int]:
    """Return (minimum count, least minimizer) over a complete period."""
    # A small sieve computes all needed smooth parts once.  The sliding
    # Counter then makes the exhaustive scan linear in the period.
    values = [1] * (period + t + 1)
    for p in primes:
        for m in range(p, len(values), p):
            q = m
            p_part = 1
            while q % p == 0:
                p_part *= p
                q //= p
            values[m] *= p_part

    frequencies = Counter(values[1 : t + 1])
    best_count = len(frequencies)
    best_n = 0
    for n in range(1, period):
        leaving = values[n]
        frequencies[leaving] -= 1
        if frequencies[leaving] == 0:
            del frequencies[leaving]
        frequencies[values[n + t]] += 1
        count = len(frequencies)
        if count < best_count:
            best_count = count
            best_n = n
    return best_count, best_n


def lcm_through(t: int) -> int:
    value = 1
    for k in range(2, t + 1):
        value = math.lcm(value, k)
    return value


def structured_candidates(t: int, period: int, primes: list[int]) -> set[int]:
    """Residues near 0, -1, and -floor(t/2) for natural moduli."""
    moduli = {1, lcm_through(t), period}
    primorial = 1
    prefix_products = []
    for p in primes:
        primorial *= p
        prefix_products.append(primorial)
    moduli.update(prefix_products)
    if primorial > 1:
        moduli.add(primorial)
        # Products missing one prime probe less symmetric congruence patterns.
        moduli.update(primorial // p for p in primes)

    candidates = {0}
    for modulus in moduli:
        for residue in (0, (-1) % modulus, (-(t // 2)) % modulus):
            for quotient in (0, 1, 2):
                center = quotient * modulus + residue
                for delta in range(-t, t + 1):
                    n = center + delta
                    if n >= 0:
                        candidates.add(n % period)
    return candidates


def sampled_minimum(
    t: int,
    period: int,
    primes: list[int],
    random_samples: int,
    seed: int,
) -> tuple[int, int, int]:
    """Return best count, least best residue, and candidates evaluated."""
    candidates = structured_candidates(t, period, primes)
    rng = random.Random(seed + 1_000_003 * t)
    candidates.update(rng.randrange(period) for _ in range(random_samples))

    @lru_cache(maxsize=None)
    def cached_part(m: int) -> int:
        return smooth_part(m, primes)

    best_count = t + 1
    best_n = 0
    for n in sorted(candidates):
        count = len({cached_part(n + offset) for offset in range(1, t + 1)})
        if count < best_count:
            best_count = count
            best_n = n
    return best_count, best_n, len(candidates)


def maximum_matching(neighbors: dict[int, list[int]]) -> dict[int, int]:
    """Return a maximum left-node-to-offset matching for a small graph."""
    offset_to_s: dict[int, int] = {}

    def augment(s: int, seen: set[int]) -> bool:
        for offset in neighbors[s]:
            if offset in seen:
                continue
            seen.add(offset)
            if offset not in offset_to_s or augment(offset_to_s[offset], seen):
                offset_to_s[offset] = s
                return True
        return False

    for s in neighbors:
        augment(s, set())
    return {s: offset for offset, s in offset_to_s.items()}


def maximum_dyadic_matching(n: int, t: int) -> tuple[int, dict[int, int]]:
    """Match s in [ceil(t/2),t) to distinct multiples in (n,n+t]."""
    divisors = list(range((t + 1) // 2, t))
    neighbors = {
        s: [offset for offset in range(1, t + 1) if (n + offset) % s == 0]
        for s in divisors
    }
    matching = maximum_matching(neighbors)
    return len(matching), matching


def dyadic_neighbors(n: int, t: int) -> dict[int, list[int]]:
    """Upper-half divisors mapped to the offsets of their interval multiples."""
    return {
        d: [offset for offset in range(1, t + 1) if (n + offset) % d == 0]
        for d in range((t + 1) // 2, t)
    }


def lower_component_neighbors(n: int, t: int) -> dict[int, list[int]]:
    """Lower-half divisors mapped to distinct smooth-component values."""
    components = sorted(set(interval_parts(n, t, primes_below(t))))
    return {
        d: [component for component in components if component % d == 0]
        for d in range(1, t // 2 + 1)
    }


@dataclass
class HallProfile:
    """The exact subset defect distribution of a finite bipartite graph."""

    left: list[int]
    right_nodes: list[int]
    matching_size: int
    max_defect: int
    witness_left: list[int]
    witness_neighbors: list[int]
    # For each left-subset size r, map |N(U)| to the number of such U.
    rows: list[dict[str, object]]


def hall_defect_profile(neighbors: dict[int, list[int]]) -> HallProfile:
    """Compute every ``(|U|, |N(U)|)`` count without enumerating subsets.

    Dynamic programming merges subsets with the same size and neighborhood.
    The result is exact; counts in row ``r`` sum to ``binomial(|L|, r)``.
    """
    left = sorted(neighbors)
    right_nodes = sorted({node for values in neighbors.values() for node in values})
    node_bit = {node: 1 << index for index, node in enumerate(right_nodes)}
    neighbor_masks = {
        d: sum(node_bit[node] for node in values) for d, values in neighbors.items()
    }

    # State values are (number of subsets, one witness subset).
    states: dict[tuple[int, int], tuple[int, tuple[int, ...]]] = {(0, 0): (1, ())}
    for d in left:
        updated = dict(states)
        for (size, mask), (count, witness) in states.items():
            key = (size + 1, mask | neighbor_masks[d])
            prior_count, prior_witness = updated.get(key, (0, witness + (d,)))
            updated[key] = (prior_count + count, prior_witness)
        states = updated

    distributions: dict[int, Counter[int]] = defaultdict(Counter)
    max_defect = 0
    witness_left: tuple[int, ...] = ()
    witness_mask = 0
    for (size, mask), (count, witness) in states.items():
        neighborhood_size = mask.bit_count()
        distributions[size][neighborhood_size] += count
        defect = max(0, size - neighborhood_size)
        if defect > max_defect:
            max_defect = defect
            witness_left = witness
            witness_mask = mask

    rows = []
    for size in range(len(left) + 1):
        defect_counts: Counter[int] = Counter()
        for neighborhood_size, count in distributions[size].items():
            defect_counts[max(0, size - neighborhood_size)] += count
        rows.append(
            {
                "subset_size": size,
                "subset_count": sum(distributions[size].values()),
                "neighborhood_cardinalities": dict(sorted(distributions[size].items())),
                "defect_cardinalities": dict(sorted(defect_counts.items())),
            }
        )
    matching = maximum_matching(neighbors)
    return HallProfile(
        left=left,
        right_nodes=right_nodes,
        matching_size=len(matching),
        max_defect=max_defect,
        witness_left=list(witness_left),
        witness_neighbors=[
            node
            for index, node in enumerate(right_nodes)
            if witness_mask & (1 << index)
        ],
        rows=rows,
    )


@dataclass
class ObstructionReport:
    label: str
    n: int
    t: int
    center: int | None
    right_kind: str
    neighbors: dict[int, list[int]]
    profile: HallProfile


def obstruction_reports(max_t: int) -> list[ObstructionReport]:
    """Exact profiles for the prime example and divisible-center family."""
    prime_neighbors = {
        p: [offset for offset in range(1, 9) if (1255 + offset) % p == 0]
        for p in primes_below(8)
        if 2 * p > 8
    }
    reports = [
        ObstructionReport(
            label="prime-pair t=8, n=1255",
            n=1255,
            t=8,
            center=1260,
            right_kind="interval offset",
            neighbors=prime_neighbors,
            profile=hall_defect_profile(prime_neighbors),
        )
    ]
    explicit_dyadic = dyadic_neighbors(1255, 8)
    explicit_components = lower_component_neighbors(1255, 8)
    reports.extend(
        [
            ObstructionReport(
                label="upper-half multiples t=8, n=1255",
                n=1255,
                t=8,
                center=1260,
                right_kind="interval offset",
                neighbors=explicit_dyadic,
                profile=hall_defect_profile(explicit_dyadic),
            ),
            ObstructionReport(
                label="lower-half components t=8, n=1255",
                n=1255,
                t=8,
                center=1260,
                right_kind="smooth component",
                neighbors=explicit_components,
                profile=hall_defect_profile(explicit_components),
            ),
        ]
    )
    for t in range(3, max_t + 1):
        center = lcm_through(t)
        n = center - (t // 2 + 1)
        neighbors = dyadic_neighbors(n, t)
        reports.append(
            ObstructionReport(
                label=f"upper-half divisible center, t={t}",
                n=n,
                t=t,
                center=center,
                right_kind="interval offset",
                neighbors=neighbors,
                profile=hall_defect_profile(neighbors),
            )
        )
        component_neighbors = lower_component_neighbors(n, t)
        reports.append(
            ObstructionReport(
                label=f"lower-half components at divisible center, t={t}",
                n=n,
                t=t,
                center=center,
                right_kind="smooth component",
                neighbors=component_neighbors,
                profile=hall_defect_profile(component_neighbors),
            )
        )
    return reports


def prime_lead(n: int, t: int, primes: list[int]) -> tuple[int, int, int]:
    """Test least multiples and maximum matching for primes in (t/2,t)."""
    dyadic_primes = [p for p in primes if 2 * p > t]
    selected_parts = []
    neighbors = {
        p: [offset for offset in range(1, t + 1) if (n + offset) % p == 0]
        for p in dyadic_primes
    }
    for p in dyadic_primes:
        step = p - (n % p) if n % p else p
        if not 1 <= step <= t:
            raise AssertionError("an interval of length t missed a p < t multiple")
        selected_parts.append(smooth_part(n + step, primes))
    return (
        len(dyadic_primes),
        len(set(selected_parts)),
        len(maximum_matching(neighbors)),
    )


def collision_description(parts: list[int]) -> str:
    fibers: dict[int, list[int]] = defaultdict(list)
    for offset, part in enumerate(parts, start=1):
        fibers[part].append(offset)
    collisions = [
        f"{part}:" + ",".join(map(str, offsets))
        for part, offsets in sorted(fibers.items())
        if len(offsets) > 1
    ]
    return "; ".join(collisions) if collisions else "none"


@dataclass
class SearchRow:
    t: int
    period: int
    status: str
    candidates: int
    count: int
    ratio: float
    n: int
    collisions: str
    prime_count: int
    prime_greedy_distinct: int
    prime_matching: int
    dyadic_size: int
    dyadic_matching: int
    pair_fibers: int
    max_fiber: int
    high_pair_fibers: int
    max_high_fiber: int


def search_t(
    t: int, exact_period_limit: int, random_samples: int, seed: int
) -> SearchRow:
    primes = primes_below(t)
    period = collision_period(t, primes)
    if period <= exact_period_limit:
        count, n = exact_minimum(t, period, primes)
        status = "exact"
        candidates = period
    else:
        count, n, candidates = sampled_minimum(t, period, primes, random_samples, seed)
        status = "sampled"

    parts = interval_parts(n, t, primes)
    if len(set(parts)) != count:
        raise AssertionError("reported count disagrees with the minimizing interval")
    p_count, p_greedy_distinct, p_matching = prime_lead(n, t, primes)
    matching, _ = maximum_dyadic_matching(n, t)
    all_fibers = list(Counter(parts).values())
    high_fibers = [
        multiplicity for part, multiplicity in Counter(parts).items() if 2 * part >= t
    ]
    if high_fibers and max(high_fibers) > 2:
        raise AssertionError("a smooth part >= t/2 occurred more than twice")

    return SearchRow(
        t=t,
        period=period,
        status=status,
        candidates=candidates,
        count=count,
        ratio=count / t,
        n=n,
        collisions=collision_description(parts),
        prime_count=p_count,
        prime_greedy_distinct=p_greedy_distinct,
        prime_matching=p_matching,
        dyadic_size=t - (t + 1) // 2,
        dyadic_matching=matching,
        pair_fibers=sum(multiplicity == 2 for multiplicity in all_fibers),
        max_fiber=max(all_fibers),
        high_pair_fibers=sum(multiplicity == 2 for multiplicity in high_fibers),
        max_high_fiber=max(high_fibers, default=0),
    )


def self_check(
    rows: list[SearchRow], seed: int, reports: list[ObstructionReport] | None = None
) -> None:
    """Check periodicity on fresh residues and all reported invariants."""
    rng = random.Random(seed ^ 0x461)
    for row in rows:
        primes = primes_below(row.t)
        for _ in range(20):
            n = rng.randrange(max(1, row.period))
            if component_count(n, row.t, primes) != component_count(
                n + row.period, row.t, primes
            ):
                raise AssertionError(f"periodicity failed for t={row.t}, n={n}")
        if row.status == "exact" and row.candidates != row.period:
            raise AssertionError("an exact row did not scan its complete period")

    for report in reports or []:
        profile = report.profile
        if profile.max_defect != len(profile.left) - profile.matching_size:
            raise AssertionError(f"Hall identity failed for {report.label}")
        for row in profile.rows:
            size = int(row["subset_size"])
            if row["subset_count"] != math.comb(len(profile.left), size):
                raise AssertionError(f"subset counts failed for {report.label}")
        if report.label.startswith("upper-half"):
            t = report.t
            k = t // 2
            expected_matching = 1 if t % 2 else 2
            expected_defect = k - expected_matching
            if profile.matching_size != expected_matching:
                raise AssertionError(f"matching formula failed for {report.label}")
            if profile.max_defect != expected_defect:
                raise AssertionError(f"defect formula failed for {report.label}")
            center_offset = t // 2 + 1
            for d, offsets in report.neighbors.items():
                expected = (
                    [1, center_offset] if t % 2 == 0 and d == k else [center_offset]
                )
                if offsets != expected:
                    raise AssertionError(f"neighbor formula failed for {report.label}")
        if (
            report.label.startswith("lower-half")
            and report.t <= 40
            and profile.max_defect != 0
        ):
            raise AssertionError(f"lower-half component defect in {report.label}")


def print_markdown(rows: list[SearchRow]) -> None:
    print(
        "| t | period | search | f | f/t | least best n | collisions "
        "(smooth part: offsets) | prime match/total (greedy) | "
        "dyadic matching | all pairs/max | high pairs/max |"
    )
    print("|---:|---:|:---|---:|---:|---:|:---|:---:|:---:|:---:|:---:|")
    for row in rows:
        search = (
            f"exact ({row.candidates})"
            if row.status == "exact"
            else f"sampled ({row.candidates})"
        )
        print(
            f"| {row.t} | {row.period} | {search} | {row.count} | "
            f"{row.ratio:.4f} | {row.n} | {row.collisions} | "
            f"{row.prime_matching}/{row.prime_count} ({row.prime_greedy_distinct}) | "
            f"{row.dyadic_matching}/{row.dyadic_size} | "
            f"{row.pair_fibers}/{row.max_fiber} | "
            f"{row.high_pair_fibers}/{row.max_high_fiber} |"
        )


def _format_histogram(histogram: dict[int, int]) -> str:
    return ", ".join(f"{key}:{value}" for key, value in histogram.items())


def print_obstruction_profiles(reports: list[ObstructionReport]) -> None:
    """Print complete subset-size/neighborhood-cardinality profiles."""
    for report in reports:
        profile = report.profile
        print(f"## {report.label}")
        print()
        print(
            f"n={report.n}, t={report.t}, center={report.center}; "
            f"left={profile.left}; {report.right_kind}s={profile.right_nodes}; "
            f"maximum matching={profile.matching_size}; "
            f"maximum defect={profile.max_defect}."
        )
        print(
            "Witness: U=" f"{profile.witness_left}, N(U)={profile.witness_neighbors}."
        )
        print()
        print("| |U| | subsets | |N(U)|:count | defect:count |")
        print("|---:|---:|:---|:---|")
        for row in profile.rows:
            neighborhoods = _format_histogram(row["neighborhood_cardinalities"])
            defects = _format_histogram(row["defect_cardinalities"])
            print(
                f"| {row['subset_size']} | {row['subset_count']} | "
                f"{neighborhoods} | {defects} |"
            )
        print()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-t", type=int, default=40)
    parser.add_argument("--exact-period-limit", type=int, default=1_000_000)
    parser.add_argument("--random-samples", type=int, default=20_000)
    parser.add_argument("--seed", type=int, default=461)
    parser.add_argument("--self-check", action="store_true")
    parser.add_argument(
        "--obstruction-profiles",
        action="store_true",
        help="print exact Hall-defect profiles instead of the minimum search",
    )
    parser.add_argument("--json", action="store_true", dest="as_json")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_t < 2:
        raise SystemExit("--max-t must be at least 2")
    if args.exact_period_limit < 1 or args.random_samples < 0:
        raise SystemExit("search limits must be nonnegative (period limit positive)")
    if args.obstruction_profiles:
        reports = obstruction_reports(args.max_t)
        if args.self_check:
            self_check([], args.seed, reports)
        if args.as_json:
            print(json.dumps([asdict(report) for report in reports], indent=2))
        else:
            print_obstruction_profiles(reports)
    else:
        rows = [
            search_t(t, args.exact_period_limit, args.random_samples, args.seed)
            for t in range(2, args.max_t + 1)
        ]
        if args.self_check:
            self_check(rows, args.seed)
        if args.as_json:
            print(json.dumps([asdict(row) for row in rows], indent=2))
        else:
            print_markdown(rows)


if __name__ == "__main__":
    main()
