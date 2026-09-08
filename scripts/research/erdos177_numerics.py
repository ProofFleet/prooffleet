#!/usr/bin/env python3
"""Finite experiments for Erdős Problem 177.

For signs x[1], ..., x[N] and a step d, every arithmetic progression contained
in [1, N] is a contiguous interval in one residue class modulo d.  Its largest
absolute sum is therefore the range (maximum minus minimum) of the prefix sums
on that residue class.  This script uses that identity for exact O(ND) profile
evaluation and for an incremental simulated-annealing search.

The ``balance`` commands implement the Phase-2 finite residue-prefix experiment.
They freeze half of the remaining prefix in each round, never revisit earlier
signs, and report the exact normalized anchored-prefix barrier after every
round.  Search decisions may use a smaller step cutoff, but the selected final
witness is always evaluated at every step through N.

The search output is an achieved upper bound for the finite instance, not a
certificate of optimality.  The ``exact`` command does certify the optimum for
small N by exhaustive enumeration (fixing the first sign by global symmetry).

Only the Python standard library is required.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import itertools
import json
import math
import random
import sys
from dataclasses import dataclass
from typing import Iterable, Sequence


CandidateName = str


def validate_instance(n: int, d_max: int) -> None:
    """Reject empty or needlessly oversized finite instances."""
    if n < 1:
        raise ValueError("N must be positive")
    if d_max < 1:
        raise ValueError("D must be positive")
    if d_max > n:
        raise ValueError("D must be at most N (larger steps add only singleton APs)")


def ap_profile(signs: Sequence[int], d_max: int) -> list[int]:
    """Return exact h(d) for 1 <= d <= D on the finite interval [1, N]."""
    n = len(signs)
    validate_instance(n, d_max)
    profile: list[int] = []
    for d in range(1, d_max + 1):
        h_d = 0
        for residue in range(d):
            total = 0
            low = 0
            high = 0
            for index in range(residue, n, d):
                total += signs[index]
                low = min(low, total)
                high = max(high, total)
            h_d = max(h_d, high - low)
        profile.append(h_d)
    return profile


def brute_profile(signs: Sequence[int], d_max: int) -> list[int]:
    """Slow definition-level evaluator, used only to test ``ap_profile``."""
    n = len(signs)
    validate_instance(n, d_max)
    result: list[int] = []
    for d in range(1, d_max + 1):
        h_d = 0
        for start in range(n):
            total = 0
            for index in range(start, n, d):
                total += signs[index]
                h_d = max(h_d, abs(total))
        result.append(h_d)
    return result


def ratios(profile: Sequence[int], alpha: float) -> list[float]:
    return [h_d / (d**alpha) for d, h_d in enumerate(profile, start=1)]


def objective(profile: Sequence[int], alpha: float) -> float:
    """The card's finite objective max_d h(d) / d^alpha."""
    return max(ratios(profile, alpha), default=0.0)


def objective_key(profile: Sequence[int], alpha: float) -> tuple[float, float]:
    """Exact objective followed by a plateau-breaking sum of normalized bounds."""
    normalized = ratios(profile, alpha)
    return (max(normalized, default=0.0), sum(normalized))


@dataclass(frozen=True)
class ResiduePrefixTrace:
    """Exact finite-witness profile and barrier checkpoints."""

    profile: tuple[int, ...]
    barrier: float
    worst_d: int
    worst_r: int
    worst_m: int
    worst_sum: int
    round_barriers: tuple[float, ...]


def residue_prefix_trace(
    signs: Sequence[int], alpha: float, round_counts: Sequence[int] = ()
) -> ResiduePrefixTrace:
    """Evaluate the exact ``FiniteResiduePrefixWitness`` constraints.

    For each ``d``, the formal endpoint condition ``r + M*d <= N`` means that
    the last sampled index is at most ``N-d``.  The optional checkpoints treat
    positions at or beyond the colored count as zero, as in a partial coloring.
    Because earlier residue prefixes remain among the constraints, their
    barrier is monotone as more positions are frozen.
    """
    n = len(signs)
    if n < 1:
        raise ValueError("N must be positive")
    if any(value not in (-1, 0, 1) for value in signs):
        raise ValueError("partial-color values must be -1, 0, or +1")
    if any(left >= right for left, right in zip(round_counts, round_counts[1:])):
        raise ValueError("round counts must be strictly increasing")
    if round_counts and (round_counts[0] < 1 or round_counts[-1] > n):
        raise ValueError("round counts must lie in [1, N]")

    profile: list[int] = []
    barrier = -1.0
    worst = (1, 0, 1, signs[0])
    new_by_round = [0.0] * len(round_counts)
    for d in range(1, n + 1):
        h_d = 0
        # Only residues at most N-d can begin a nonempty constrained prefix.
        for residue in range(min(d, n - d + 1)):
            total = 0
            for index in range(residue, n - d + 1, d):
                total += signs[index]
                magnitude = abs(total)
                h_d = max(h_d, magnitude)
                normalized = magnitude / (d**alpha)
                if normalized > barrier:
                    barrier = normalized
                    worst = (d, residue, index // d + 1, total)
                if round_counts:
                    round_index = bisect.bisect_right(round_counts, index)
                    if round_index < len(round_counts):
                        new_by_round[round_index] = max(
                            new_by_round[round_index], normalized
                        )
        profile.append(h_d)

    round_barriers: list[float] = []
    running = 0.0
    for new_value in new_by_round:
        running = max(running, new_value)
        round_barriers.append(running)
    worst_d, worst_r, worst_m, worst_sum = worst
    return ResiduePrefixTrace(
        profile=tuple(profile),
        barrier=max(0.0, barrier),
        worst_d=worst_d,
        worst_r=worst_r,
        worst_m=worst_m,
        worst_sum=worst_sum,
        round_barriers=tuple(round_barriers),
    )


def brute_residue_prefix_profile(signs: Sequence[int]) -> list[int]:
    """Definition-level finite-witness evaluator used by the self-test."""
    n = len(signs)
    if n < 1:
        raise ValueError("N must be positive")
    result: list[int] = []
    for d in range(1, n + 1):
        h_d = 0
        for residue in range(d):
            total = 0
            m = 0
            while residue + (m + 1) * d <= n:
                total += signs[residue + m * d]
                h_d = max(h_d, abs(total))
                m += 1
        result.append(h_d)
    return result


def partial_round_counts(n: int, freeze_fraction: float) -> list[int]:
    """Freeze a fixed fraction of the remaining positions in every round."""
    if n < 1:
        raise ValueError("N must be positive")
    if not 0.0 < freeze_fraction <= 1.0:
        raise ValueError("freeze fraction must lie in (0, 1]")
    result: list[int] = []
    colored = 0
    while colored < n:
        newly_colored = max(1, math.ceil((n - colored) * freeze_fraction))
        colored = min(n, colored + newly_colored)
        result.append(colored)
    return result


class PrefixGreedyState:
    """A prefix-frozen, barrier-aware partial-coloring search state.

    Search decisions use steps through ``search_d_max``.  The returned witness
    is separately checked against every step through ``N``.
    """

    def __init__(self, n: int, search_d_max: int, alpha: float):
        validate_instance(n, search_d_max)
        self.n = n
        self.search_d_max = search_d_max
        self.alpha = alpha
        self.signs: list[int] = []
        self.totals = [[0] * d for d in range(1, search_d_max + 1)]
        self.profile = [0] * search_d_max
        self.barrier = 0.0

    def clone(self) -> PrefixGreedyState:
        result = object.__new__(PrefixGreedyState)
        result.n = self.n
        result.search_d_max = self.search_d_max
        result.alpha = self.alpha
        result.signs = list(self.signs)
        result.totals = [list(row) for row in self.totals]
        result.profile = list(self.profile)
        result.barrier = self.barrier
        return result

    def _choice(self, rng: random.Random) -> int:
        index = len(self.signs)
        active_d_max = min(self.search_d_max, self.n - index)
        plus_peak = self.barrier
        minus_peak = self.barrier
        plus_energy = 0.0
        minus_energy = 0.0
        for d in range(1, active_d_max + 1):
            current = self.totals[d - 1][index % d]
            plus_peak = max(plus_peak, abs(current + 1) / (d**self.alpha))
            minus_peak = max(minus_peak, abs(current - 1) / (d**self.alpha))
            weight = math.exp(rng.uniform(-0.35, 0.35)) / (d ** (2 * self.alpha))
            plus_energy += (2 * current + 1) * weight
            minus_energy += (-2 * current + 1) * weight
        plus_key = (plus_peak, plus_energy)
        minus_key = (minus_peak, minus_energy)
        if plus_key < minus_key:
            return 1
        if minus_key < plus_key:
            return -1
        return rng.choice((-1, 1))

    def extend_one(self, rng: random.Random) -> None:
        if len(self.signs) >= self.n:
            raise ValueError("the partial coloring is already complete")
        value = self._choice(rng)
        index = len(self.signs)
        self.signs.append(value)
        active_d_max = min(self.search_d_max, self.n - index)
        for d in range(1, active_d_max + 1):
            residue = index % d
            self.totals[d - 1][residue] += value
            magnitude = abs(self.totals[d - 1][residue])
            self.profile[d - 1] = max(self.profile[d - 1], magnitude)
            self.barrier = max(self.barrier, magnitude / (d**self.alpha))

    def key(self) -> tuple[float, float]:
        return objective_key(self.profile, self.alpha)


def finite_balancing_record(
    n: int,
    search_d_max: int,
    alpha: float,
    trials_per_round: int,
    seed: int,
    freeze_fraction: float,
    emit_signs: bool = False,
) -> dict[str, object]:
    """Search and exactly evaluate one finite residue-prefix witness."""
    validate_instance(n, search_d_max)
    if trials_per_round < 1:
        raise ValueError("trials per round must be positive")
    counts = partial_round_counts(n, freeze_fraction)
    state = PrefixGreedyState(n, search_d_max, alpha)
    search_rounds: list[dict[str, object]] = []
    for round_index, target in enumerate(counts, start=1):
        candidates: list[PrefixGreedyState] = []
        for trial in range(trials_per_round):
            candidate = state.clone()
            trial_seed = seed + round_index * 1_000_003 + trial * 104_729
            rng = random.Random(trial_seed)
            while len(candidate.signs) < target:
                candidate.extend_one(rng)
            candidates.append(candidate)
        state = min(candidates, key=lambda candidate: candidate.key())
        candidate_barriers = [candidate.barrier for candidate in candidates]
        search_rounds.append(
            {
                "round": round_index,
                "colored": target,
                "colored_fraction": target / n,
                "selected_search_barrier": state.barrier,
                "candidate_search_barrier_min": min(candidate_barriers),
                "candidate_search_barrier_max": max(candidate_barriers),
            }
        )

    trace = residue_prefix_trace(state.signs, alpha, counts)
    for record, full_barrier in zip(search_rounds, trace.round_barriers):
        record["full_barrier"] = full_barrier
    result: dict[str, object] = {
        "N": n,
        "alpha": alpha,
        "search_D": search_d_max,
        "trials_per_round": trials_per_round,
        "freeze_fraction": freeze_fraction,
        "seed": seed,
        "rounds": search_rounds,
        "best": {
            "barrier": trace.barrier,
            "search_barrier": state.barrier,
            "worst": {
                "d": trace.worst_d,
                "r": trace.worst_r,
                "M": trace.worst_m,
                "sum": trace.worst_sum,
            },
            "profile_d_1_through_16": list(trace.profile[:16]),
            "signs_sha256_16": signs_hash(state.signs),
        },
    }
    if emit_signs:
        best = result["best"]
        assert isinstance(best, dict)
        best["signs"] = "".join("+" if value > 0 else "-" for value in state.signs)
    return result


def signs_hash(signs: Sequence[int]) -> str:
    packed = bytes(1 if value > 0 else 0 for value in signs)
    return hashlib.sha256(packed).hexdigest()[:16]


def alternating(n: int) -> list[int]:
    return [1 if index % 2 == 0 else -1 for index in range(n)]


def thue_morse(n: int) -> list[int]:
    """Thue--Morse signs (-1)^popcount(k), with position n=k+1."""
    return [1 if index.bit_count() % 2 == 0 else -1 for index in range(n)]


def rudin_shapiro(n: int) -> list[int]:
    """Rudin--Shapiro signs from the parity of adjacent ``11`` bit pairs."""
    return [
        1 if (index & (index >> 1)).bit_count() % 2 == 0 else -1 for index in range(n)
    ]


def block_sequence(n: int, block_size: int) -> list[int]:
    if block_size < 1:
        raise ValueError("block size must be positive")
    return [1 if (index // block_size) % 2 == 0 else -1 for index in range(n)]


def random_sequence(n: int, rng: random.Random) -> list[int]:
    return [rng.choice((-1, 1)) for _ in range(n)]


def random_balancing(n: int, d_max: int, alpha: float, rng: random.Random) -> list[int]:
    """A randomized energy-balancing surrogate, not an implementation of Beck's proof.

    Positions are colored in increasing order.  At each position we choose the
    sign that decreases a randomly perturbed weighted quadratic energy of the
    current residue-class prefix sums.  Beck's theorem also balances vectors,
    but its infinite-dimensional partial-coloring argument is substantially
    stronger; the name here records only the motivating analogy.
    """
    validate_instance(n, d_max)
    partial = [[0] * d for d in range(1, d_max + 1)]
    signs: list[int] = []
    for index in range(n):
        linear_term = 0.0
        for d in range(1, d_max + 1):
            current = partial[d - 1][index % d]
            perturbation = math.exp(rng.uniform(-0.35, 0.35))
            linear_term += perturbation * current / (d ** (2.0 * alpha))
        if abs(linear_term) < 1e-15:
            value = rng.choice((-1, 1))
        else:
            value = -1 if linear_term > 0 else 1
        signs.append(value)
        for d in range(1, d_max + 1):
            partial[d - 1][index % d] += value
    return signs


def named_candidate(
    name: CandidateName,
    n: int,
    d_max: int,
    alpha: float,
    seed: int,
    block_size: int,
) -> list[int]:
    rng = random.Random(seed)
    if name == "alternating":
        return alternating(n)
    if name == "thue-morse":
        return thue_morse(n)
    if name == "rudin-shapiro":
        return rudin_shapiro(n)
    if name == "block":
        return block_sequence(n, block_size)
    if name == "random":
        return random_sequence(n, rng)
    if name == "random-balancing":
        return random_balancing(n, d_max, alpha, rng)
    raise ValueError(f"unknown candidate: {name}")


def candidate_record(
    name: str, signs: Sequence[int], d_max: int, alpha: float, emit_signs: bool = False
) -> dict[str, object]:
    profile = ap_profile(signs, d_max)
    record: dict[str, object] = {
        "candidate": name,
        "objective": objective(profile, alpha),
        "profile": profile,
        "signs_sha256_16": signs_hash(signs),
    }
    if emit_signs:
        record["signs"] = "".join("+" if value > 0 else "-" for value in signs)
    return record


@dataclass(frozen=True)
class FlipProposal:
    index: int
    new_ranges: tuple[int, ...]
    new_profile: tuple[int, ...]
    energy: float


class FlipState:
    """Exact profile state supporting tentative single-coordinate flips."""

    def __init__(self, signs: Sequence[int], d_max: int, alpha: float):
        validate_instance(len(signs), d_max)
        if any(value not in (-1, 1) for value in signs):
            raise ValueError("all entries must be -1 or +1")
        self.signs = list(signs)
        self.d_max = d_max
        self.alpha = alpha
        self.prefixes: list[list[list[int]]] = []
        self.class_ranges: list[list[int]] = []
        self.profile: list[int] = []
        self.max_counts: list[int] = []
        self.second_maxima: list[int] = []
        for d in range(1, d_max + 1):
            groups: list[list[int]] = []
            group_ranges: list[int] = []
            for residue in range(d):
                values = [0]
                for index in range(residue, len(signs), d):
                    values.append(values[-1] + signs[index])
                groups.append(values)
                group_ranges.append(max(values) - min(values))
            self.prefixes.append(groups)
            self.class_ranges.append(group_ranges)
            top, count, second = self._summarize(group_ranges)
            self.profile.append(top)
            self.max_counts.append(count)
            self.second_maxima.append(second)
        self.energy = self._energy(self.profile)

    @staticmethod
    def _summarize(values: Sequence[int]) -> tuple[int, int, int]:
        top = max(values)
        count = sum(value == top for value in values)
        second = max((value for value in values if value < top), default=0)
        return top, count, second

    def _energy(self, profile: Sequence[int]) -> float:
        """Max objective plus a small plateau-breaking average."""
        normalized = ratios(profile, self.alpha)
        return max(normalized) + 0.02 * sum(normalized) / self.d_max

    def propose(self, index: int) -> FlipProposal:
        if not 0 <= index < len(self.signs):
            raise IndexError(index)
        delta = -2 * self.signs[index]
        proposed_ranges: list[int] = []
        proposed_profile: list[int] = []
        for d in range(1, self.d_max + 1):
            residue = index % d
            rank = index // d
            prefix = self.prefixes[d - 1][residue]
            low = math.inf
            high = -math.inf
            for prefix_index, value in enumerate(prefix):
                shifted = value + delta if prefix_index > rank else value
                low = min(low, shifted)
                high = max(high, shifted)
            new_range = int(high - low)
            proposed_ranges.append(new_range)

            old_range = self.class_ranges[d - 1][residue]
            if old_range == self.profile[d - 1] and self.max_counts[d - 1] == 1:
                unchanged_max = self.second_maxima[d - 1]
            else:
                unchanged_max = self.profile[d - 1]
            proposed_profile.append(max(unchanged_max, new_range))
        return FlipProposal(
            index=index,
            new_ranges=tuple(proposed_ranges),
            new_profile=tuple(proposed_profile),
            energy=self._energy(proposed_profile),
        )

    def apply(self, proposal: FlipProposal) -> None:
        index = proposal.index
        delta = -2 * self.signs[index]
        self.signs[index] = -self.signs[index]
        for d in range(1, self.d_max + 1):
            residue = index % d
            rank = index // d
            prefix = self.prefixes[d - 1][residue]
            for prefix_index in range(rank + 1, len(prefix)):
                prefix[prefix_index] += delta
            self.class_ranges[d - 1][residue] = proposal.new_ranges[d - 1]
            top, count, second = self._summarize(self.class_ranges[d - 1])
            self.profile[d - 1] = top
            self.max_counts[d - 1] = count
            self.second_maxima[d - 1] = second
        self.energy = proposal.energy


def local_search(
    initial: Sequence[int],
    d_max: int,
    alpha: float,
    iterations: int,
    seed: int,
    start_temperature: float = 0.20,
    end_temperature: float = 0.002,
) -> tuple[list[int], list[int], int]:
    """Run deterministic-seed simulated annealing and return the best achieved state."""
    if iterations < 0:
        raise ValueError("iterations must be nonnegative")
    if not (0 < end_temperature <= start_temperature):
        raise ValueError("temperatures must satisfy 0 < end <= start")
    rng = random.Random(seed)
    state = FlipState(initial, d_max, alpha)
    best_signs = list(state.signs)
    best_profile = list(state.profile)
    best_key = objective_key(best_profile, alpha)
    accepted = 0
    for iteration in range(iterations):
        proposal = state.propose(rng.randrange(len(state.signs)))
        if iterations <= 1:
            temperature = end_temperature
        else:
            progress = iteration / (iterations - 1)
            temperature = start_temperature * (
                (end_temperature / start_temperature) ** progress
            )
        energy_delta = proposal.energy - state.energy
        if energy_delta <= 0 or rng.random() < math.exp(-energy_delta / temperature):
            state.apply(proposal)
            accepted += 1
            key = objective_key(state.profile, alpha)
            if key < best_key:
                best_key = key
                best_signs = list(state.signs)
                best_profile = list(state.profile)
    return best_signs, best_profile, accepted


def standard_candidates(
    n: int, d_max: int, alpha: float, seed: int
) -> dict[str, list[int]]:
    candidates = {
        "alternating": alternating(n),
        "thue-morse": thue_morse(n),
        "rudin-shapiro": rudin_shapiro(n),
        "random": random_sequence(n, random.Random(seed)),
        "random-balancing": random_balancing(n, d_max, alpha, random.Random(seed)),
    }
    for block_size in (2, 4, 8, 16):
        if block_size <= n:
            candidates[f"block-{block_size}"] = block_sequence(n, block_size)
    return candidates


def search_record(
    n: int,
    d_max: int,
    alpha: float,
    iterations: int,
    restarts: int,
    seed: int,
    emit_signs: bool = False,
) -> dict[str, object]:
    if restarts < 1:
        raise ValueError("restarts must be positive")
    candidates = standard_candidates(n, d_max, alpha, seed)
    candidate_records = [
        candidate_record(name, signs, d_max, alpha)
        for name, signs in candidates.items()
    ]
    candidate_records.sort(key=lambda item: (item["objective"], item["candidate"]))
    best_seed_name = str(candidate_records[0]["candidate"])

    best_signs: list[int] | None = None
    best_profile: list[int] | None = None
    best_key = (math.inf, math.inf)
    runs: list[dict[str, object]] = []
    for restart in range(restarts):
        run_seed = seed + 1_000_003 * restart
        if restart == 0:
            initial_name = best_seed_name
            initial = candidates[best_seed_name]
        elif restart % 2 == 1:
            initial_name = "random-balancing"
            initial = random_balancing(n, d_max, alpha, random.Random(run_seed))
        else:
            initial_name = "random"
            initial = random_sequence(n, random.Random(run_seed))
        found_signs, found_profile, accepted = local_search(
            initial, d_max, alpha, iterations, run_seed
        )
        key = objective_key(found_profile, alpha)
        runs.append(
            {
                "restart": restart,
                "seed": run_seed,
                "initial": initial_name,
                "accepted_flips": accepted,
                "objective": key[0],
                "profile": found_profile,
                "signs_sha256_16": signs_hash(found_signs),
            }
        )
        if key < best_key:
            best_key = key
            best_signs = found_signs
            best_profile = found_profile

    assert best_signs is not None and best_profile is not None
    result: dict[str, object] = {
        "N": n,
        "D": d_max,
        "alpha": alpha,
        "iterations_per_restart": iterations,
        "restarts": restarts,
        "seed": seed,
        "structured_candidates": candidate_records,
        "runs": runs,
        "best": {
            "objective": best_key[0],
            "profile": best_profile,
            "signs_sha256_16": signs_hash(best_signs),
        },
    }
    if emit_signs:
        best = result["best"]
        assert isinstance(best, dict)
        best["signs"] = "".join("+" if value > 0 else "-" for value in best_signs)
    return result


def exhaustive_search(n: int, d_max: int, alpha: float) -> dict[str, object]:
    """Certify the finite optimum by enumeration; intended only for N <= 20."""
    validate_instance(n, d_max)
    best_signs: list[int] | None = None
    best_profile: list[int] | None = None
    best_key = (math.inf, math.inf)
    checked = 0
    # Negating every sign preserves every discrepancy, so fix x[1] = +1.
    for tail in itertools.product((-1, 1), repeat=n - 1):
        signs = [1, *tail]
        profile = ap_profile(signs, d_max)
        key = objective_key(profile, alpha)
        checked += 1
        if key < best_key:
            best_key = key
            best_signs = signs
            best_profile = profile
    assert best_signs is not None and best_profile is not None
    return {
        "N": n,
        "D": d_max,
        "alpha": alpha,
        "certified_optimum": best_key[0],
        "profile": best_profile,
        "signs": "".join("+" if value > 0 else "-" for value in best_signs),
        "signs_sha256_16": signs_hash(best_signs),
        "assignments_checked_after_symmetry": checked,
    }


def parse_int_list(raw: str) -> list[int]:
    return [int(part.strip()) for part in raw.split(",") if part.strip()]


def parse_float_list(raw: str) -> list[float]:
    return [float(part.strip()) for part in raw.split(",") if part.strip()]


def print_suite_markdown(records: Sequence[dict[str, object]]) -> None:
    print(
        "| N | D | alpha | best structured | structured score | local-search score | hash |"
    )
    print("|---:|---:|---:|:---|---:|---:|:---|")
    for record in records:
        structured = record["structured_candidates"]
        best = record["best"]
        assert isinstance(structured, list) and isinstance(best, dict)
        first = structured[0]
        assert isinstance(first, dict)
        print(
            f"| {record['N']} | {record['D']} | {float(record['alpha']):g} "
            f"| {first['candidate']} | {float(first['objective']):.6f} "
            f"| {float(best['objective']):.6f} | `{best['signs_sha256_16']}` |"
        )
    print()
    for record in records:
        best = record["best"]
        assert isinstance(best, dict)
        profile = best["profile"]
        assert isinstance(profile, list)
        rendered = ", ".join(f"{d}:{value}" for d, value in enumerate(profile, start=1))
        print(f"- N={record['N']}, alpha={record['alpha']}: {rendered}")


def print_balancing_markdown(records: Sequence[dict[str, object]]) -> None:
    print(
        "| N | alpha | search D | full barrier | search barrier | worst (d,r,M,sum) | hash |"
    )
    print("|---:|---:|---:|---:|---:|:---|:---|")
    for record in records:
        best = record["best"]
        assert isinstance(best, dict)
        worst = best["worst"]
        assert isinstance(worst, dict)
        coordinate = f"({worst['d']},{worst['r']},{worst['M']},{worst['sum']})"
        print(
            f"| {record['N']} | {float(record['alpha']):g} | {record['search_D']} "
            f"| {float(best['barrier']):.6f} | {float(best['search_barrier']):.6f} "
            f"| `{coordinate}` | `{best['signs_sha256_16']}` |"
        )


def run_self_tests() -> None:
    rng = random.Random(177)
    for n in range(1, 13):
        for _ in range(20):
            signs = random_sequence(n, rng)
            d_max = rng.randint(1, n)
            assert ap_profile(signs, d_max) == brute_profile(signs, d_max)

    signs = random_sequence(37, rng)
    state = FlipState(signs, 12, 0.5)
    for _ in range(100):
        index = rng.randrange(len(signs))
        proposal = state.propose(index)
        expected_signs = list(state.signs)
        expected_signs[index] *= -1
        expected_profile = ap_profile(expected_signs, state.d_max)
        assert list(proposal.new_profile) == expected_profile
        state.apply(proposal)
        assert state.signs == expected_signs
        assert state.profile == expected_profile

    initial = random_sequence(40, random.Random(9))
    initial_key = objective_key(ap_profile(initial, 10), 0.5)
    _, found_profile, _ = local_search(initial, 10, 0.5, 200, 9)
    assert objective_key(found_profile, 0.5) <= initial_key

    for n in range(1, 14):
        signs = random_sequence(n, rng)
        counts = partial_round_counts(n, 0.5)
        trace = residue_prefix_trace(signs, 0.5, counts)
        expected_profile = brute_residue_prefix_profile(signs)
        assert list(trace.profile) == expected_profile
        assert math.isclose(trace.barrier, objective(expected_profile, 0.5))
        for count, barrier in zip(counts, trace.round_barriers):
            partial = [*signs[:count], *([0] * (n - count))]
            expected = objective(brute_residue_prefix_profile(partial), 0.5)
            assert math.isclose(barrier, expected)

    balancing = finite_balancing_record(40, 12, 0.5, 2, 177, 0.5, True)
    best = balancing["best"]
    rounds = balancing["rounds"]
    assert isinstance(best, dict) and isinstance(rounds, list)
    assert rounds[-1]["colored"] == 40
    barriers = [float(record["full_barrier"]) for record in rounds]
    assert barriers == sorted(barriers)
    rendered_signs = str(best["signs"])
    recovered = [1 if value == "+" else -1 for value in rendered_signs]
    assert math.isclose(
        float(best["barrier"]),
        objective(brute_residue_prefix_profile(recovered), 0.5),
    )
    print("self-test: OK")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    profile_parser = subparsers.add_parser(
        "profile", help="evaluate one named candidate"
    )
    profile_parser.add_argument("--N", dest="n", type=int, required=True)
    profile_parser.add_argument("--D", dest="d_max", type=int, required=True)
    profile_parser.add_argument("--alpha", type=float, default=0.5)
    profile_parser.add_argument(
        "--candidate",
        choices=(
            "alternating",
            "thue-morse",
            "rudin-shapiro",
            "block",
            "random",
            "random-balancing",
        ),
        required=True,
    )
    profile_parser.add_argument("--block-size", type=int, default=4)
    profile_parser.add_argument("--seed", type=int, default=177)
    profile_parser.add_argument("--emit-signs", action="store_true")

    search_parser = subparsers.add_parser(
        "search", help="compare candidates and run local search"
    )
    search_parser.add_argument("--N", dest="n", type=int, required=True)
    search_parser.add_argument("--D", dest="d_max", type=int, required=True)
    search_parser.add_argument("--alpha", type=float, default=0.5)
    search_parser.add_argument("--iterations", type=int, default=2_000)
    search_parser.add_argument("--restarts", type=int, default=2)
    search_parser.add_argument("--seed", type=int, default=177)
    search_parser.add_argument("--emit-signs", action="store_true")

    suite_parser = subparsers.add_parser(
        "suite", help="run the same search over several N, alpha"
    )
    suite_parser.add_argument("--Ns", default="256,1024,4096")
    suite_parser.add_argument("--D", dest="d_max", type=int, default=16)
    suite_parser.add_argument("--alphas", default="0.5")
    suite_parser.add_argument("--iterations", type=int, default=2_000)
    suite_parser.add_argument("--restarts", type=int, default=2)
    suite_parser.add_argument("--seed", type=int, default=177)
    suite_parser.add_argument("--format", choices=("json", "markdown"), default="json")

    exact_parser = subparsers.add_parser(
        "exact", help="certify a small optimum exhaustively"
    )
    exact_parser.add_argument("--N", dest="n", type=int, required=True)
    exact_parser.add_argument("--D", dest="d_max", type=int, required=True)
    exact_parser.add_argument("--alpha", type=float, default=0.5)
    exact_parser.add_argument("--max-N", dest="max_n", type=int, default=20)

    balance_parser = subparsers.add_parser(
        "balance", help="search one finite residue-prefix witness in freezing rounds"
    )
    balance_parser.add_argument("--N", dest="n", type=int, required=True)
    balance_parser.add_argument("--alpha", type=float, required=True)
    balance_parser.add_argument(
        "--search-D", dest="search_d_max", type=int, default=128
    )
    balance_parser.add_argument("--trials-per-round", type=int, default=4)
    balance_parser.add_argument("--freeze-fraction", type=float, default=0.5)
    balance_parser.add_argument("--seed", type=int, default=177)
    balance_parser.add_argument("--emit-signs", action="store_true")

    balance_suite_parser = subparsers.add_parser(
        "balance-suite", help="run finite residue-prefix searches over several N, alpha"
    )
    balance_suite_parser.add_argument("--Ns", default="256,1024,4096")
    balance_suite_parser.add_argument("--alphas", default="0.5,1,2,4,7")
    balance_suite_parser.add_argument(
        "--search-D", dest="search_d_max", type=int, default=128
    )
    balance_suite_parser.add_argument("--trials-per-round", type=int, default=4)
    balance_suite_parser.add_argument("--freeze-fraction", type=float, default=0.5)
    balance_suite_parser.add_argument("--seed", type=int, default=177)
    balance_suite_parser.add_argument(
        "--format", choices=("json", "markdown"), default="json"
    )

    subparsers.add_parser(
        "self-test", help="cross-check optimized and incremental evaluators"
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.command == "self-test":
            run_self_tests()
            return 0
        if args.command == "profile":
            validate_instance(args.n, args.d_max)
            signs = named_candidate(
                args.candidate,
                args.n,
                args.d_max,
                args.alpha,
                args.seed,
                args.block_size,
            )
            result = {
                "N": args.n,
                "D": args.d_max,
                "alpha": args.alpha,
                "seed": args.seed,
                **candidate_record(
                    args.candidate, signs, args.d_max, args.alpha, args.emit_signs
                ),
            }
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        if args.command == "search":
            validate_instance(args.n, args.d_max)
            result = search_record(
                args.n,
                args.d_max,
                args.alpha,
                args.iterations,
                args.restarts,
                args.seed,
                args.emit_signs,
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        if args.command == "suite":
            ns = parse_int_list(args.Ns)
            alphas = parse_float_list(args.alphas)
            if not ns or not alphas:
                raise ValueError(
                    "--Ns and --alphas must be nonempty comma-separated lists"
                )
            records = []
            for alpha in alphas:
                for n in ns:
                    validate_instance(n, args.d_max)
                    records.append(
                        search_record(
                            n,
                            args.d_max,
                            alpha,
                            args.iterations,
                            args.restarts,
                            args.seed,
                        )
                    )
            if args.format == "markdown":
                print_suite_markdown(records)
            else:
                print(json.dumps(records, indent=2, sort_keys=True))
            return 0
        if args.command == "exact":
            if args.n > args.max_n:
                raise ValueError(
                    f"refusing exhaustive search at N={args.n}; raise --max-N (current {args.max_n})"
                )
            print(
                json.dumps(exhaustive_search(args.n, args.d_max, args.alpha), indent=2)
            )
            return 0
        if args.command == "balance":
            result = finite_balancing_record(
                args.n,
                min(args.search_d_max, args.n),
                args.alpha,
                args.trials_per_round,
                args.seed,
                args.freeze_fraction,
                args.emit_signs,
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        if args.command == "balance-suite":
            ns = parse_int_list(args.Ns)
            alphas = parse_float_list(args.alphas)
            if not ns or not alphas:
                raise ValueError(
                    "--Ns and --alphas must be nonempty comma-separated lists"
                )
            records = []
            for alpha in alphas:
                for n in ns:
                    records.append(
                        finite_balancing_record(
                            n,
                            min(args.search_d_max, n),
                            alpha,
                            args.trials_per_round,
                            args.seed,
                            args.freeze_fraction,
                        )
                    )
            if args.format == "markdown":
                print_balancing_markdown(records)
            else:
                print(json.dumps(records, indent=2, sort_keys=True))
            return 0
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    raise AssertionError(f"unhandled command: {args.command}")


if __name__ == "__main__":
    raise SystemExit(main())
