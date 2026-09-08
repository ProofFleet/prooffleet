#!/usr/bin/env python3
"""Monte Carlo data for Erdős Problem 1144.

For each trial, independently sample signs at the primes and extend them completely
multiplicatively.  The smallest-prime-factor recurrence

    f(n) = f(spf(n)) * f(n / spf(n))

computes all values through ``N`` in linear time after a shared sieve.  NumPy fixes
the random-number generator (PCG64), and Numba makes the requested ``N=10^7`` run
practical without changing the recurrence.

Tested dependencies: NumPy 2.1.3 and Numba 0.61.0.
"""

from __future__ import annotations

import argparse
import json
import math
import platform
import sys
import time
from pathlib import Path
from typing import Any, Sequence

try:
    import numpy as np
    from numba import njit
except ImportError as exc:  # pragma: no cover - dependency error is environment-specific
    raise SystemExit(
        "This script requires NumPy and Numba. Reproduce the recorded run with "
        "`python3 -m pip install numpy==2.1.3 numba==0.61.0`."
    ) from exc


@njit
def simulate_one(
    spf: np.ndarray, prime_sign: np.ndarray, checkpoints: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Return sums and running extrema at each checkpoint for one sample."""
    limit = len(spf) - 1
    values = np.empty(limit + 1, dtype=np.int8)
    values[0] = 1
    values[1] = 1

    sums = np.empty(len(checkpoints), dtype=np.int64)
    running_max = np.empty(len(checkpoints), dtype=np.float64)
    running_min = np.empty(len(checkpoints), dtype=np.float64)
    max_at = np.empty(len(checkpoints), dtype=np.int64)
    min_at = np.empty(len(checkpoints), dtype=np.int64)

    partial = 0
    largest = -1.0e300
    smallest = 1.0e300
    largest_at = 0
    smallest_at = 0
    checkpoint_index = 0

    for n in range(1, limit + 1):
        if n > 1:
            p = spf[n]
            values[n] = prime_sign[p] * values[n // p]
        partial += int(values[n])
        normalized = partial / math.sqrt(n)
        if normalized > largest:
            largest = normalized
            largest_at = n
        if normalized < smallest:
            smallest = normalized
            smallest_at = n

        if n == checkpoints[checkpoint_index]:
            sums[checkpoint_index] = partial
            running_max[checkpoint_index] = largest
            running_min[checkpoint_index] = smallest
            max_at[checkpoint_index] = largest_at
            min_at[checkpoint_index] = smallest_at
            checkpoint_index += 1
            if checkpoint_index == len(checkpoints):
                break

    return sums, running_max, running_min, max_at, min_at


def smallest_prime_factors(limit: int) -> tuple[np.ndarray, np.ndarray]:
    """Sieve the smallest prime factor of every integer through ``limit``."""
    spf = np.zeros(limit + 1, dtype=np.int32)
    for p in range(2, math.isqrt(limit) + 1):
        if spf[p] == 0:
            multiples = spf[p * p :: p]
            multiples[multiples == 0] = p

    primes = np.flatnonzero(spf[2:] == 0).astype(np.int64) + 2
    spf[primes] = primes
    return spf, primes.astype(np.int32)


def parse_checkpoints(specification: str | None, limit: int) -> np.ndarray:
    """Parse comma-separated checkpoints, or use powers of ten plus ``limit``."""
    if specification:
        points = [int(value.replace("_", "")) for value in specification.split(",")]
    else:
        points = []
        power = 100
        while power <= limit:
            points.append(power)
            power *= 10
        points.append(limit)

    points = sorted(set(points))
    if not points or points[0] < 1 or points[-1] > limit:
        raise ValueError("checkpoints must be nonempty integers in [1, N]")
    if points[-1] != limit:
        points.append(limit)
    return np.asarray(points, dtype=np.int64)


def summary(values: np.ndarray) -> dict[str, float | int]:
    """Stable descriptive statistics used throughout the JSON report."""
    quantiles = np.quantile(values, [0.05, 0.25, 0.5, 0.75, 0.95])
    return {
        "count": int(len(values)),
        "mean": float(np.mean(values)),
        "sample_std": float(np.std(values, ddof=1)) if len(values) > 1 else 0.0,
        "min": float(np.min(values)),
        "q05": float(quantiles[0]),
        "q25": float(quantiles[1]),
        "median": float(quantiles[2]),
        "q75": float(quantiles[3]),
        "q95": float(quantiles[4]),
        "max": float(np.max(values)),
    }


def run_experiment(
    limit: int, trials: int, seed: int, checkpoints: np.ndarray, quiet: bool
) -> dict[str, Any]:
    """Run all trials and return a JSON-serializable report."""
    started = time.perf_counter()
    sieve_started = time.perf_counter()
    spf, primes = smallest_prime_factors(limit)
    sieve_seconds = time.perf_counter() - sieve_started

    shape = (trials, len(checkpoints))
    sums = np.empty(shape, dtype=np.int64)
    running_max = np.empty(shape, dtype=np.float64)
    running_min = np.empty(shape, dtype=np.float64)
    max_at = np.empty(shape, dtype=np.int64)
    min_at = np.empty(shape, dtype=np.int64)

    child_seeds = np.random.SeedSequence(seed).spawn(trials)
    trial_started = time.perf_counter()
    for trial, child_seed in enumerate(child_seeds):
        generator = np.random.default_rng(child_seed)
        prime_sign = np.ones(limit + 1, dtype=np.int8)
        bits = generator.integers(0, 2, size=len(primes), dtype=np.int8)
        prime_sign[primes] = bits * 2 - 1
        result = simulate_one(spf, prime_sign, checkpoints)
        sums[trial], running_max[trial], running_min[trial], max_at[trial], min_at[trial] = result
        if not quiet:
            print(f"trial {trial + 1}/{trials}", file=sys.stderr, flush=True)
    trial_seconds = time.perf_counter() - trial_started

    checkpoint_reports: list[dict[str, Any]] = []
    for index, checkpoint_value in enumerate(checkpoints):
        n = int(checkpoint_value)
        root_n = math.sqrt(n)
        normalized = sums[:, index] / root_n
        square_bias = math.isqrt(n) / root_n
        centered = normalized - square_bias
        log_log_n = math.log(math.log(n)) if n > 1 else None
        harper_factor = log_log_n ** 0.25 if log_log_n is not None and log_log_n > 0 else None
        checkpoint_reports.append(
            {
                "N": n,
                "log_log_N": log_log_n,
                "deterministic_square_mean_over_sqrt_N": square_bias,
                "harper_comparator_loglog_quarter_factor": harper_factor,
                "harper_comparator_normalized_scale":
                    1.0 / harper_factor if harper_factor is not None else None,
                "atherfold_comparator_log_N": math.log(n),
                "S_over_sqrt_N": summary(normalized),
                "centered_S_over_sqrt_N": summary(centered),
                "running_max_S_over_sqrt_n": summary(running_max[:, index]),
                "running_max_div_loglog_quarter":
                    summary(running_max[:, index] / harper_factor)
                    if harper_factor is not None else None,
                "running_min_S_over_sqrt_n": summary(running_min[:, index]),
            }
        )

    final_index = len(checkpoints) - 1
    final_root = math.sqrt(limit)
    final_square_bias = math.isqrt(limit) / final_root
    trial_reports = [
        {
            "trial": trial,
            "spawn_key": list(child_seeds[trial].spawn_key),
            "S_N": int(sums[trial, final_index]),
            "S_N_over_sqrt_N": float(sums[trial, final_index] / final_root),
            "centered_S_N_over_sqrt_N": float(
                sums[trial, final_index] / final_root - final_square_bias
            ),
            "running_max": float(running_max[trial, final_index]),
            "running_max_at": int(max_at[trial, final_index]),
            "running_min": float(running_min[trial, final_index]),
            "running_min_at": int(min_at[trial, final_index]),
        }
        for trial in range(trials)
    ]

    return {
        "metadata": {
            "problem": "Erdos 1144",
            "model": "independent prime signs, extended completely multiplicatively",
            "N": limit,
            "trials": trials,
            "seed": seed,
            "rng": "numpy.random.PCG64 via SeedSequence.spawn",
            "sign_encoding": "bit 0 -> -1; bit 1 -> +1",
            "python": platform.python_version(),
            "numpy": np.__version__,
            "numba": __import__("numba").__version__,
            "prime_count": int(len(primes)),
            "checkpoints": checkpoints.tolist(),
            "sieve_seconds": sieve_seconds,
            "trial_seconds": trial_seconds,
            "total_seconds": time.perf_counter() - started,
        },
        "checkpoint_summaries": checkpoint_reports,
        "final_trial_values": trial_reports,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, default=10_000_000, help="largest sampled integer")
    parser.add_argument("--trials", type=int, default=256, help="number of independent samples")
    parser.add_argument("--seed", type=int, default=1144, help="root SeedSequence entropy")
    parser.add_argument(
        "--checkpoints",
        help="comma-separated N values; defaults to powers of ten from 100 through N",
    )
    parser.add_argument("--output", type=Path, help="write JSON here instead of standard output")
    parser.add_argument("--quiet", action="store_true", help="suppress per-trial progress")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.N < 2:
        raise SystemExit("N must be at least 2")
    if args.trials < 1:
        raise SystemExit("trials must be positive")
    try:
        checkpoints = parse_checkpoints(args.checkpoints, args.N)
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc

    report = run_experiment(args.N, args.trials, args.seed, checkpoints, args.quiet)
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
        if not args.quiet:
            print(args.output, file=sys.stderr)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
