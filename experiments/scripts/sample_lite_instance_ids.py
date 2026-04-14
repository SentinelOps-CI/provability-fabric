#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Deterministic sample of N instance_ids from SWE-bench Lite (test split).
# Uses a fixed seed and round-robin across repos so the same list is reproduced
# and diversity across repos is preferred. Optionally excludes known broken-harness IDs.
#
# Usage:
#   python experiments/scripts/sample_lite_instance_ids.py [--count 20] [--seed 42] [--out path]
#
# Output: one instance_id per line (for use with --instance_ids id1,id2,... or by reading lines).

from __future__ import annotations

import argparse
import random
import sys
from pathlib import Path


# Optional: add known broken-harness instance_ids here (or load from file) to exclude from pool.
BROKEN_HARNESS_IDS: set[str] = set()


def load_lite_test_instance_ids() -> list[tuple[str, str]]:
    """Load (instance_id, repo) for SWE-bench Lite test split."""
    try:
        from datasets import load_dataset
    except ImportError:
        raise SystemExit(
            "HuggingFace 'datasets' is required. Install with: pip install datasets"
        ) from None

    ds = load_dataset("princeton-nlp/SWE-bench_Lite", split="test")
    out: list[tuple[str, str]] = []
    for row in ds:
        rec = dict(row)
        iid = str(rec.get("instance_id", rec.get("id", "")))
        repo = str(rec.get("repo", ""))
        if iid:
            out.append((iid, repo))
    return out


def sample_with_repo_diversity(
    pairs: list[tuple[str, str]],
    count: int,
    seed: int,
    exclude: set[str] | None = None,
) -> list[str]:
    """
    Deterministic sample of `count` instance_ids, preferring one per repo (round-robin).
    Excluded IDs are removed from the pool before sampling.
    """
    exclude = exclude or set()
    pool = [(iid, repo) for iid, repo in pairs if iid not in exclude]
    if not pool:
        return []

    # Group by repo; sort repos and instance_ids for determinism
    by_repo: dict[str, list[str]] = {}
    for iid, repo in pool:
        by_repo.setdefault(repo, []).append(iid)
    for repo in by_repo:
        by_repo[repo].sort()
    repos = sorted(by_repo.keys())

    # Round-robin: take one from each repo per round until we have `count`
    rng = random.Random(seed)
    # Shuffle repo order within each round for randomness, but seed fixes it
    result: list[str] = []
    round_index = 0
    while len(result) < count:
        # Order repos randomly within this round (deterministic given seed)
        order = repos.copy()
        rng.shuffle(order)
        for repo in order:
            ids_in_repo = by_repo[repo]
            if round_index < len(ids_in_repo):
                result.append(ids_in_repo[round_index])
                if len(result) >= count:
                    break
        round_index += 1
        if round_index >= max(len(by_repo[r]) for r in repos):
            break

    return result[:count]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Sample deterministic instance_ids from SWE-bench Lite (test) with repo diversity."
    )
    parser.add_argument(
        "--count",
        type=int,
        default=20,
        help="Number of instance_ids to sample (default: 20)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="Random seed for reproducibility (default: 42)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output file (default: experiments/exp-step2-lite-smoke/instance_ids.txt)",
    )
    parser.add_argument(
        "--exclude-file",
        type=Path,
        default=None,
        help="Optional file with one instance_id per line to exclude (e.g. broken harness)",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent.parent
    out_path = args.out or (repo_root / "experiments" / "exp-step2-lite-smoke" / "instance_ids.txt")

    exclude = set(BROKEN_HARNESS_IDS)
    if args.exclude_file and args.exclude_file.exists():
        exclude |= {line.strip() for line in args.exclude_file.read_text().splitlines() if line.strip()}

    pairs = load_lite_test_instance_ids()
    if len(pairs) < args.count:
        print(
            f"Warning: only {len(pairs)} instances in Lite test; requested {args.count}",
            file=sys.stderr,
        )
    ids = sample_with_repo_diversity(pairs, args.count, args.seed, exclude)
    if len(ids) < args.count:
        print(
            f"Warning: sampled {len(ids)} instance_ids (excludes or pool size)",
            file=sys.stderr,
        )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(ids) + ("\n" if ids else ""), encoding="utf-8")
    print(f"Wrote {len(ids)} instance_ids to {out_path}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
