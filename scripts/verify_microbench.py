#!/usr/bin/env python3
"""Valida limites Knuth para microbenchmarks."""

from __future__ import annotations

import json
import re
import sys

LIMITS = {
    "engine::dec_paths::match_core": (1.20, 0.15),
    "engine::dec_paths::route_fast": (0.70, 0.10),
    "engine::dec_paths::twap_update": (0.45, 0.08),
}

PATTERN = re.compile(
    r"(?P<name>engine::[\w:]+)\s+time:\s+(?P<mean>[0-9.]+)\s+ms\s+\(σ=(?P<std>[0-9.]+)"
)


def parse(path: str) -> dict[str, tuple[float, float]]:
    metrics: dict[str, tuple[float, float]] = {}
    with open(path, "r", encoding="utf-8") as handle:
        for line in handle:
            match = PATTERN.search(line)
            if match:
                metrics[match.group("name")] = (
                    float(match.group("mean")),
                    float(match.group("std")),
                )
    return metrics


def main() -> None:
    if len(sys.argv) != 2:
        print("Uso: verify_microbench.py <microbench.txt>")
        sys.exit(2)
    metrics = parse(sys.argv[1])
    failures: dict[str, dict[str, float]] = {}
    for name, (mean, stddev) in metrics.items():
        if name in LIMITS:
            limit_mean, limit_std = LIMITS[name]
            if mean > limit_mean or stddev > limit_std:
                failures[name] = {
                    "mean": mean,
                    "stddev": stddev,
                    "limit_mean": limit_mean,
                    "limit_std": limit_std,
                }
    if failures:
        print(json.dumps({"allow-flakiness": 0, "failures": failures}, indent=2))
        sys.exit(1)
    print(json.dumps({"allow-flakiness": 0, "status": "ok"}, indent=2))


if __name__ == "__main__":
    main()
