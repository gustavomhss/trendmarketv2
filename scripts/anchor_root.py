#!/usr/bin/env python3
"""Calcula raiz de Merkle determinística para o Evidence Pack."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from dataclasses import dataclass
from typing import Iterable, List


@dataclass(frozen=True)
class Leaf:
    path: str
    digest: str

    @staticmethod
    def from_path(path: str) -> "Leaf":
        hasher = hashlib.sha256()
        with open(path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                hasher.update(chunk)
        digest = hasher.hexdigest()
        return Leaf(path=os.path.relpath(path), digest=digest)


def pairwise(items: List[str]) -> List[str]:
    if len(items) % 2 == 1:
        items.append(items[-1])
    next_level: List[str] = []
    for i in range(0, len(items), 2):
        combined = items[i] + items[i + 1]
        next_level.append(hashlib.sha256(combined.encode()).hexdigest())
    return next_level


def merkle_root(leaves: Iterable[Leaf]) -> dict:
    ordered = sorted(leaves, key=lambda leaf: leaf.path)
    if not ordered:
        raise ValueError("Nenhum arquivo fornecido para ancoragem")
    level = [leaf.digest for leaf in ordered]
    proof = {leaf.path: leaf.digest for leaf in ordered}
    while len(level) > 1:
        level = pairwise(level)
    return {"root": level[0], "leaves": proof, "count": len(proof)}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Calcula Merkle root para arquivos")
    parser.add_argument("paths", nargs="+", help="Lista de arquivos para incluir")
    return parser.parse_args()


def expand(paths: Iterable[str]) -> List[str]:
    expanded: List[str] = []
    for path in paths:
        if os.path.isdir(path):
            for root, _, files in os.walk(path):
                for name in files:
                    expanded.append(os.path.join(root, name))
        else:
            expanded.append(path)
    return expanded


def main() -> None:
    args = parse_args()
    files = expand(args.paths)
    leaves = [Leaf.from_path(path) for path in files]
    output = merkle_root(leaves)
    json.dump(output, sys.stdout, indent=2)


if __name__ == "__main__":
    main()
