from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Iterable, List

from scripts.normalizer.normalize_batch import Decimal4Encoder, canonical_json

DEFAULT_IN = Path("out/normalized/batch.json")
DEFAULT_OUT = Path("out/normalized/batch.json")


class MerkleError(RuntimeError):
    def __init__(self, message: str, exit_code: int = 41) -> None:
        super().__init__(message)
        self.exit_code = exit_code


def hash_record(record: dict) -> str:
    return hashlib.sha256(canonical_json(record)).hexdigest()


def build_leaves(records: Iterable[dict]) -> List[str]:
    return [hash_record(record) for record in records]


def pairwise_hash(left: str, right: str) -> str:
    return hashlib.sha256(bytes.fromhex(left) + bytes.fromhex(right)).hexdigest()


def compute_root(leaves: List[str]) -> str:
    if not leaves:
        raise MerkleError("no_leaves", 41)
    layer = leaves[:]
    while len(layer) > 1:
        if len(layer) % 2 == 1:
            layer.append(layer[-1])
        layer = [pairwise_hash(layer[i], layer[i + 1]) for i in range(0, len(layer), 2)]
    return layer[0]


def read_batch(path: Path) -> dict:
    if not path.exists():
        raise MerkleError("batch_missing", 41)
    return json.loads(path.read_text(encoding="utf-8"))


def write_batch(path: Path, data: dict) -> None:
    path.write_text(
        json.dumps(data, separators=(",", ":"), sort_keys=True, cls=Decimal4Encoder),
        encoding="utf-8",
    )


def build_merkle_tree(batch_path: Path, out_path: Path) -> dict:
    batch = read_batch(batch_path)
    records = batch.get("records")
    if not isinstance(records, list):
        raise MerkleError("invalid_batch_records", 41)
    leaves = build_leaves(records)
    root = compute_root(leaves)
    batch["leaves"] = leaves
    batch["root"] = root
    write_batch(out_path, batch)
    return batch


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Compute Merkle root for canonical batch")
    parser.add_argument("--in", dest="input", default=str(DEFAULT_IN))
    parser.add_argument("--out", dest="output", default=str(DEFAULT_OUT))
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        build_merkle_tree(Path(args.input), Path(args.output))
    except MerkleError as exc:
        payload = {"ok": False, "exit_code": exc.exit_code, "error": str(exc)}
        print(json.dumps(payload, separators=(",", ":")), flush=True)
        return exc.exit_code
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
