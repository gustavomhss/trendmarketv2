"""Merkle append-only writer for oracle batches."""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List, Mapping, Sequence

BATCH_DIR = Path("out/evidence/S7_event_model")
BATCH_DIR.mkdir(parents=True, exist_ok=True)


@dataclass(frozen=True)
class MerkleBatch:
    batch_ts: str
    count: int
    merkle_root: str
    leaves: Sequence[str]
    leaf_ids: Sequence[str]


def _canonical_event_bytes(event: Mapping[str, object]) -> bytes:
    return json.dumps(event, sort_keys=True, separators=(",", ":")).encode("utf-8")


def hash_event(event: Mapping[str, object]) -> str:
    """Compute the canonical SHA-256 hash for a normalised event."""
    return hashlib.sha256(_canonical_event_bytes(event)).hexdigest()


def _combine_hash(left: bytes, right: bytes) -> bytes:
    return hashlib.sha256(left + right).digest()


def _build_merkle(leaves: List[str]) -> str:
    if not leaves:
        return hashlib.sha256(b"").hexdigest()
    level = [bytes.fromhex(leaf) for leaf in leaves]
    while len(level) > 1:
        next_level: List[bytes] = []
        for idx in range(0, len(level), 2):
            left = level[idx]
            right = level[idx + 1] if idx + 1 < len(level) else level[idx]
            next_level.append(_combine_hash(left, right))
        level = next_level
    return level[0].hex()


def _ensure_monotonic(proof_path: Path, batch_ts: str) -> None:
    if not proof_path.exists():
        return
    with proof_path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    previous_ts = data.get("ts")
    if isinstance(previous_ts, str) and previous_ts > batch_ts:
        raise RuntimeError("Append-only proof regression: batch timestamp older than recorded state")


def write_batch(events: Iterable[Mapping[str, object]], *, batch_ts: datetime | None = None) -> MerkleBatch:
    batch_time = batch_ts.astimezone(timezone.utc) if batch_ts else datetime.now(timezone.utc)
    canonical_ts = batch_time.replace(microsecond=0).isoformat().replace("+00:00", "Z")

    events_list = sorted((dict(event) for event in events), key=lambda item: item["id"])
    leaves = [hash_event(event) for event in events_list]
    leaf_ids = [event["id"] for event in events_list]
    merkle_root = _build_merkle(leaves)

    batch_record = {
        "batch_ts": canonical_ts,
        "count": len(events_list),
        "merkle_root": merkle_root,
        "leaves": leaves,
        "leaf_ids": leaf_ids,
    }

    BATCH_DIR.mkdir(parents=True, exist_ok=True)
    file_ts = canonical_ts.replace(":", "").replace("+00:00", "Z")
    batch_path = BATCH_DIR / f"batch_{file_ts}.json"
    latest_path = BATCH_DIR / "batch_latest.json"
    with batch_path.open("w", encoding="utf-8") as handle:
        json.dump(batch_record, handle, ensure_ascii=False, indent=2)
    with latest_path.open("w", encoding="utf-8") as handle:
        json.dump(batch_record, handle, ensure_ascii=False, indent=2)

    proof_path = BATCH_DIR / "proof_append_only.json"
    _ensure_monotonic(proof_path, canonical_ts)
    with proof_path.open("w", encoding="utf-8") as handle:
        json.dump({"latest_root": merkle_root, "ts": canonical_ts}, handle, ensure_ascii=False, indent=2)

    return MerkleBatch(
        batch_ts=canonical_ts,
        count=len(events_list),
        merkle_root=merkle_root,
        leaves=tuple(leaves),
        leaf_ids=tuple(leaf_ids),
    )
