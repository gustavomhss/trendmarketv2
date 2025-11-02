from __future__ import annotations

import argparse
import hashlib
import json
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Iterable, List, Optional

BATCH_PATH = Path("out/normalized/batch.json")
DEFAULT_LOG = Path("data/log/log.jsonl")
DEFAULT_OUT = Path("out/evidence/T7_append_only/append_only_report.json")


class AppendOnlyError(RuntimeError):
    def __init__(self, message: str, exit_code: int) -> None:
        super().__init__(message)
        self.exit_code = exit_code


def load_log(path: Path) -> List[dict]:
    entries: List[dict] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            entries.append(json.loads(line))
    return entries


def parse_ts(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(UTC)


def _build_violation(name: str, *, index: Optional[int] = None, **extra: object) -> dict:
    payload: dict[str, object] = {"name": name}
    if index is not None:
        payload["index"] = index
    payload.update(extra)
    return payload


def guard_append_only(log_entries: List[dict], batch: dict, batch_bytes: bytes) -> dict:
    violations: List[dict] = []
    expected_index: Optional[int] = None
    prev_root: Optional[str] = None
    batch_created = parse_ts(batch["created_at"]) if "created_at" in batch else None
    batch_root = batch.get("root")
    batch_sha = hashlib.sha256(batch_bytes).hexdigest()

    for entry in log_entries:
        index = entry.get("index")
        root = entry.get("root")
        entry_prev = entry.get("prev_root")
        created_at = entry.get("created_at")
        batch_sha_entry = entry.get("batch_sha256")

        if expected_index is None:
            expected_index = index
            if expected_index != 1:
                violations.append(_build_violation("reorder_detected", index=index))
        else:
            expected_index += 1
            if index != expected_index:
                violations.append(_build_violation("reorder_detected", index=index))
        if prev_root is not None and entry_prev != prev_root:
            violations.append(_build_violation("prev_root_mismatch", index=index))
        prev_root = root

        if created_at and batch_created and parse_ts(str(created_at)) < batch_created:
            violations.append(_build_violation("created_at_regression", index=index))

        if batch_sha_entry != batch_sha:
            violations.append(_build_violation("batch_sha256_mismatch", index=index))

    if batch_root and prev_root != batch_root:
        violations.append(
            _build_violation(
                "tip_root_mismatch",
                expected=batch_root,
                actual=prev_root,
            )
        )

    return {
        "ok": not violations,
        "violations": len(violations),
        "details": violations,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Validate append-only Merkle log")
    parser.add_argument("--log", default=str(DEFAULT_LOG))
    parser.add_argument("--batch", default=str(BATCH_PATH))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    start = time.monotonic()
    log_path = Path(args.log)
    batch_path = Path(args.batch)
    if not log_path.exists() or not batch_path.exists():
        raise SystemExit(61)
    log_entries = load_log(log_path)
    batch_bytes = batch_path.read_bytes()
    batch = json.loads(batch_bytes.decode("utf-8"))
    payload = guard_append_only(log_entries, batch, batch_bytes)
    payload["duration_ms"] = int((time.monotonic() - start) * 1000)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")
    if not payload["ok"]:
        has_reorder = any(
            item["name"] in {"reorder_detected", "created_at_regression"}
            for item in payload["details"]
        )
        exit_code = 63 if has_reorder else 62
        print(json.dumps(payload, separators=(",", ":")), flush=True)
        return exit_code
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
