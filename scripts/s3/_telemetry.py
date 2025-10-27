#!/usr/bin/env python3
"""Shared helpers for S3 scripts evidence/telemetry emission."""

from __future__ import annotations

import json
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict

import os

EVIDENCE_ROOT = Path(os.getenv("MBP_EVIDENCE_DIR", "out/s3_gatecheck/evidence"))


def ensure_evidence_dir() -> Path:
    EVIDENCE_ROOT.mkdir(parents=True, exist_ok=True)
    return EVIDENCE_ROOT


def _timestamp() -> str:
    return datetime.now(tz=timezone.utc).isoformat()


class TelemetryEmitter:
    """Simple JSONL span/counter emitter for gatecheck evidence."""

    def __init__(self, name: str) -> None:
        ensure_evidence_dir()
        safe = name.replace("/", "_")
        self.path = EVIDENCE_ROOT / f"telemetry_{safe}.jsonl"

    def emit(self, event: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        record = {
            "trace_id": uuid.uuid4().hex,
            "ts": _timestamp(),
            "event": event,
            "payload": payload,
        }
        with self.path.open("a", encoding="utf-8") as fp:
            fp.write(json.dumps(record, ensure_ascii=False) + "\n")
        return record


class AuditLog:
    """Append-only audit emitter used by multiple scripts."""

    def __init__(self, name: str) -> None:
        ensure_evidence_dir()
        safe = name.replace("/", "_")
        self.path = EVIDENCE_ROOT / f"audit_{safe}.jsonl"

    def append(self, record: Dict[str, Any]) -> None:
        data = {
            "ts": _timestamp(),
            **record,
        }
        with self.path.open("a", encoding="utf-8") as fp:
            fp.write(json.dumps(data, ensure_ascii=False) + "\n")


__all__ = ["TelemetryEmitter", "AuditLog", "ensure_evidence_dir"]
