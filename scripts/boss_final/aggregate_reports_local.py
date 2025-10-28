#!/usr/bin/env python3
"""Aggregate guard stage reports from local artifacts."""

from __future__ import annotations

import json
import os
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

RUNNER_TEMP = Path(os.environ.get("RUNNER_TEMP", "."))
ARTS_DIR = Path(os.environ.get("ARTS_DIR") or RUNNER_TEMP / "boss-arts")
OUT_DIR = Path(os.environ.get("REPORT_DIR") or RUNNER_TEMP / "boss-aggregate")


def _load_report(path: Path) -> List[Dict[str, Any]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 - safe aggregation
        return [{"name": "unknown", "status": "error", "errors": [str(exc)]}]
    if isinstance(data, dict) and isinstance(data.get("stages"), list):
        return [entry for entry in data["stages"] if isinstance(entry, dict)]
    return []


def collect_stage_results(root: Path) -> List[Dict[str, Any]]:
    results: List[Dict[str, Any]] = []
    if not root.exists():
        return results
    for report_path in root.rglob("report.json"):
        results.extend(_load_report(report_path))
    return results


def ensure_missing_stages(results: List[Dict[str, Any]]) -> None:
    present = {entry.get("name") for entry in results}
    for index in range(1, 7):
        name = f"s{index}"
        if name not in present:
            results.append(
                {"name": name, "status": "missing", "errors": ["artifact not found"]}
            )


def write_aggregate(results: List[Dict[str, Any]], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    aggregate: Dict[str, Any] = {"stages": results}

    version: int | None = None
    schema_raw = aggregate.get("schema")
    if isinstance(schema_raw, str):
        match = re.search(r"@(\d+)$", schema_raw)
        if match:
            try:
                version = int(match.group(1))
            except Exception:  # noqa: BLE001 - defensive parsing
                version = None
    if version is None:
        schema_version_raw = aggregate.get("schema_version")
        try:
            version = int(str(schema_version_raw))
        except Exception:
            version = None
    if version is None:
        version = 1

    now = (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )
    aggregate["schema"] = f"boss_final.report@{version}"
    aggregate["schema_version"] = version
    aggregate.setdefault("timestamp_utc", now)
    aggregate.setdefault("generated_at", aggregate["timestamp_utc"])

    payload = json.dumps(aggregate, ensure_ascii=False, indent=2) + "\n"

    (out_dir / "report.json").write_text(payload, encoding="utf-8")

    local_dir = Path("out/boss_final")
    local_dir.mkdir(parents=True, exist_ok=True)
    (local_dir / "report.local.json").write_text(payload, encoding="utf-8")


def summarize_status(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    status = {
        entry["name"]: str(entry.get("status", "missing")).upper()
        for entry in results
        if "name" in entry
    }
    overall = "FAIL" if any(value != "PASSED" for value in status.values()) else "PASS"
    return {"status": overall, "stages": status}


def main() -> int:
    results = collect_stage_results(ARTS_DIR)
    ensure_missing_stages(results)
    write_aggregate(results, OUT_DIR)
    summary = summarize_status(results)
    print(json.dumps(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
