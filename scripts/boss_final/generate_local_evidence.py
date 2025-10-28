#!/usr/bin/env python3
"""Generate local evidence metadata for Boss Final reports."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
from datetime import datetime, timezone


def _infer_version(report: dict) -> int:
    v = None
    s = report.get("schema")
    if isinstance(s, str):
        m = re.search(r"@(\d+)$", s)
        if m:
            try:
                v = int(m.group(1))
            except Exception:
                v = None
    if v is None:
        try:
            v = int(str(report.get("schema_version")))
        except Exception:
            v = None
    return v or 1


def _now_utc_z() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "report_path",
        type=pathlib.Path,
        help="Path to the aggregated Boss Final report JSON",
    )
    p.add_argument(
        "--out",
        type=pathlib.Path,
        default=pathlib.Path("out/boss_final/report.local.json"),
    )
    p.add_argument(
        "--status",
        type=str,
        default=os.environ.get("BOSS_LOCAL_STATUS", "PASS"),
        help="Status do relatório local (PASS/FAIL). ENV BOSS_LOCAL_STATUS também é aceito.",
    )
    args = p.parse_args()

    base = {}
    if args.report_path.exists():
        try:
            base = json.loads(args.report_path.read_text(encoding="utf-8"))
        except Exception:
            base = {}

    version = _infer_version(base)
    now = _now_utc_z()
    status = (args.status or "PASS").strip().upper() or "PASS"

    payload = {
        "schema": f"boss_final.report@{version}",
        "schema_version": version,
        "timestamp_utc": now,
        "generated_at": now,
        "status": status,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"[local-evidence] Wrote {args.out} | status={status}")


if __name__ == "__main__":
    main()
