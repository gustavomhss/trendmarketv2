#!/usr/bin/env python3
"""Generate local evidence metadata for Boss Final reports."""

from __future__ import annotations
import argparse
import json
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
    args = p.parse_args()

    base = {}
    if args.report_path.exists():
        try:
            base = json.loads(args.report_path.read_text(encoding="utf-8"))
        except Exception:
            base = {}

    version = _infer_version(base)
    now = (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )
    payload = {
        "schema": f"boss_final.report@{version}",
        "schema_version": version,
        "timestamp_utc": now,
        "generated_at": now,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"[local-evidence] Wrote {args.out}")


if __name__ == "__main__":
    main()
