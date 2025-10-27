#!/usr/bin/env python3
"""Generate local evidence metadata for Boss Final reports."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
from typing import Optional


def _format_lines(
    path: pathlib.Path,
    schema: Optional[str],
    schema_version: Optional[int],
    generated_at: Optional[str],
) -> list[str]:
    return [
        f"report_path: {path.resolve()}",
        f"schema: {schema or '<missing>'}",
        f"schema_version: {schema_version if schema_version is not None else '<missing>'}",
        f"generated_at: {generated_at or '<missing>'}",
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "report_path",
        type=pathlib.Path,
        help="Path to the report JSON file",
    )
    parser.add_argument(
        "--diagnostics-path",
        type=pathlib.Path,
        default=None,
        help="Optional path for the diagnostics output file",
    )
    args = parser.parse_args()

    report_path = args.report_path
    if not report_path.is_file():
        raise SystemExit(f"Report file not found: {report_path}")

    data = json.loads(report_path.read_text(encoding="utf-8"))
    digest = hashlib.sha256(report_path.read_bytes()).hexdigest()

    diagnostics_path = args.diagnostics_path or report_path.parent / "diagnostics.txt"
    schema_version_raw = data.get("schema_version")
    schema_version = None
    if isinstance(schema_version_raw, int):
        schema_version = schema_version_raw
    elif isinstance(schema_version_raw, str) and schema_version_raw.isdigit():
        schema_version = int(schema_version_raw)

    lines = _format_lines(
        report_path,
        schema=data.get("schema"),
        schema_version=schema_version,
        generated_at=data.get("generated_at"),
    )
    diagnostics_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    digest_path = report_path.parent / "report.local.json.sha256.txt"
    digest_path.write_text(digest + "\n", encoding="utf-8")

    print("\n".join(lines))

    github_output = os.environ.get("GITHUB_OUTPUT")
    if github_output:
        with open(github_output, "a", encoding="utf-8") as handle:
            handle.write(f"schema={data.get('schema', '')}\n")
            handle.write(
                f"schema_version={schema_version if schema_version is not None else ''}\n"
            )
            handle.write(f"generated_at={data.get('generated_at', '')}\n")
            handle.write(f"sha256={digest}\n")


if __name__ == "__main__":
    main()
