"""Generate the Sprint 7 NDJSON filemap manifest."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Iterable

DEFAULT_MANIFEST = (
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_filemap_v_7.json"
)

TARGET_PATHS: tuple[str, ...] = (
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_1_spec_v_7.md",
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_2_gates_orr_scorecards_v_1.md",
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_3_filemap_100_v_1.md",
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_4_codex_harness_guardrails_v_1.md",
)


def compute_sha1(path: Path) -> str:
    """Return the Git blob sha1 for *path*."""

    result = subprocess.check_output(
        ["git", "hash-object", "--", str(path)], text=True
    )
    return result.strip()


def build_entries(paths: Iterable[str]) -> list[dict[str, object]]:
    entries: list[dict[str, object]] = []
    for raw in paths:
        file_path = Path(raw)
        stat = file_path.stat()
        sha1 = compute_sha1(file_path)
        entries.append(
            {
                "path": file_path.as_posix(),
                "bytes": stat.st_size,
                "sha1": sha1,
            }
        )
    return entries


def write_manifest(entries: Iterable[dict[str, object]], destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", encoding="utf-8", newline="\n") as handle:
        for entry in entries:
            text = json.dumps(entry, ensure_ascii=False, separators=(", ", ": "))
            handle.write(f"{text}\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Sprint 7 NDJSON manifest")
    parser.add_argument(
        "--manifest",
        default=DEFAULT_MANIFEST,
        help="Path to the NDJSON manifest to write.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    entries = build_entries(TARGET_PATHS)
    write_manifest(entries, Path(args.manifest))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
