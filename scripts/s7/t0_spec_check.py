"""Strict Gate T0 validation for Sprint 7."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Iterable

EXPECTED_COUNT = 4
DEFAULT_MANIFEST = (
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_filemap_v_7.json"
)
DEFAULT_OUTPUT = "out/obs_gatecheck/T0_discovery.json"
TARGET_PATHS: tuple[str, ...] = (
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_1_spec_v_7.md",
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_2_gates_orr_scorecards_v_1.md",
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_3_filemap_100_v_1.md",
    "docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_capitulo_4_codex_harness_guardrails_v_1.md",
)


class ManifestError(RuntimeError):
    """Raised when the manifest cannot be read."""


def load_lines(manifest_path: Path) -> Iterable[str]:
    with manifest_path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            yield line


def parse_line(line: str) -> dict[str, object]:
    try:
        record = json.loads(line)
    except json.JSONDecodeError as exc:
        raise ManifestError(f"linha inválida no manifesto: {exc}") from exc
    if not isinstance(record, dict):
        raise ManifestError("entrada do manifesto deve ser objeto JSON")
    for key in ("path", "bytes", "sha1"):
        if key not in record:
            raise ManifestError(f"campo obrigatório ausente: {key}")
    return record


def git_sha1(path: Path) -> str:
    result = subprocess.check_output(["git", "hash-object", "--", str(path)], text=True)
    return result.strip()


def emit_github_annotation(level: str, path: Path, message: str) -> None:
    rel = path.as_posix()
    print(f"::{level} file={rel}::{message}")


def build_payload(status: str, checked: int, missing: list[str], mismatched: list[str]) -> dict[str, object]:
    return {
        "gate": "T0",
        "status": status,
        "checked": checked,
        "missing": missing,
        "sha1_mismatch": mismatched,
    }


def write_payload(payload: dict[str, object], destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True), encoding="utf-8")


def validate_manifest(manifest_path: Path) -> tuple[int, list[str], list[str]]:
    checked = 0
    missing: list[str] = []
    mismatched: list[str] = []
    for line in load_lines(manifest_path):
        record = parse_line(line)
        raw_path = record["path"]
        if not isinstance(raw_path, str):
            raise ManifestError("campo 'path' deve ser string")
        file_path = Path(raw_path)
        checked += 1
        if not file_path.exists():
            missing.append(file_path.as_posix())
            emit_github_annotation("error", file_path, "T0 missing")
            continue
        expected_sha = record.get("sha1")
        if isinstance(expected_sha, str) and expected_sha:
            actual_sha = git_sha1(file_path)
            if actual_sha != expected_sha:
                mismatched.append(file_path.as_posix())
                emit_github_annotation(
                    "warning",
                    file_path,
                    f"sha1 mismatch (calc={actual_sha} expected={expected_sha})",
                )
    return checked, sorted(set(missing)), sorted(set(mismatched))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate Sprint 7 manifest")
    parser.add_argument("--manifest", default=DEFAULT_MANIFEST)
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--expected-count", type=int, default=EXPECTED_COUNT)
    return parser.parse_args()


def main(argv: list[str] | None = None) -> int:
    args = parse_args()
    manifest_path = Path(args.manifest)
    output_path = Path(args.output)
    expected_count: int = args.expected_count

    if not manifest_path.exists():
        missing = [path for path in TARGET_PATHS]
        payload = build_payload("FAIL", 0, missing, [])
        write_payload(payload, output_path)
        print("::error ::manifest ausente para T0")
        return 1

    try:
        checked, missing, mismatched = validate_manifest(manifest_path)
    except ManifestError as exc:
        payload = build_payload("FAIL", 0, [], [])
        write_payload(payload, output_path)
        print(f"::error ::{exc}")
        return 1

    status = "PASS"
    if missing or mismatched or checked != expected_count:
        status = "FAIL"
        if checked != expected_count:
            print(
                f"::error ::manifest entries esperados={expected_count} encontrados={checked}"
            )
    payload = build_payload(status, checked, missing, mismatched)
    write_payload(payload, output_path)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
