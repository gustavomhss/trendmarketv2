#!/usr/bin/env python3
"""Resilient aggregation for Boss Final stage artifacts."""

from __future__ import annotations

import json
import os
import sys
import zipfile
from datetime import datetime, timezone
from io import BytesIO
from pathlib import Path
from typing import Dict, List
from urllib import request
from urllib.error import HTTPError, URLError

from ensure_schema import ensure_schema_metadata

STAGE_COUNT = 6
ARTIFACT_PREFIX = "boss-stage-"


def _require_env(key: str) -> str:
    value = os.environ.get(key)
    if not value:
        raise RuntimeError(f"Missing required environment variable: {key}")
    return value


def _headers(token: str) -> Dict[str, str]:
    return {
        "Authorization": f"Bearer {token}",
        "User-Agent": "trendmarketv2-boss-final-aggregator",
        "Accept": "application/vnd.github+json",
    }


def _http_get_json(url: str, token: str) -> Dict[str, object]:
    req = request.Request(url, headers=_headers(token))
    with request.urlopen(req) as resp:
        return json.load(resp)


def _http_get_bytes(url: str, token: str) -> bytes:
    req = request.Request(url, headers=_headers(token))
    with request.urlopen(req) as resp:
        return resp.read()


def _normalize_status(raw: object, exit_code: int | None = None) -> str:
    if isinstance(raw, str):
        value = raw.strip().lower()
        if value in {"pass", "passed", "success", "ok"}:
            return "passed"
        if value in {"fail", "failed", "failure", "error"}:
            return "failed"
        if value in {"missing", "notfound"}:
            return "missing"
        if value:
            return value
    if exit_code is not None:
        return "passed" if exit_code == 0 else "failed"
    return "unknown"


def _ensure_list(value: object) -> List[Dict[str, object]]:
    if isinstance(value, list):
        return [item for item in value if isinstance(item, dict)]
    if isinstance(value, dict):
        return [value]
    return []


def _normalize_entry(entry: Dict[str, object], stage_name: str) -> Dict[str, object]:
    result: Dict[str, object] = {"name": stage_name}
    exit_code = entry.get("exit_code")
    try:
        exit_code_int = int(exit_code) if exit_code is not None else None
    except (TypeError, ValueError):
        exit_code_int = None
    status = _normalize_status(entry.get("status"), exit_code_int)
    if status == "unknown" and entry.get("errors"):
        status = "error"
    result["status"] = status
    if exit_code_int is not None:
        result["exit_code"] = exit_code_int
    if "clean" in entry:
        result["clean"] = bool(entry["clean"])
    if "variant" in entry:
        result["variant"] = entry["variant"]
    if "errors" in entry:
        errors = entry["errors"]
        if isinstance(errors, list):
            result["errors"] = [str(item) for item in errors]
        else:
            result["errors"] = [str(errors)]
    note = entry.get("notes") or entry.get("message")
    if isinstance(note, str) and note.strip():
        result["notes"] = note.strip()
    return result


def _process_report(payload: Dict[str, object], stage_name: str) -> Dict[str, object]:
    if "stages" in payload:
        candidates = payload["stages"]
    else:
        candidates = payload
    entries = _ensure_list(candidates)
    if not entries:
        return {
            "name": stage_name,
            "status": "missing",
            "errors": ["report.json empty"],
        }
    for entry in entries:
        name = entry.get("name") if isinstance(entry, dict) else None
        if name == stage_name:
            return _normalize_entry(entry, stage_name)
    normalized = _normalize_entry(entries[0], stage_name)
    normalized["name"] = stage_name
    return normalized


def _stage_missing(stage_name: str, error: str) -> Dict[str, object]:
    return {
        "name": stage_name,
        "status": "missing",
        "errors": [error],
    }


def _fetch_stage_entry(
    stage_index: int, artifacts: Dict[str, dict], token: str, repository: str
) -> Dict[str, object]:
    stage_name = f"s{stage_index}"
    prefix = f"{ARTIFACT_PREFIX}{stage_name}"
    matching = [info for name, info in artifacts.items() if name.startswith(prefix)]
    if not matching:
        return _stage_missing(stage_name, "artifact not found")
    chosen = sorted(
        matching,
        key=lambda item: item.get("updated_at") or item.get("created_at") or "",
        reverse=True,
    )[0]
    artifact_id = chosen.get("id")
    if not artifact_id:
        return _stage_missing(stage_name, "artifact id missing")
    try:
        blob = _http_get_bytes(
            f"https://api.github.com/repos/{repository}/actions/artifacts/{artifact_id}/zip",
            token,
        )
    except (HTTPError, URLError) as exc:
        return _stage_missing(stage_name, f"download error: {exc}")
    try:
        archive = zipfile.ZipFile(BytesIO(blob))
    except zipfile.BadZipFile as exc:
        return _stage_missing(stage_name, f"invalid artifact zip: {exc}")
    candidate_name = None
    for member in archive.namelist():
        if member.endswith("report.json"):
            candidate_name = member
            break
    if not candidate_name:
        return _stage_missing(stage_name, "report.json not found in artifact")
    try:
        payload = json.loads(archive.read(candidate_name).decode("utf-8"))
    except Exception as exc:  # noqa: BLE001
        return {
            "name": stage_name,
            "status": "error",
            "errors": [f"report.json parse error: {exc}"],
        }
    if not isinstance(payload, dict):
        return {
            "name": stage_name,
            "status": "error",
            "errors": ["report.json has unexpected format"],
        }
    entry = _process_report(payload, stage_name)
    if entry.get("status") == "missing":
        entry.setdefault("errors", []).append("stage data missing in report.json")
    return entry


def _now_utc() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def main() -> int:
    repository = _require_env("GITHUB_REPOSITORY")
    run_id = _require_env("GITHUB_RUN_ID")
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise RuntimeError("GITHUB_TOKEN (or GH_TOKEN) is required to fetch artifacts")
    artifacts_payload = _http_get_json(
        f"https://api.github.com/repos/{repository}/actions/runs/{run_id}/artifacts",
        token,
    )
    artifacts = {item["name"]: item for item in artifacts_payload.get("artifacts", [])}
    out_dir = os.environ.get("REPORT_DIR", "report")
    os.makedirs(out_dir, exist_ok=True)

    stages: List[Dict[str, object]] = []
    for index in range(1, STAGE_COUNT + 1):
        stages.append(_fetch_stage_entry(index, artifacts, token, repository))

    summary_counts: Dict[str, int] = {}
    for entry in stages:
        status = str(entry.get("status", "unknown"))
        summary_counts[status] = summary_counts.get(status, 0) + 1

    final_status = "PASS" if summary_counts.get("passed", 0) == STAGE_COUNT else "FAIL"
    raw_summary = {"counts": summary_counts}
    generated_at = _now_utc()
    report = {
        "generated_at": generated_at,
        "stages": stages,
        "summary": raw_summary,
        "status": final_status,
    }
    report = ensure_schema_metadata(report)
    summary_for_humans = raw_summary
    generated_at_for_humans = generated_at
    for key in ("summary", "generated_at"):
        report.pop(key, None)
    report_path = os.path.join(out_dir, "report.json")
    with open(report_path, "w", encoding="utf-8") as handle:
        json.dump(report, handle, ensure_ascii=False, indent=2)
        handle.write("\n")
    human: list[str] = []
    if summary_for_humans:
        human.append(
            "# Boss Final\n\n"
            + json.dumps(summary_for_humans, ensure_ascii=False, indent=2)
        )
    if generated_at_for_humans:
        human.append(f"\n\n_Gerado em_: {generated_at_for_humans}")
    if human:
        boss_out = Path("out/boss")
        boss_out.mkdir(parents=True, exist_ok=True)
        (boss_out / "summary.md").write_text("\n".join(human), encoding="utf-8")
    guard_path = os.path.join(out_dir, "guard_status.txt")
    with open(guard_path, "w", encoding="utf-8") as handle:
        handle.write(f"{final_status}\n")
    print(json.dumps({"summary": {"counts": summary_counts}}, ensure_ascii=False))
    return 0


if __name__ == "__main__":  # pragma: no cover
    try:
        raise SystemExit(main())
    except Exception as exc:  # noqa: BLE001
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        raise
