#!/usr/bin/env python3
"""Ensure Boss Final local report includes mandatory schema fields."""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import pathlib
import re
import sys
import zipfile
from functools import lru_cache
from typing import Any, MutableMapping

MANDATORY = ("schema", "schema_version", "timestamp_utc", "status")


_SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
_SCHEMA_CANDIDATES = (
    _REPO_ROOT / "schemas" / "q1_boss_report.schema.json",
    pathlib.Path("schemas/q1_boss_report.schema.json"),
    _REPO_ROOT / "jsonschema" / "boss_final.report.schema.json",
    _REPO_ROOT / "jsonschema" / "schemas" / "boss_final.report.schema.json",
    pathlib.Path("jsonschema/boss_final.report.schema.json"),
    pathlib.Path("jsonschema/schemas/boss_final.report.schema.json"),
)


@lru_cache(maxsize=1)
def _load_schema_definition() -> tuple[dict[str, Any], pathlib.Path]:
    """Locate and load the Boss Final JSON Schema."""

    errors: list[str] = []
    for path in _SCHEMA_CANDIDATES:
        if not path.exists():
            errors.append(f"{path} (missing)")
            continue
        try:
            return json.loads(path.read_text(encoding="utf-8")), path
        except json.JSONDecodeError as exc:
            errors.append(f"{path} (invalid JSON: {exc})")
            continue
    joined = (
        "; ".join(errors) if errors else "no candidates"
    )  # pragma: no cover - defensive
    raise FileNotFoundError("Boss Final schema not found; checked: " + joined)


@lru_cache(maxsize=1)
def expected_schema_id() -> str:
    """Return the canonical schema identifier enforced by the JSON Schema."""

    try:
        data, schema_path = _load_schema_definition()
    except FileNotFoundError:
        return "boss_final.report@v1"

    try:
        const_value = data["properties"]["schema"]["const"]
    except Exception as exc:  # pragma: no cover - defensive
        raise RuntimeError(
            f"Não foi possível determinar 'schema.const' em {schema_path}: {exc}"
        ) from exc

    if not isinstance(const_value, str) or not const_value.strip():
        raise RuntimeError(
            f"Valor inválido para 'schema.const' em {schema_path}: {const_value!r}"
        )
    return const_value.strip()


def _schema_version_default() -> int:
    """Expose the default schema version derived from the schema identifier."""

    raw = os.environ.get("BOSS_SCHEMA_VERSION")
    if raw:
        try:
            return int(raw.strip())
        except (TypeError, ValueError):
            return 1

    match = re.search(r"@v?(\d+)$", expected_schema_id())
    if match:
        try:
            return int(match.group(1))
        except (TypeError, ValueError):  # pragma: no cover - defensive fallback
            return 1
    return 1


def _infer_version(data: MutableMapping[str, Any]) -> int:
    version = None

    schema_value = data.get("schema")
    if isinstance(schema_value, str):
        match = re.search(r"@v?(\d+)$", schema_value)
        if match:
            try:
                version = int(match.group(1))
            except Exception:  # pragma: no cover - defensive
                version = None

    if version is None:
        try:
            version = int(str(data.get("schema_version")))
        except Exception:  # pragma: no cover - defensive
            version = None

    return version or _schema_version_default()


@lru_cache(maxsize=1)
def expected_schema_version() -> int:
    """Return the canonical schema version declared by the JSON Schema."""

    try:
        data, _ = _load_schema_definition()
    except FileNotFoundError:
        return _schema_version_default()

    schema_version_node = data.get("properties", {}).get("schema_version", {})
    const_value = schema_version_node.get("const")
    if isinstance(const_value, int):
        return const_value
    if isinstance(const_value, str):
        try:
            return int(const_value.strip())
        except ValueError:
            pass

    enum_values = schema_version_node.get("enum")
    if isinstance(enum_values, list):
        for item in enum_values:
            if isinstance(item, int):
                return item
            if isinstance(item, str) and item.isdigit():
                return int(item)
            if isinstance(item, str):
                try:
                    return int(item.strip())
                except ValueError:
                    continue

    return _schema_version_default()


def _normalize_stages(raw: Any) -> dict[str, Any]:
    """Coerce arbitrary stage collections into a mapping."""

    if raw is None:
        return {}
    if isinstance(raw, MutableMapping):
        return dict(raw)
    if isinstance(raw, list):
        normalized: dict[str, Any] = {}
        for item in raw:
            if not isinstance(item, MutableMapping):
                continue
            key = None
            for candidate in ("id", "stage", "name"):
                value = item.get(candidate)
                if isinstance(value, str) and value.strip():
                    key = value.strip()
                    break
            if not key:
                key = f"stage_{len(normalized) + 1}"
            normalized[key] = item
        return normalized
    return {}


def _sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _find_stage_zips(
    search_roots: list[pathlib.Path], pattern: str
) -> list[pathlib.Path]:
    found: list[pathlib.Path] = []
    for root in search_roots:
        if not root.exists():
            continue
        found.extend(root.glob(pattern))
        found.extend(root.rglob(pattern))
    unique = sorted({path.resolve() for path in found if path.is_file()})
    return unique


def _find_candidate() -> pathlib.Path:
    candidates = sorted(pathlib.Path("out").rglob("report.local.json"))
    if not candidates:
        raise SystemExit(
            "[ensure-schema] relatório não encontrado: out/boss_final/report.local.json"
        )
    return candidates[0]


def _now_utc_z() -> str:
    return (
        datetime.datetime.now(datetime.timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def ensure_schema_metadata(data: MutableMapping[str, Any]) -> dict[str, Any]:
    """Normalize Boss Final reports enforcing local contracts."""

    normalized: dict[str, Any] = dict(data)

    schema_version = normalized.get("schema_version")
    if not schema_version:
        normalized["schema_version"] = _schema_version_default()

    version = _infer_version(normalized)

    normalized["schema"] = expected_schema_id()

    normalized["schema_version"] = int(version)

    if not normalized.get("timestamp_utc"):
        normalized["timestamp_utc"] = _now_utc_z()

    status = normalized.get("status")
    if isinstance(status, str) and status.strip():
        normalized["status"] = status.strip().upper()
    else:
        default_status = (
            os.environ.get("BOSS_LOCAL_STATUS", "PASS").strip().upper() or "PASS"
        )
        normalized["status"] = default_status

    normalized["stages"] = _normalize_stages(normalized.get("stages"))

    bundle_info = normalized.get("bundle")
    boss_out_dir = pathlib.Path(os.environ.get("BOSS_OUT_DIR", "out/boss"))
    bundle_override = os.environ.get("BOSS_BUNDLE_PATH")
    stage_dir_override = os.environ.get("BOSS_STAGE_DIR")
    stage_glob = os.environ.get("BOSS_STAGE_GLOB", "boss-stage-*.zip")
    bundle_name = os.environ.get("BOSS_BUNDLE_NAME", "boss-final-bundle.zip")
    bundle_path = boss_out_dir / bundle_name

    chosen_bundle: pathlib.Path | None = None

    if bundle_override:
        override_path = pathlib.Path(bundle_override)
        if override_path.exists():
            chosen_bundle = override_path
        else:
            print(
                f"[ensure-schema] BOSS_BUNDLE_PATH aponta para arquivo inexistente: {override_path}"
            )

    if chosen_bundle is None and isinstance(bundle_info, MutableMapping):
        raw_bundle_path = bundle_info.get("path")
        if raw_bundle_path:
            bundle_path_candidate = pathlib.Path(str(raw_bundle_path))
            if bundle_path_candidate.exists():
                chosen_bundle = bundle_path_candidate
            else:
                print(
                    "[ensure-schema] bundle.path informado não existe; tentando gerar novo bundle"
                )

    if chosen_bundle is None:
        search_roots: list[pathlib.Path] = []
        if stage_dir_override:
            search_roots.append(pathlib.Path(stage_dir_override))
        search_roots.append(boss_out_dir)
        search_roots.append(pathlib.Path.cwd())

        stage_zips = _find_stage_zips(search_roots, stage_glob)
        if stage_zips:
            bundle_path.parent.mkdir(parents=True, exist_ok=True)
            print(f"[ensure-schema] Zips de estágio detectados ({len(stage_zips)}):")
            for stage_zip in stage_zips:
                print(f"  - {stage_zip}")
            with zipfile.ZipFile(
                bundle_path, "w", compression=zipfile.ZIP_DEFLATED
            ) as archive:
                for stage_zip in stage_zips:
                    archive.write(stage_zip, arcname=stage_zip.name)
            chosen_bundle = bundle_path
        else:
            print(
                "[ensure-schema] Nenhum boss-stage-*.zip encontrado (roots verificados):"
            )
            for root in search_roots:
                print(f"  - {root}")

    if chosen_bundle is None:
        print("[ensure-schema] bundle ausente e não foi possível inferir")
        sys.exit(1)

    bundle_path = chosen_bundle
    bundle_sha = _sha256(bundle_path)
    normalized["bundle"] = {"sha256": bundle_sha}

    for key in ("summary", "generated_at"):
        normalized.pop(key, None)

    missing = [field for field in MANDATORY if field not in normalized]
    if missing:
        raise SystemExit(
            f"[ensure-schema] campos obrigatórios ausentes após normalização: {', '.join(missing)}"
        )

    return normalized


def _ensure_fields(path: pathlib.Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    normalized = ensure_schema_metadata(data)

    if normalized != data:
        path.write_text(
            json.dumps(normalized, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
    data = normalized

    print(
        f"[ensure-schema] OK: {path} | schema={data['schema']} | v={data['schema_version']} | ts={data['timestamp_utc']} | status={data['status']}"
    )


def main() -> int:
    _ensure_fields(_find_candidate())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
