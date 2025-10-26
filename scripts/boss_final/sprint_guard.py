#!/usr/bin/env python3
"""Boss Final sprint guard executor."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence

BASE_DIR = Path(__file__).resolve().parents[2]
OUTPUT_ROOT = BASE_DIR / "out" / "q1_boss_final" / "stages"
SCORECARD_DIR = BASE_DIR / "out" / "s6_scorecards"
ERROR_PREFIX = "BOSS-E"
STAGES = ("s1", "s2", "s3", "s4", "s5", "s6")


@dataclass
class CommandRecord:
    name: str
    command: Optional[Sequence[str]]
    status: str
    returncode: int
    duration_seconds: float
    stdout: str
    stderr: str

    def to_dict(self) -> Dict[str, object]:
        return {
            "name": self.name,
            "command": " ".join(self.command) if self.command else None,
            "status": self.status,
            "returncode": self.returncode,
            "duration_seconds": round(self.duration_seconds, 6),
            "stdout": self.stdout,
            "stderr": self.stderr,
        }


@dataclass
class StageContext:
    stage: str
    variant: str
    records: List[CommandRecord] = field(default_factory=list)

    def stage_dir(self) -> Path:
        return OUTPUT_ROOT / self.stage / self.variant


class StageFailure(RuntimeError):
    def __init__(
        self, code: str, message: str, record: CommandRecord | None = None
    ) -> None:
        self.code = f"{ERROR_PREFIX}-{code}"
        self.message = message
        self.record = record
        super().__init__(f"{self.code}:{message}")


def isoformat_utc() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def canonical_dumps(payload: Dict[str, object]) -> str:
    return (
        json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
        + "\n"
    )


def stage_summary_dir(stage: str) -> Path:
    return OUTPUT_ROOT / stage


def update_stage_summary(stage: str) -> Dict[str, object]:
    base_dir = stage_summary_dir(stage)
    base_dir.mkdir(parents=True, exist_ok=True)
    variant_summaries: Dict[str, Dict[str, str]] = {}
    notes_parts: List[str] = []
    missing: List[str] = []
    statuses: List[str] = []
    for variant in ("primary", "clean"):
        result_path = OUTPUT_ROOT / stage / variant / "result.json"
        if not result_path.exists():
            variant_summaries[variant] = {
                "status": "MISSING",
                "notes": "result.json ausente",
            }
            missing.append(variant)
            continue
        payload = json.loads(result_path.read_text(encoding="utf-8"))
        status = str(payload.get("status", "FAIL")).upper()
        notes = str(payload.get("notes", "")).strip()
        variant_summaries[variant] = {
            "status": status,
            "notes": notes,
        }
        statuses.append(status)
        detail = f"{variant}:{status}"
        if notes:
            detail += f" {notes}"
        notes_parts.append(detail)
    if missing:
        stage_status = "FAIL"
        notes_parts.append(f"missing:{','.join(sorted(missing))}")
    elif any(status != "PASS" for status in statuses) or len(statuses) != 2:
        stage_status = "FAIL"
    else:
        stage_status = "PASS"
    summary = {
        "stage": stage,
        "status": stage_status,
        "notes": " | ".join(notes_parts),
        "variants": variant_summaries,
        "timestamp_utc": isoformat_utc(),
    }
    summary_path = base_dir / "summary.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    guard_path = base_dir / "guard_status.txt"
    guard_path.write_text(f"{stage_status}\n", encoding="utf-8")
    return summary


def run_command(
    *,
    context: StageContext,
    name: str,
    code: str,
    command: Sequence[str],
    env: Optional[Dict[str, str]] = None,
) -> None:
    start = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            cwd=BASE_DIR,
            capture_output=True,
            text=True,
            env=(os.environ | env) if env else None,
            check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - configuration error
        raise StageFailure(code, f"Comando ausente: {command[0]}") from exc
    duration = time.perf_counter() - start
    status = "PASS" if completed.returncode == 0 else "FAIL"
    record = CommandRecord(
        name=name,
        command=command,
        status=status,
        returncode=completed.returncode,
        duration_seconds=duration,
        stdout=completed.stdout.strip(),
        stderr=completed.stderr.strip(),
    )
    context.records.append(record)
    if status != "PASS":
        raise StageFailure(code, f"{name} (exit {completed.returncode})", record)


def record_check(
    context: StageContext, *, name: str, code: str, passed: bool, detail: str
) -> None:
    status = "PASS" if passed else "FAIL"
    record = CommandRecord(
        name=name,
        command=None,
        status=status,
        returncode=0 if passed else 1,
        duration_seconds=0.0,
        stdout=detail if passed else "",
        stderr="" if passed else detail,
    )
    context.records.append(record)
    if not passed:
        raise StageFailure(code, detail, record)


def ensure_healthchecks(context: StageContext) -> None:
    missing: List[str] = []
    for file_name in ("compose.yaml", "docker-compose.sut.yml"):
        path = BASE_DIR / file_name
        if not path.exists():
            missing.append(f"{file_name}: arquivo ausente")
            continue
        if "healthcheck" not in path.read_text(encoding="utf-8"):
            missing.append(f"{file_name}: healthcheck não encontrado")
    detail = "Healthchecks verificados" if not missing else "; ".join(missing)
    record_check(
        context,
        name="Healthcheck manifests",
        code="S1-HEALTH",
        passed=not missing,
        detail=detail,
    )


def run_microbenchmark(context: StageContext) -> None:
    start = time.perf_counter()
    total = 0
    for value in range(100_000):
        total += value % 7
    duration = time.perf_counter() - start
    detail = f"total={total} tempo={duration:.6f}s"
    passed = duration < 1.0
    record_check(
        context, name="Microbenchmark", code="S2-MICRO", passed=passed, detail=detail
    )


def ensure_observability_catalog(context: StageContext) -> None:
    catalog = BASE_DIR / "observability"
    if not catalog.exists():
        record_check(
            context,
            name="Observability catalog",
            code="S3-CATALOG",
            passed=False,
            detail="observability/ ausente",
        )
        return
    yaml_files = list(catalog.rglob("*.yaml"))
    passed = bool(yaml_files)
    detail = (
        f"{len(yaml_files)} YAML encontrados"
        if passed
        else "Nenhum YAML em observability/"
    )
    record_check(
        context,
        name="Observability catalog",
        code="S3-CATALOG",
        passed=passed,
        detail=detail,
    )


def validate_actions_lock(context: StageContext) -> None:
    path = BASE_DIR / "actions.lock"
    if not path.exists():
        record_check(
            context,
            name="actions.lock",
            code="S4-ACTIONS",
            passed=False,
            detail="actions.lock ausente",
        )
        return
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        record_check(
            context,
            name="actions.lock",
            code="S4-ACTIONS",
            passed=False,
            detail=f"JSON inválido: {exc}",
        )
        return
    if not isinstance(data, dict):
        record_check(
            context,
            name="actions.lock",
            code="S4-ACTIONS",
            passed=False,
            detail="Formato inválido: esperado objeto de ações",
        )
        return
    issues: List[str] = []
    for action, meta in sorted(data.items()):
        if not isinstance(meta, dict):
            issues.append(f"{action}: metadados inválidos")
            continue
        sha = str(meta.get("sha", ""))
        if len(sha) != 40:
            issues.append(f"{action}: SHA inválido")
        for field_name in ("date", "author", "rationale"):
            if field_name not in meta or not str(meta[field_name]).strip():
                issues.append(f"{action}: campo {field_name} ausente")
    record_check(
        context,
        name="actions.lock",
        code="S4-ACTIONS",
        passed=not issues,
        detail="actions.lock validado" if not issues else "; ".join(issues),
    )

    workflows_dir = BASE_DIR / ".github" / "workflows"
    missing: List[str] = []
    for workflow in sorted(workflows_dir.glob("*.yml")):
        for line in workflow.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if not stripped.startswith("uses:"):
                continue
            ref = stripped.split("uses:", 1)[1].strip()
            if ref.startswith("./"):
                continue
            if "@" not in ref:
                missing.append(f"{workflow.name}: {ref}")
                continue
            sha = ref.split("@", 1)[1].strip()
            if len(sha) != 40:
                missing.append(f"{workflow.name}: {ref}")
    record_check(
        context,
        name="Workflow pins",
        code="S4-PINS",
        passed=not missing,
        detail="Workflows pinados" if not missing else "; ".join(missing),
    )


def validate_dashboard_structure(context: StageContext) -> None:
    path = BASE_DIR / "observability" / "grafana" / "dashboards" / "s5_mbp_scale.json"
    if not path.exists():
        record_check(
            context,
            name="Grafana dashboard",
            code="S5-DASH",
            passed=False,
            detail="Dashboard ausente",
        )
        return
    payload = json.loads(path.read_text(encoding="utf-8"))
    issues: List[str] = []
    schema_version = payload.get("schemaVersion")
    if schema_version is None or schema_version < 40:
        issues.append("SchemaVersion inválido")
    panels = payload.get("panels", [])
    quorum_expr = 'avg(mbp:oracle:quorum_ratio{env="prod"})'
    failover_expr = 'avg(mbp:oracle:failover_time_p95_s{env="prod"})'
    quorum_panel = next(
        (
            panel
            for panel in panels
            if panel.get("title", "").lower().startswith("quorum ratio")
        ),
        None,
    )
    failover_panel = next(
        (panel for panel in panels if "failover" in panel.get("title", "").lower()),
        None,
    )
    if not quorum_panel:
        issues.append("Painel de quorum_ratio ausente")
    else:
        targets = quorum_panel.get("targets", [])
        if not any(target.get("expr") == quorum_expr for target in targets):
            issues.append("Consulta de quorum_ratio divergente")
    if not failover_panel:
        issues.append("Painel de failover ausente")
    else:
        targets = failover_panel.get("targets", [])
        if not any(target.get("expr") == failover_expr for target in targets):
            issues.append("Consulta de failover divergente")
    record_check(
        context,
        name="Grafana dashboard",
        code="S5-DASH",
        passed=not issues,
        detail="Dashboard verificado" if not issues else "; ".join(issues),
    )


def run_scorecards(context: StageContext) -> None:
    run_command(
        context=context,
        name="Sprint 6 scorecards",
        code="S6-SCORECARDS",
        command=[sys.executable, "scripts/scorecards/s6_scorecards.py"],
    )
    guard_path = SCORECARD_DIR / "guard_status.txt"
    if not guard_path.exists():
        record_check(
            context,
            name="S6 guard",
            code="S6-GUARD",
            passed=False,
            detail="guard_status.txt não encontrado",
        )
    else:
        status = guard_path.read_text(encoding="utf-8").strip()
        record_check(
            context,
            name="S6 guard",
            code="S6-GUARD",
            passed=status == "PASS",
            detail=f"guard_status={status}",
        )


def stage_s1(context: StageContext) -> None:
    run_command(
        context=context,
        name="Ruff lint",
        code="S1-LINT",
        command=["ruff", "check", "scripts/scorecards", "scripts/boss_final"],
    )
    run_command(
        context=context,
        name="Ruff format",
        code="S1-FORMAT",
        command=[
            "ruff",
            "format",
            "--check",
            "scripts/scorecards",
            "scripts/boss_final",
        ],
    )
    run_command(
        context=context,
        name="Core pytest",
        code="S1-PYTEST",
        command=["pytest", "-q", "tests/scorecards", "tests/boss_final"],
    )
    ensure_healthchecks(context)


def stage_s2(context: StageContext) -> None:
    run_command(
        context=context,
        name="Compile modules",
        code="S2-BUILD",
        command=[sys.executable, "-m", "compileall", "src"],
    )
    run_command(
        context=context,
        name="Module pytest",
        code="S2-PYTEST",
        command=["pytest", "-q", "tests/unit"],
    )
    run_microbenchmark(context)


def stage_s3(context: StageContext) -> None:
    run_command(
        context=context,
        name="Observability smoke",
        code="S3-SMOKE",
        command=["pytest", "-q", "tests/workflows/test_comment_fallback.py"],
    )
    ensure_observability_catalog(context)


def stage_s4(context: StageContext) -> None:
    run_command(
        context=context,
        name="YAML validation",
        code="S4-YAML",
        command=["yamllint", "-s", "configs", "ops"],
    )
    validate_actions_lock(context)


def stage_s5(context: StageContext) -> None:
    validate_dashboard_structure(context)


def stage_s6(context: StageContext) -> None:
    run_scorecards(context)


STAGE_HANDLERS: Dict[str, Callable[[StageContext], None]] = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def write_stage_outputs(
    context: StageContext, status: str, notes: str
) -> Dict[str, object]:
    status = status.upper()
    directory = context.stage_dir()
    directory.mkdir(parents=True, exist_ok=True)
    result = {
        "stage": context.stage,
        "variant": context.variant,
        "status": status,
        "notes": notes.strip(),
        "timestamp_utc": isoformat_utc(),
        "checks": [record.to_dict() for record in context.records],
    }
    result_path = directory / "result.json"
    result_path.write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    guard_path = directory / "guard_status.txt"
    guard_path.write_text(f"{status}\n", encoding="utf-8")
    comment_lines = [
        f"### Stage {context.stage.upper()} ({context.variant})",
        "",
        f"{status}: {notes}",
        "",
    ]
    (directory / "comment.md").write_text("\n".join(comment_lines), encoding="utf-8")
    bundle_sha = hashlib.sha256(canonical_dumps(result).encode("utf-8")).hexdigest()
    (directory / "bundle.sha256").write_text(bundle_sha + "\n", encoding="utf-8")
    update_stage_summary(context.stage)
    return result


def run_stage(stage: str, variant: str) -> Dict[str, object]:
    if stage not in STAGES:
        raise SystemExit(f"Estágio inválido: {stage}")
    if variant not in {"primary", "clean"}:
        raise SystemExit(f"Variant inválido: {variant}")

    context = StageContext(stage=stage, variant=variant)
    handler = STAGE_HANDLERS[stage]
    status = "PASS"
    notes = f"PASS:{stage.upper()} {variant} guard completado"
    try:
        handler(context)
    except StageFailure as exc:
        status = "FAIL"
        notes = f"{exc.code}:{exc.message}"
    result = write_stage_outputs(context, status, notes)
    if status != "PASS":
        raise SystemExit(1)
    return result


def parse_args(argv: List[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Execute Sprint guard stage")
    parser.add_argument("--stage", required=True, choices=STAGES)
    parser.add_argument("--variant", default="primary", choices=["primary", "clean"])
    return parser.parse_args(argv)


def main(argv: List[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    run_stage(stage=args.stage, variant=args.variant)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main(sys.argv[1:]))
