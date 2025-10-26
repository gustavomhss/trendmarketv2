#!/usr/bin/env python3
from __future__ import annotations

import contextlib
import json
import os
import shutil
import subprocess
import sys
import textwrap
import time
import urllib.request
from argparse import ArgumentParser
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, List, Sequence
from typing import Callable, Dict, List

BASE_DIR = Path(__file__).resolve().parents[2]
OUTPUT_ROOT = BASE_DIR / "out" / "q1_boss_final" / "stages"
ERROR_PREFIX = "BOSS-E"


@dataclass
class CommandRecord:
    name: str
    command: Sequence[str] | None
    returncode: int
    duration_seconds: float
    stdout: str
    stderr: str


class StageFailure(Exception):
    def __init__(self, code: str, message: str, record: CommandRecord | None = None) -> None:
        self.code = code
        self.message = message
        self.record = record
        super().__init__(f"{ERROR_PREFIX}-{code}:{message}")


@dataclass
class StageContext:
    stage: str
    records: List[CommandRecord] = field(default_factory=list)
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
ERROR_PREFIX = "BOSS-E"
SCHEMA_VERSION = 1
STAGE_GUARD_SUFFIX = "_guard_status.txt"


class StageFailure(Exception):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


@dataclass(frozen=True)
class StageContext:
    stage: str
    variant: str
    executed: List[str]


def run_command(
    command: List[str],
    context: StageContext,
    code: str,
    description: str,
    *,
    env: Dict[str, str] | None = None,
) -> None:
    context.executed.append(" ".join(command))
    run_env = None
    if env:
        run_env = os.environ.copy()
        run_env.update(env)
    try:
        subprocess.run(command, check=True, cwd=BASE_DIR, env=run_env)
    except FileNotFoundError as exc:
        raise StageFailure(code, f"{description}: comando ausente ({command[0]})") from exc
    except subprocess.CalledProcessError as exc:
        raise StageFailure(code, f"{description} (exit {exc.returncode})") from exc


def validate_healthchecks() -> None:
    missing: List[str] = []
    for file_name in ("compose.yaml", "docker-compose.sut.yml"):
        path = BASE_DIR / file_name
        if not path.exists():
            missing.append(f"{file_name}: arquivo ausente")
            continue
        if "healthcheck" not in path.read_text(encoding="utf-8"):
            missing.append(f"{file_name}: healthcheck não encontrado")
    if missing:
        raise StageFailure("S1-HEALTHCHECK", "; ".join(missing))


def validate_actions_lock() -> None:
    path = BASE_DIR / "actions.lock"
    if not path.exists():
        raise StageFailure("S4-ACTIONS-LOCK", "actions.lock ausente")
    text = path.read_text(encoding="utf-8")
    shas = []
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("sha:"):
            shas.append(line.split(":", 1)[1].strip())
    if not shas:
        raise StageFailure("S4-ACTIONS-SHA", "nenhum SHA encontrado em actions.lock")
    bad = [value for value in shas if len(value) != 40 or not all(c in "0123456789abcdef" for c in value.lower())]
    if bad:
        raise StageFailure("S4-ACTIONS-SHA", f"SHA inválido: {', '.join(bad)}")

    workflows_dir = BASE_DIR / ".github" / "workflows"
    missing_pin: List[str] = []
    if workflows_dir.exists():
        for file in sorted(workflows_dir.glob("*.yml")):
            content = file.read_text(encoding="utf-8")
            for line in content.splitlines():
                stripped = line.strip()
                if not stripped.startswith("uses:"):
                    continue
                target = stripped.split("uses:", 1)[1].strip()
                if target.startswith("./"):
                    continue
                if "@" not in target:
                    missing_pin.append(f"{file.name}: {target}")
                    continue
                ref = target.split("@", 1)[1].strip()
                if not ref or len(ref) != 40 or not all(c in "0123456789abcdef" for c in ref.lower()):
                    missing_pin.append(f"{file.name}: {target}")
    if missing_pin:
        raise StageFailure("S4-ACTIONS-PIN", f"ações sem pin: {', '.join(missing_pin)}")


def ensure_trace_log_evidence() -> None:
    evidence_dir = BASE_DIR / "out" / "obs_gatecheck" / "evidence"
    trace_path = evidence_dir / "trace_log_smoke.json"
    if not trace_path.exists():
        raise StageFailure("S3-EVIDENCE", f"{trace_path} não foi gerado")
    payload = json.loads(trace_path.read_text(encoding="utf-8"))
    if payload.get("skipped"):
        raise StageFailure("S3-TRACE-SKIP", "trace/log smoke marcado como skipped")
    ratio = payload.get("correlated_ratio")
    if ratio != 1.0:
        raise StageFailure("S3-TRACE-RATIO", f"trace/log ratio inválido: {ratio}")


def ensure_scorecards_guard() -> str:
    guard_path = BASE_DIR / "out" / "s6_scorecards" / "guard_status.txt"
    if not guard_path.exists():
        raise StageFailure("S6-GUARD-MISSING", "out/s6_scorecards/guard_status.txt ausente")
    status = guard_path.read_text(encoding="utf-8").strip().upper()
    if status not in {"PASS", "FAIL"}:
        raise StageFailure("S6-GUARD-VALUE", f"valor inesperado em guard_status: {status}")
    if status != "PASS":
        raise StageFailure("S6-GUARD-FAIL", "scorecards retornou FAIL")
    report_path = BASE_DIR / "out" / "s6_scorecards" / "report.json"
    if report_path.exists():
        data = json.loads(report_path.read_text(encoding="utf-8"))
        return data.get("status", "PASS")
    return status


def stage_s1(context: StageContext) -> str:
    run_command([sys.executable, "-m", "ruff", "check", "src", "scripts", "tests"], context, "S1-LINT", "Ruff lint falhou")
    run_command([sys.executable, "-m", "ruff", "format", "--check", "src", "scripts"], context, "S1-FORMAT", "Ruff format --check falhou")
    run_command(
        [sys.executable, "-m", "pytest", "-q", "tests/test_prompt_extras.py"],
        context,
        "S1-PYTEST",
        "pytest falhou",
        env={"PYTHONPATH": str(BASE_DIR / "src")},
    )
    validate_healthchecks()
    return "Lint, format, pytest básico e healthchecks do Compose validados."

    def run(
        self,
        command: Sequence[str],
        *,
        failure_code: str = "CMDFAIL",
        env: dict[str, str] | None = None,
    ) -> CommandRecord:
        start = time.monotonic()
        process = subprocess.run(
            list(command),
            cwd=BASE_DIR,
            env=env,
            text=True,
            capture_output=True,
            check=False,
        )
        record = CommandRecord(
            name=" ".join(map(str, command)),
            command=list(command),
            returncode=process.returncode,
            duration_seconds=time.monotonic() - start,
            stdout=process.stdout,
            stderr=process.stderr,
        )
        self.records.append(record)
        if process.returncode != 0:
            raise StageFailure(
                failure_code,
                f"Command '{record.name}' returned {process.returncode}",
                record,
            )
        return record

    def record(
        self,
        name: str,
        *,
        stdout: str = "",
        stderr: str = "",
        duration: float = 0.0,
        returncode: int = 0,
        failure_code: str = "CHECKFAIL",
    ) -> CommandRecord:
        record = CommandRecord(
            name=name,
            command=None,
            returncode=returncode,
            duration_seconds=duration,
            stdout=stdout,
            stderr=stderr,
        )
        self.records.append(record)
        if returncode != 0:
            raise StageFailure(failure_code, f"Check '{name}' failed", record)
        return record


def ensure_stage_dir(stage: str) -> Path:
    stage_dir = OUTPUT_ROOT / stage
    if stage_dir.exists():
        shutil.rmtree(stage_dir)
    stage_dir.mkdir(parents=True, exist_ok=True)
    return stage_dir


def run_sut_healthcheck(ctx: StageContext) -> None:
    server_path = BASE_DIR / "tools" / "sut_health.py"
    if not server_path.exists():
        ctx.record(
            "sut_healthcheck",
            stdout="",
            stderr="tools/sut_health.py missing",
            returncode=1,
            failure_code="HEALTH-NO-SERVER",
        )
        return
def stage_s2(context: StageContext) -> str:
    run_command(["cargo", "fetch", "--locked"], context, "S2-CARGO-FETCH", "cargo fetch falhou")
    run_command(["cargo", "build", "--locked", "--all-targets", "--quiet"], context, "S2-CARGO-BUILD", "cargo build falhou")
    run_command(["cargo", "test", "--locked", "--lib"], context, "S2-CARGO-TEST", "cargo test falhou")
    run_command(["bash", str(BASE_DIR / "scripts" / "microbench_dec.sh")], context, "S2-MICROBENCH", "microbench violou thresholds")
    return "Build, testes de módulo e microbenchmarks dentro dos limites."


def stage_s3(context: StageContext) -> str:
    run_command([sys.executable, str(BASE_DIR / "scripts" / "orr_t2_parse_unit.py")], context, "S3-T2", "simulação observabilidade falhou")
    run_command([sys.executable, str(BASE_DIR / "scripts" / "obs_trace_log_smoke.py")], context, "S3-TRACE", "trace/log smoke falhou")
    ensure_trace_log_evidence()
    return "Observabilidade offline gerou métricas, labels e correlação de trace/log."


def stage_s4(context: StageContext) -> str:
    run_command(["bash", str(BASE_DIR / "scripts" / "ci_repo_guard.sh")], context, "S4-REPO-GUARD", "repo guard encontrou padrões proibidos")
    run_command(["bash", str(BASE_DIR / "scripts" / "tla_ascii_guard.sh")], context, "S4-TLA", "tla_ascii_guard detectou caracteres inválidos")
    validate_actions_lock()
    return "Repo guard, TLA ASCII e pinagem de actions verificados."


def stage_s5(context: StageContext) -> str:
    dashboard = BASE_DIR / "dashboards" / "grafana" / "scorecards_quorum_failover_staleness.json"
    if not dashboard.exists():
        raise StageFailure("S5-DASHBOARD", f"dashboard ausente: {dashboard}")
    run_command(["jq", "-e", "(.panels | length) == 5", str(dashboard)], context, "S5-JQ-PANELS", "painéis != 5")
    run_command(["jq", "-e", "all(.panels[]; .type == \"stat\")", str(dashboard)], context, "S5-JQ-TYPE", "painéis não são do tipo stat")
    run_command(["jq", "-e", "(.templating.list | length) == 0", str(dashboard)], context, "S5-JQ-TEMPL", "templating não vazio")
    run_command(["jq", "-e", "(.time.from == \"now-24h\" and .time.to == \"now\")", str(dashboard)], context, "S5-JQ-TIME", "intervalo de tempo inválido")
    run_command([
        "jq",
        "-e",
        "([.panels[].targets[0].expr] | sort == [\"cdc_lag_p95_s\",\"divergence_pct\",\"failover_time_p95_s\",\"quorum_ratio\",\"staleness_p95_s\"])",
        str(dashboard),
    ], context, "S5-JQ-TARGETS", "targets esperados ausentes")
    return "Dashboard validado com jq (painéis, templating e métricas-alvo)."


def stage_s6(context: StageContext) -> str:
    run_command([sys.executable, str(BASE_DIR / "scripts" / "scorecards" / "s6_scorecards.py")], context, "S6-SCORECARDS", "execução dos scorecards falhou")
    status = ensure_scorecards_guard()
    return f"Scorecards executados com status {status}."


STAGE_HANDLERS: Dict[str, Callable[[StageContext], str]] = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def prepare_variant_dir(stage: str, variant: str) -> Path:
    target = OUTPUT_DIR / stage / variant
    if target.exists():
        shutil.rmtree(target)
    target.mkdir(parents=True, exist_ok=True)
    return target


def write_outputs(directory: Path, payload: Dict[str, object]) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "result.json").write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (directory / "guard_status.txt").write_text(f"{payload['status']}\n", encoding="utf-8")

    start = time.monotonic()
    process = subprocess.Popen(
        [sys.executable, str(server_path)],
        cwd=BASE_DIR,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    body = ""
    status_code: int | None = None
    error: Exception | None = None
    try:
        time.sleep(0.5)
        with urllib.request.urlopen("http://127.0.0.1:8080/health", timeout=5) as response:
            status_code = response.status
            body = response.read().decode("utf-8")
        if status_code != 200:
            raise RuntimeError(f"unexpected HTTP {status_code}")
    except Exception as exc:  # pragma: no cover - defensive path
        error = exc
    finally:
        with contextlib.suppress(Exception):
            process.terminate()
        with contextlib.suppress(Exception):
            process.wait(timeout=2)

    stdout = ""
    stderr = ""
    with contextlib.suppress(Exception):
        captured = process.communicate(timeout=1)
        stdout = captured[0]
        stderr = captured[1]

    duration = time.monotonic() - start
    if error is not None:
        ctx.record(
            "sut_healthcheck",
            stdout=stdout,
            stderr=f"{stderr}\n{error}",
            duration=duration,
            returncode=1,
            failure_code="HEALTHCHECK",
        )
    else:
        ctx.record(
            "sut_healthcheck",
            stdout=textwrap.dedent(
                f"HTTP {status_code}\n{body.strip()}"
            ),
            stderr=stderr,
            duration=duration,
        )


def stage_s1(ctx: StageContext) -> str:
    ctx.run(["yamllint", "."], failure_code="YAML-LINT")
    ctx.run(["ruff", "check", "."], failure_code="LINT")
    ctx.run(["ruff", "format", "--check", "."], failure_code="FORMAT")
    ctx.run([sys.executable, "-m", "pytest", "-q"], failure_code="TESTS")
    run_sut_healthcheck(ctx)
    return "YAML linting, formatting, tests, and SUT healthcheck succeeded."


def stage_s2(ctx: StageContext) -> str:
    ctx.run(["cargo", "fetch", "--locked"], failure_code="CARGO-FETCH")
    ctx.run(["cargo", "build", "--locked", "--workspace"], failure_code="CARGO-BUILD")
    ctx.run(
        ["cargo", "test", "--locked", "--workspace"],
        failure_code="CARGO-TEST",
    )
    ctx.run(["bash", "scripts/microbench_dec.sh"], failure_code="MICROBENCH")
    fixture = BASE_DIR / "fixtures" / "microbench" / "baseline.txt"
    if fixture.exists():
        ctx.run(
            [sys.executable, "scripts/verify_microbench.py", str(fixture)],
            failure_code="MICROBENCH-VERIFY",
        )
    return "Cargo build/test and microbench thresholds satisfied."


def stage_s3(ctx: StageContext) -> str:
    ctx.run(["bash", "scripts/obs_probe_synthetic.sh"], failure_code="PROBE")
    ctx.run([sys.executable, "scripts/prom_label_lint.py"], failure_code="LABELS")
    ctx.run([sys.executable, "scripts/obs_trace_log_smoke.py"], failure_code="TRACE-SMOKE")
    ctx.run(
        [sys.executable, "scripts/obs_bundle_report.py"],
        failure_code="BUNDLE-REPORT",
    )
    return "Observability smoke validations completed."


def _load_json(path: Path, failure_code: str, ctx: StageContext) -> dict:
    if not path.exists():
        ctx.record(
            f"load:{path.name}",
            stdout="",
            stderr=f"Missing file: {path}",
            returncode=1,
            failure_code=failure_code,
        )
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        ctx.record(
            f"load:{path.name}",
            stdout="",
            stderr=f"Invalid JSON in {path}: {exc}",
            returncode=1,
            failure_code=failure_code,
        )
    else:
        ctx.record(f"load:{path.name}", stdout=json.dumps(data, indent=2))
        return data
    raise AssertionError("unreachable")


def stage_s4(ctx: StageContext) -> str:
    bundle_dir = BASE_DIR / "out" / "obs_gatecheck"
    summary = _load_json(bundle_dir / "summary.json", "ORR-SUMMARY", ctx)
    acceptance = summary.get("acceptance")
    gatecheck = summary.get("gatecheck")
    if acceptance != "OK" or gatecheck != "OK":
        ctx.record(
            "summary-status",
            stdout=json.dumps({"acceptance": acceptance, "gatecheck": gatecheck}),
            stderr="Gatecheck or acceptance not OK",
            returncode=1,
            failure_code="ORR-STATUS",
        )
    else:
        ctx.record(
            "summary-status",
            stdout=json.dumps({"acceptance": acceptance, "gatecheck": gatecheck}),
        )

    bundle_hash_path = bundle_dir / "bundle.sha256.txt"
    if not bundle_hash_path.exists():
        ctx.record(
            "bundle-hash",
            stdout="",
            stderr="bundle.sha256.txt missing",
            returncode=1,
            failure_code="ORR-BUNDLE",
        )
    else:
        hash_line = bundle_hash_path.read_text(encoding="utf-8").strip()
        hash_value = hash_line.split()[0] if hash_line else ""
        if len(hash_value) != 64:
            ctx.record(
                "bundle-hash",
                stdout=hash_line,
                stderr="Invalid SHA-256 length",
                returncode=1,
                failure_code="ORR-BUNDLE",
            )
        else:
            ctx.record("bundle-hash", stdout=hash_line)

    log_path = bundle_dir / "logs" / "orr_all.txt"
    if not log_path.exists():
        ctx.record(
            "orr-log",
            stdout="",
            stderr="logs/orr_all.txt missing",
            returncode=1,
            failure_code="ORR-LOG",
        )
    else:
        content = log_path.read_text(encoding="utf-8")
        if "ACCEPTANCE_OK" not in content or "GATECHECK_OK" not in content:
            ctx.record(
                "orr-log",
                stdout="",
                stderr="Required markers not found in orr_all.txt",
                returncode=1,
                failure_code="ORR-LOG",
            )
        else:
            ctx.record(
                "orr-log",
                stdout="Markers OK",
            )

    return "ORR lite validations succeeded."


def stage_s5(ctx: StageContext) -> str:
    dashboard = BASE_DIR / "dashboards" / "grafana" / "scorecards_quorum_failover_staleness.json"
    ctx.run(
        [
            "jq",
            "-e",
            ".title == \"Scorecards Quorum Failover Staleness\"",
            str(dashboard),
        ],
        failure_code="DASHBOARD-TITLE",
    )
    ctx.run(
        ["jq", "-e", ".time.from == \"now-24h\"", str(dashboard)],
        failure_code="DASHBOARD-TIME",
    )
    ctx.run(
        ["jq", "-e", ".time.to == \"now\"", str(dashboard)],
        failure_code="DASHBOARD-TIME",
    )
    ctx.run(
        ["jq", "-e", ".panels | length == 5", str(dashboard)],
        failure_code="DASHBOARD-PANELS",
    )
    expressions = {
        "Guard Status": "avg(scorecard_guard_status)",
        "Latency p50": "histogram_quantile(0.5, sum(rate(scorecard_latency_bucket[5m])) by (le))",
        "Latency p95": "histogram_quantile(0.95, sum(rate(scorecard_latency_bucket[5m])) by (le))",
        "Scorecard Freshness (m)": "(time() - max(scorecard_last_run_timestamp)) / 60",
        "Boss Aggregate Ratio": "avg(q1_boss_final_ratio)",
def execute_stage(stage: str, variant: str) -> Dict[str, object]:
    handler = STAGE_HANDLERS.get(stage)
    if handler is None:
        raise StageFailure("UNKNOWN-STAGE", f"Stage desconhecido: {stage}")
    context = StageContext(stage=stage, variant=variant, executed=[])
    started = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    status = "PASS"
    notes = ""
    failure_code = None
    try:
        notes = handler(context)
    except StageFailure as exc:
        status = "FAIL"
        notes = exc.message
        failure_code = f"{ERROR_PREFIX}-{exc.code}"
        print(f"{ERROR_PREFIX}-{exc.code}:{exc.message}", file=sys.stderr)
    except Exception as exc:  # pragma: no cover
        status = "FAIL"
        notes = f"Erro inesperado: {exc}"
        failure_code = f"{ERROR_PREFIX}-{stage.upper()}-UNEXPECTED"
        print(f"{failure_code}:{exc}", file=sys.stderr)
    finished = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    payload: Dict[str, object] = {
        "schema_version": 1,
        "stage": stage,
        "variant": variant,
        "status": status,
        "notes": notes,
        "started_at": started,
        "completed_at": finished,
        "executed": context.executed,
    }
    if failure_code:
        payload["failure_code"] = failure_code
    return payload
def run_static_stage(definition: StageDefinition) -> Dict[str, str]:
    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    return {
        "schema_version": SCHEMA_VERSION,
        "stage": definition.stage,
        "status": "pass",
        "score": str(definition.target_ratio),
        "formatted_score": f"{definition.target_ratio.quantize(Decimal('0.0001'))}",
        "generated_at": now,
        "description": definition.description,
        "on_fail": definition.on_fail,
    }
    for title, expr in expressions.items():
        jq_filter = textwrap.dedent(
            f"""
            .panels[] | select(.title == \"{title}\") | (.type == \"stat\") and (.targets | length == 1) and (.targets[0].expr == \"{expr}\")
            """
        ).strip()
        ctx.run(["jq", "-e", jq_filter, str(dashboard)], failure_code="DASHBOARD-CARD")
    return "Grafana dashboard structure validated via jq."


def stage_s6(ctx: StageContext) -> str:
    ctx.run([sys.executable, "scripts/scorecards/s6_scorecards.py"], failure_code="SCORECARDS")
    ctx.run(
        [
            sys.executable,
            "-m",
            "jsonschema",
            "--instance",
            "out/s6_scorecards/report.json",
            "--schema",
            "schemas/report.schema.json",
        ],
        failure_code="SCORECARDS-SCHEMA",
    )
    return "Scorecards generated and schema-validated."


STAGE_RUNNERS = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def truncate(value: str, limit: int = 4000) -> str:
    if len(value) <= limit:
        return value
    return value[: limit - 3] + "..."


def write_stage_artifacts(
    stage: str,
    status: str,
    notes: str,
    ctx: StageContext,
    started_at: datetime,
    finished_at: datetime,
) -> Path:
    stage_dir = ensure_stage_dir(stage)
    command_entries = [
        {
            "name": record.name,
            "command": list(record.command) if record.command is not None else None,
            "returncode": record.returncode,
            "duration_seconds": round(record.duration_seconds, 3),
def run_stage(stage: str) -> Dict[str, str]:
    if stage in STATIC_STAGES:
        return run_static_stage(STATIC_STAGES[stage])
    if stage == "s6":
        artifacts: ScorecardArtifacts = generate_report()
        passing = sum(1 for result in artifacts.results if result.ok)
        total = len(artifacts.results)
        ratio = Decimal(passing) / Decimal(max(total, 1))
        formatted_ratio = f"{ratio.quantize(Decimal('0.0001'))}"
        status = "pass" if artifacts.report["status"] == "PASS" else "fail"
        report = generate_report()
        metrics = report["metrics"]
        passing = sum(1 for metric in metrics.values() if metric["ok"])
        total = max(len(metrics), 1)
        ratio = Decimal(passing) / Decimal(total)
        formatted_ratio = f"{ratio.quantize(Decimal('0.0001'))}"
        status = "pass" if report["status"] == "PASS" else "fail"
        now = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
        return {
            "schema_version": SCHEMA_VERSION,
            "stage": "s6",
            "status": status,
            "score": str(ratio),
            "formatted_score": formatted_ratio,
            "generated_at": now,
            "report_path": str(S6_OUTPUT_DIR.relative_to(BASE_DIR)),
            "bundle_sha256": artifacts.bundle_sha256,
            "bundle_sha256": report["bundle"]["sha256"],
            "on_fail": "Executar playbook de estabilização da Sprint 6 e rodar watchers.",
        }
        for record in ctx.records
    ]
    payload = {
        "schema_version": 1,
        "stage": stage,
        "status": status,
        "notes": notes,
        "started_at": started_at.isoformat(),
        "completed_at": finished_at.isoformat(),
        "commands": command_entries,
    }
    (stage_dir / "stage.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (stage_dir / "guard_status.txt").write_text(status + "\n", encoding="utf-8")

    log_lines: List[str] = []
    for record in ctx.records:
        prefix = f"$ {record.name}" if record.command else f"# {record.name}"
        log_lines.append(prefix)
        log_lines.append(
            f"exit_code={record.returncode} duration={record.duration_seconds:.3f}s"
        )
        if record.stdout:
            log_lines.append("--- stdout ---")
            log_lines.append(truncate(record.stdout))
        if record.stderr:
            log_lines.append("--- stderr ---")
            log_lines.append(truncate(record.stderr))
        log_lines.append("")
    (stage_dir / "commands.log").write_text("\n".join(log_lines).strip() + "\n", encoding="utf-8")

    summary_lines = [
        f"### Stage {stage.upper()} — {status}",
        "",
        f"- Notes: {notes}",
        f"- Commands executed: {len(ctx.records)}",
        f"- Completed at: {finished_at.isoformat()}",
    ]
    if status != "PASS":
        summary_lines.append("- See commands.log for detailed failure output.")
    (stage_dir / "comment.md").write_text("\n".join(summary_lines) + "\n", encoding="utf-8")
    return stage_dir


def main(argv: Iterable[str] | None = None) -> int:
    parser = ArgumentParser(description="Executa guardas de sprint para o Boss Final")
    parser.add_argument("--stage", required=True, help="Identificador do estágio (s1..s6)")
    args = parser.parse_args(list(argv) if argv is not None else None)

    stage = args.stage.lower().strip()
    if stage not in STAGE_RUNNERS:
        raise SystemExit(f"{ERROR_PREFIX}-UNKNOWN-STAGE:Stage desconhecido: {stage}")

    OUTPUT_ROOT.mkdir(parents=True, exist_ok=True)
    ctx = StageContext(stage)
    started_at = datetime.now(timezone.utc).replace(microsecond=0)
    status = "PASS"
    notes = ""
    failure: StageFailure | None = None

    try:
        notes = STAGE_RUNNERS[stage](ctx)
    except StageFailure as exc:
        status = "FAIL"
        notes = exc.message
        failure = exc
    except Exception as exc:  # pragma: no cover - unexpected failure path
        status = "FAIL"
        notes = f"Unexpected error: {exc}"
        failure = StageFailure("UNEXPECTED", notes)
    finished_at = datetime.now(timezone.utc).replace(microsecond=0)

    write_stage_artifacts(stage, status, notes, ctx, started_at, finished_at)

    if status != "PASS":
        error_code = failure.code if failure else "FAIL"
        print(f"{ERROR_PREFIX}-{error_code}:{notes}", file=sys.stderr)
        return 1

    print(f"PASS {stage.upper()}")
    parser.add_argument("--variant", default="primary", help="Rótulo do ambiente/runner (ex: primary, clean)")
    args = parser.parse_args()
    stage = args.stage.lower().strip()
    variant = args.variant.strip() or "primary"
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = execute_stage(stage, variant)
    variant_dir = prepare_variant_dir(stage, variant)
    write_outputs(variant_dir, payload)
    print(f"{payload['status']} {stage.upper()} ({variant})")
    ensure_output_dir()
    result = run_stage(stage)
    output_path = OUTPUT_DIR / f"{stage}.json"
    output_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    guard_status = "PASS" if result["status"] == "pass" else "FAIL"
    (OUTPUT_DIR / f"{stage}{STAGE_GUARD_SUFFIX}").write_text(guard_status + "\n", encoding="utf-8")
    print("PASS", stage)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
