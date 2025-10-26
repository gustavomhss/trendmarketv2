#!/usr/bin/env python3
from __future__ import annotations

import contextlib
import json
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
