#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request
from argparse import ArgumentParser
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List, Sequence

BASE_DIR = Path(__file__).resolve().parents[2]
OUTPUT_ROOT = BASE_DIR / "out" / "q1_boss_final" / "stages"


class StageExecutionError(RuntimeError):
    def __init__(
        self,
        description: str,
        command: Sequence[str] | str,
        returncode: int,
        stdout: str = "",
        stderr: str = "",
    ) -> None:
        command_str = command if isinstance(command, str) else " ".join(map(str, command))
        snippet_source = (stderr or stdout or "").strip()
        snippet_lines = snippet_source.splitlines()
        snippet = " | ".join(line.strip() for line in snippet_lines[-5:]) if snippet_lines else "no output captured"
        message = f"{description} failed (exit {returncode}) — {command_str}. {snippet}"
        super().__init__(message)
        self.notes = message


@dataclass(frozen=True)
class StageOutcome:
    status: str
    notes: str
    details: Dict[str, object]


def run_command(
    command: Sequence[str], *, description: str, env: Dict[str, str] | None = None
) -> subprocess.CompletedProcess:
    print(f"[sprint-guard] $ {' '.join(map(str, command))}")
    environment = os.environ.copy()
    if env:
        environment.update(env)
    result = subprocess.run(
        list(map(str, command)),
        cwd=str(BASE_DIR),
        text=True,
        capture_output=True,
        check=False,
        env=environment,
    )
    if result.stdout:
        print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, file=sys.stderr, end="")
    if result.returncode != 0:
        raise StageExecutionError(description, command, result.returncode, result.stdout, result.stderr)
    return result


def run_sut_healthcheck() -> None:
    server_script = BASE_DIR / "scripts" / "sut-server.js"
    if not server_script.exists():
        raise StageExecutionError(
            "SUT healthcheck",
            ["node", str(server_script)],
            1,
            stderr="sut-server.js ausente",
        )

    process = subprocess.Popen(
        ["node", str(server_script)],
        cwd=str(BASE_DIR),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = "http://127.0.0.1:8080/health"
    try:
        deadline = time.time() + 10.0
        while time.time() < deadline:
            try:
                with urllib.request.urlopen(url, timeout=1.0) as response:
                    if response.status != 200:
                        raise StageExecutionError(
                            "SUT healthcheck",
                            ["curl", url],
                            response.status,
                            stderr=f"HTTP {response.status}",
                        )
                    payload = json.loads(response.read().decode("utf-8"))
            except urllib.error.URLError:
                time.sleep(0.2)
                continue
            else:
                if payload.get("status") != "ok":
                    raise StageExecutionError(
                        "SUT healthcheck",
                        ["curl", url],
                        1,
                        stderr=f"payload={payload}",
                    )
                return
        raise StageExecutionError(
            "SUT healthcheck",
            ["node", str(server_script)],
            124,
            stderr="timeout aguardando resposta",
        )
    finally:
        process.terminate()
        try:
            process.wait(timeout=3.0)
        except subprocess.TimeoutExpired:
            process.kill()


def stage_s1() -> StageOutcome:
    checks: List[str] = []
    run_command(["ruff", "check", "."], description="Ruff lint")
    checks.append("ruff check .")
    run_command(["ruff", "format", "--check", "."], description="Ruff format check")
    checks.append("ruff format --check .")
    run_command(
        ["pytest", "-q"],
        description="pytest core suite",
        env={"PYTHONPATH": str(BASE_DIR / "src")},
    )
    checks.append("pytest -q")
    run_sut_healthcheck()
    checks.append("node scripts/sut-server.js healthcheck")
    notes = "Lint, format, pytest, and offline SUT healthcheck succeeded."
    return StageOutcome(status="PASS", notes=notes, details={"checks": checks})


def stage_s2() -> StageOutcome:
    checks: List[str] = []
    run_command(["cargo", "build", "--locked", "--release"], description="cargo build --release")
    checks.append("cargo build --locked --release")
    run_command(["cargo", "test", "--locked", "--lib", "--tests"], description="cargo test lib/tests")
    checks.append("cargo test --locked --lib --tests")
    run_command(["bash", str(BASE_DIR / "scripts" / "microbench_dec.sh")], description="microbench determinístico")
    checks.append("bash scripts/microbench_dec.sh")
    notes = "Cargo build/test and microbench thresholds respected."
    return StageOutcome(status="PASS", notes=notes, details={"checks": checks})


def stage_s3() -> StageOutcome:
    checks: List[str] = []
    run_command(["python", "scripts/prom_label_lint.py"], description="Prometheus label lint")
    checks.append("python scripts/prom_label_lint.py")
    run_command(["python", "scripts/obs_trace_log_smoke.py"], description="Trace/log smoke test")
    checks.append("python scripts/obs_trace_log_smoke.py")
    notes = "Prometheus label lint and trace/log smoke validations passed."
    return StageOutcome(status="PASS", notes=notes, details={"checks": checks})


def stage_s4() -> StageOutcome:
    checks: List[str] = []
    run_command(["bash", str(BASE_DIR / "scripts" / "orr_env_probe.sh")], description="ORR env probe")
    checks.append("bash scripts/orr_env_probe.sh")
    run_command(["python", "scripts/obs_bundle_report.py"], description="ORR bundle validation")
    checks.append("python scripts/obs_bundle_report.py")
    notes = "ORR lite validations completed with bundle structure intact."
    return StageOutcome(status="PASS", notes=notes, details={"checks": checks})


def stage_s5() -> StageOutcome:
    dashboard = BASE_DIR / "dashboards" / "grafana" / "scorecards_quorum_failover_staleness.json"
    expression = (
        "(.panels | length) == 5 and all(.panels[].type; . == \"stat\") and "
        "(.templating.list | length) == 0 and (.time.from == \"now-24h\" and .time.to == \"now\")"
    )
    run_command(
        ["jq", "-e", expression, str(dashboard)],
        description="Grafana dashboard schema validation",
    )
    notes = "Grafana dashboard shape verified via jq guards."
    return StageOutcome(
        status="PASS",
        notes=notes,
        details={"dashboard": str(dashboard.relative_to(BASE_DIR))},
    )


def stage_s6() -> StageOutcome:
    run_command(["python", "scripts/scorecards/s6_scorecards.py"], description="Sprint 6 scorecards")
    report_path = BASE_DIR / "out" / "s6_scorecards" / "report.json"
    if not report_path.exists():
        raise StageExecutionError(
            "Sprint 6 scorecards",
            ["python", "scripts/scorecards/s6_scorecards.py"],
            1,
            stderr="report.json ausente",
        )
    report = json.loads(report_path.read_text(encoding="utf-8"))
    summary = report.get("summary", {})
    total = int(summary.get("total_metrics", 0))
    passing = int(summary.get("passing", 0))
    status = "PASS" if summary.get("status") == "pass" and passing == total else "FAIL"
    notes = f"Scorecards {passing}/{total} metrics within thresholds."
    details = {
        "bundle_sha256": report.get("bundle_sha256"),
        "summary": summary,
    }
    return StageOutcome(status=status, notes=notes, details=details)


STAGE_RUNNERS: Dict[str, Callable[[], StageOutcome]] = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def persist_outcome(stage: str, outcome: StageOutcome) -> None:
    OUTPUT_ROOT.mkdir(parents=True, exist_ok=True)
    stage_dir = OUTPUT_ROOT / stage
    stage_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    payload: Dict[str, object] = {
        "schema_version": 1,
        "stage": stage,
        "status": outcome.status,
        "notes": outcome.notes,
        "timestamp_utc": timestamp,
    }
    if outcome.details:
        payload["details"] = outcome.details
    (stage_dir / "result.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (stage_dir / "guard_status.txt").write_text(outcome.status + "\n", encoding="utf-8")


def main() -> int:
    parser = ArgumentParser(description="Executa guardas de sprint para o Boss Final")
    parser.add_argument("--stage", required=True, help="Identificador do estágio (s1..s6)")
    args = parser.parse_args()
    stage = args.stage.lower().strip()
    if stage not in STAGE_RUNNERS:
        raise SystemExit(f"BOSS-E-UNKNOWN-STAGE:Stage desconhecido: {stage}")

    try:
        outcome = STAGE_RUNNERS[stage]()
    except StageExecutionError as exc:
        outcome = StageOutcome(status="FAIL", notes=exc.notes, details={})
    except Exception as exc:  # pragma: no cover
        outcome = StageOutcome(status="FAIL", notes=f"Unhandled error: {exc}", details={})

    persist_outcome(stage, outcome)
    print(f"{outcome.status} {stage.upper()}: {outcome.notes}")
    return 0 if outcome.status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
