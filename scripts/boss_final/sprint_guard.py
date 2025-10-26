#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import textwrap
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Mapping, Sequence
from urllib import error as urllib_error
from urllib import request as urllib_request

BASE_DIR = Path(__file__).resolve().parents[2]
STAGES_ROOT = BASE_DIR / "out" / "q1_boss_final" / "stages"
SCHEMA_VERSION = 1
ERROR_PREFIX = "BOSS-E"
RESULT_FILENAME = "result.json"
GUARD_FILENAME = "guard_status.txt"

PYTHON = sys.executable


@dataclass(frozen=True)
class CommandOutcome:
    name: str
    command: List[str]
    status: str
    returncode: int
    detail: str
    stdout: str
    stderr: str


@dataclass
class StageBundle:
    stage: str
    checks: List[CommandOutcome]
    metadata: Dict[str, object] = field(default_factory=dict)

    @property
    def status(self) -> str:
        return "PASS" if all(outcome.status == "PASS" for outcome in self.checks) else "FAIL"

    @property
    def notes(self) -> str:
        if not self.checks:
            return "No checks executed."
        parts: List[str] = []
        for outcome in self.checks:
            if outcome.status == "PASS":
                parts.append(f"{outcome.name} OK")
            else:
                parts.append(outcome.detail)
        return " | ".join(parts)


class StageExecutionError(RuntimeError):
    """Raised when the guard cannot enforce its contract."""


def fail(code: str, message: str) -> None:
    raise SystemExit(f"{ERROR_PREFIX}-{code}:{message}")


def trim_output(value: str | None, limit: int = 4000) -> str:
    if not value:
        return ""
    if len(value) <= limit:
        return value
    trimmed = value[:limit]
    suffix = f"\n...[truncated {len(value) - limit} chars]"
    return trimmed + suffix


def execute_command(name: str, command: Sequence[object], stage_code: str) -> CommandOutcome:
    argv = [str(part) for part in command]
    try:
        completed = subprocess.run(
            argv,
            cwd=BASE_DIR,
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError as exc:
        detail = f"{ERROR_PREFIX}-{stage_code}-MISSING: {name} ({exc})"
        return CommandOutcome(
            name=name,
            command=argv,
            status="FAIL",
            returncode=127,
            detail=detail,
            stdout="",
            stderr=str(exc),
        )
    except Exception as exc:  # pragma: no cover - defensive
        detail = f"{ERROR_PREFIX}-{stage_code}-UNEXPECTED: {name} ({exc})"
        return CommandOutcome(
            name=name,
            command=argv,
            status="FAIL",
            returncode=1,
            detail=detail,
            stdout="",
            stderr=str(exc),
        )

    status = "PASS" if completed.returncode == 0 else "FAIL"
    if status == "PASS":
        detail = f"{name} succeeded."
    else:
        detail = f"{ERROR_PREFIX}-{stage_code}-CMD: {name} exited {completed.returncode}."
    return CommandOutcome(
        name=name,
        command=argv,
        status=status,
        returncode=completed.returncode,
        detail=detail,
        stdout=trim_output(completed.stdout),
        stderr=trim_output(completed.stderr),
    )


def run_healthcheck(stage_code: str = "S1") -> CommandOutcome:
    name = "SUT healthcheck"
    command = ["node", str(BASE_DIR / "scripts" / "sut-server.js")]
    try:
        proc = subprocess.Popen(
            command,
            cwd=BASE_DIR,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except FileNotFoundError as exc:
        detail = f"{ERROR_PREFIX}-{stage_code}-HEALTH-MISSING: node not found ({exc})"
        return CommandOutcome(
            name=name,
            command=[str(part) for part in command],
            status="FAIL",
            returncode=127,
            detail=detail,
            stdout="",
            stderr=str(exc),
        )

    stdout = ""
    stderr = ""
    status = "FAIL"
    detail = f"{ERROR_PREFIX}-{stage_code}-HEALTH: health endpoint unavailable"
    try:
        url = "http://127.0.0.1:8080/health"
        deadline = time.time() + 5.0
        while time.time() < deadline:
            if proc.poll() is not None:
                raise StageExecutionError("sut-server exited before responding")
            try:
                with urllib_request.urlopen(url, timeout=1) as response:
                    payload = response.read().decode("utf-8")
                data = json.loads(payload)
            except (urllib_error.URLError, TimeoutError, json.JSONDecodeError):
                time.sleep(0.2)
                continue
            status_value = str(data.get("status", "")).lower()
            if status_value == "ok":
                status = "PASS"
                detail = "SUT health endpoint responded with status=ok."
            else:
                detail = f"{ERROR_PREFIX}-{stage_code}-HEALTH: unexpected payload {data!r}"
            break
        else:
            detail = f"{ERROR_PREFIX}-{stage_code}-HEALTH: timeout waiting for health response"
    except StageExecutionError as exc:
        detail = f"{ERROR_PREFIX}-{stage_code}-HEALTH: {exc}"
    except Exception as exc:  # pragma: no cover - defensive
        detail = f"{ERROR_PREFIX}-{stage_code}-HEALTH: {exc}"
    finally:
        try:
            proc.terminate()
            stdout, stderr = proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            stdout, stderr = proc.communicate()
        stdout = trim_output(stdout)
        stderr = trim_output(stderr)

    return CommandOutcome(
        name=name,
        command=[str(part) for part in command],
        status=status,
        returncode=0 if status == "PASS" else 1,
        detail=detail,
        stdout=stdout,
        stderr=stderr,
    )


def stage_s1(_: Path) -> StageBundle:
    checks = [
        execute_command("Ruff lint", [PYTHON, "-m", "ruff", "check", "."], "S1"),
        execute_command("Ruff format", [PYTHON, "-m", "ruff", "format", "--check", "."], "S1"),
        execute_command("Pytest", [PYTHON, "-m", "pytest", "-q"], "S1"),
        run_healthcheck(),
    ]
    return StageBundle(stage="s1", checks=checks)


def stage_s2(_: Path) -> StageBundle:
    checks = [
        execute_command("Cargo fmt", ["cargo", "fmt", "--all", "--", "--check"], "S2"),
        execute_command(
            "Cargo build",
            ["cargo", "build", "--workspace", "--all-targets", "--locked"],
            "S2",
        ),
        execute_command(
            "Cargo test",
            [
                "cargo",
                "test",
                "--workspace",
                "--lib",
                "--bins",
                "--tests",
            ],
            "S2",
        ),
        execute_command("Microbench DEC", ["bash", "scripts/microbench_dec.sh"], "S2"),
    ]
    return StageBundle(stage="s2", checks=checks)


def stage_s3(_: Path) -> StageBundle:
    checks = [
        execute_command("T2 unit observability", [PYTHON, "scripts/orr_t2_parse_unit.py"], "S3"),
        execute_command("Trace/log smoke", [PYTHON, "scripts/obs_trace_log_smoke.py"], "S3"),
        execute_command("Cardinality costs", [PYTHON, "scripts/obs_cardinality_costs.py"], "S3"),
        execute_command(
            "Bundle report",
            [PYTHON, "scripts/obs_bundle_report.py", "--bundle", "out/obs_gatecheck"],
            "S3",
        ),
    ]
    metadata = {"bundle_dir": str(Path("out/obs_gatecheck"))}
    return StageBundle(stage="s3", checks=checks, metadata=metadata)


def stage_s4(_: Path) -> StageBundle:
    checks = [
        execute_command("Yamllint workflows", ["yamllint", ".github/workflows"], "S4"),
        execute_command("Yamllint ops", ["yamllint", "ops"], "S4"),
        execute_command("Repo denylist", ["bash", "scripts/ci_repo_guard.sh"], "S4"),
        execute_command("TLA ASCII guard", ["bash", "scripts/tla_ascii_guard.sh"], "S4"),
    ]
    return StageBundle(stage="s4", checks=checks)


def stage_s5(stage_dir: Path) -> StageBundle:
    dashboard = BASE_DIR / "dashboards" / "grafana" / "scorecards_quorum_failover_staleness.json"
    jq_script = textwrap.dedent(
        """
        def has_panel(id; title; expr) {
          any(
            .panels[];
            .id == id and
            .title == title and
            .type == "stat" and
            (.targets | length == 1) and
            .targets[0].expr == expr
          )
        };
        .title == "Scorecards Quorum Failover Staleness" and
        .time.from == "now-24h" and
        .time.to == "now" and
        (.templating.list == []) and
        (.schemaVersion >= 38) and
        (.version == 1) and
        (.panels | length == 5) and
        has_panel(1; "Quorum Ratio"; "avg(mbp:oracle:quorum_ratio{env=\\\"prod\\\"})") and
        has_panel(2; "Failover Time p95 (s)"; "avg(mbp:oracle:failover_time_p95_s{env=\\\"prod\\\"})") and
        has_panel(3; "Staleness p95 (s)"; "avg(mbp:oracle:staleness_p95_ms{env=\\\"prod\\\"}) / 1000") and
        has_panel(4; "CDC Lag p95 (s)"; "max(quantile_over_time(0.95, cdc_lag_seconds{env=\\\"prod\\\"}[5m]))") and
        has_panel(5; "Divergence (%)"; "avg(mbp:oracle:divergence_p95{env=\\\"prod\\\"}) * 100")
        """
    ).strip()
    checks = [
        execute_command(
            "Dashboard contract (jq)",
            ["jq", "-e", jq_script, str(dashboard)],
            "S5",
        )
    ]
    metadata = {"dashboard": str(dashboard.relative_to(BASE_DIR))}
    return StageBundle(stage="s5", checks=checks, metadata=metadata)


def stage_s6(_: Path) -> StageBundle:
    scorecards_dir = BASE_DIR / "out" / "s6_scorecards"
    checks = [
        execute_command("Generate scorecards", [PYTHON, "scripts/scorecards/s6_scorecards.py"], "S6"),
        execute_command(
            "Scorecards schema",
            [
                PYTHON,
                "-m",
                "jsonschema",
                "--instance",
                str(scorecards_dir / "report.json"),
                "--schema",
                "schemas/report.schema.json",
            ],
            "S6",
        ),
        execute_command(
            "Scorecards guard",
            ["bash", "scripts/watchers/s6_scorecard_guard.sh"],
            "S6",
        ),
    ]
    metadata: Dict[str, object] = {}
    if scorecards_dir.exists():
        metadata["scorecards_dir"] = str(scorecards_dir.relative_to(BASE_DIR))
        bundle_path = scorecards_dir / "bundle.sha256"
        if bundle_path.exists():
            metadata["scorecards_bundle_sha256"] = bundle_path.read_text(encoding="utf-8").strip()
    return StageBundle(stage="s6", checks=checks, metadata=metadata)


STAGE_HANDLERS: Mapping[str, Callable[[Path], StageBundle]] = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def serialise_outcome(outcome: CommandOutcome) -> Dict[str, object]:
    payload: Dict[str, object] = {
        "name": outcome.name,
        "command": outcome.command,
        "status": outcome.status,
        "returncode": outcome.returncode,
        "detail": outcome.detail,
    }
    if outcome.stdout:
        payload["stdout"] = outcome.stdout
    if outcome.stderr:
        payload["stderr"] = outcome.stderr
    return payload


def ensure_stage_dir(stage: str) -> Path:
    stage_dir = STAGES_ROOT / stage
    if stage_dir.exists():
        shutil.rmtree(stage_dir)
    stage_dir.mkdir(parents=True, exist_ok=True)
    return stage_dir


def write_stage_bundle(stage_dir: Path, bundle: StageBundle) -> None:
    payload: Dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "stage": bundle.stage,
        "status": bundle.status,
        "notes": bundle.notes,
        "checks": [serialise_outcome(outcome) for outcome in bundle.checks],
    }
    if bundle.metadata:
        payload["metadata"] = bundle.metadata
    (stage_dir / RESULT_FILENAME).write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (stage_dir / GUARD_FILENAME).write_text(bundle.status + "\n", encoding="utf-8")


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Executa guardas de sprint para o Boss Final")
    parser.add_argument("--stage", required=True, help="Identificador do estágio (s1..s6)")
    return parser.parse_args(list(argv) if argv is not None else None)


def main(argv: Iterable[str] | None = None) -> int:
    args = parse_args(argv)
    stage = args.stage.lower().strip()
    handler = STAGE_HANDLERS.get(stage)
    if handler is None:
        fail("STAGE-UNKNOWN", f"Stage desconhecido: {stage}")
    STAGES_ROOT.mkdir(parents=True, exist_ok=True)
    stage_dir = ensure_stage_dir(stage)
    bundle = handler(stage_dir)
    if bundle.stage != stage:
        fail("STAGE-MISMATCH", f"Handler retornou estágio {bundle.stage} para {stage}")
    write_stage_bundle(stage_dir, bundle)
    print(f"{bundle.status} {stage.upper()}: {bundle.notes}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
