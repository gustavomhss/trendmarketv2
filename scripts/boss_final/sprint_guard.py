#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from argparse import ArgumentParser
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List

BASE_DIR = Path(__file__).resolve().parents[2]
OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
ERROR_PREFIX = "BOSS-E"


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


def main() -> int:
    parser = ArgumentParser(description="Executa guardas de sprint para o Boss Final")
    parser.add_argument("--stage", required=True, help="Identificador do estágio (s1..s6)")
    parser.add_argument("--variant", default="primary", help="Rótulo do ambiente/runner (ex: primary, clean)")
    args = parser.parse_args()
    stage = args.stage.lower().strip()
    variant = args.variant.strip() or "primary"
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = execute_stage(stage, variant)
    variant_dir = prepare_variant_dir(stage, variant)
    write_outputs(variant_dir, payload)
    print(f"{payload['status']} {stage.upper()} ({variant})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
