#!/usr/bin/env python3
from __future__ import annotations

import http.server
import importlib.util
import json
import os
import socketserver
import subprocess
import threading
import time
import urllib.request
from argparse import ArgumentParser
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional

BASE_DIR = Path(__file__).resolve().parents[2]

_S6_MODULE_PATH = BASE_DIR / "scripts" / "scorecards" / "s6_scorecards.py"
_S6_SPEC = importlib.util.spec_from_file_location("s6_scorecards", _S6_MODULE_PATH)
if _S6_SPEC is None or _S6_SPEC.loader is None:  # pragma: no cover - defensive
    raise RuntimeError(
        f"Não foi possível carregar módulo de scorecards em {_S6_MODULE_PATH}"
    )
_S6_MODULE = importlib.util.module_from_spec(_S6_SPEC)
_S6_SPEC.loader.exec_module(_S6_MODULE)
generate_report = _S6_MODULE.generate_report
S6_OUTPUT_DIR = _S6_MODULE.OUTPUT_DIR

OUTPUT_DIR = BASE_DIR / "out" / "q1_boss_final" / "stages"
ERROR_PREFIX = "BOSS-E"
DEFAULT_ENV = dict(os.environ)
DEFAULT_ENV.setdefault("PYTHONPATH", str(BASE_DIR / "src"))


class StageExecutionError(RuntimeError):
    def __init__(
        self, code: str, message: str, *, context: Optional[Dict[str, Any]] = None
    ) -> None:
        super().__init__(message)
        self.code = code
        self.detail = message
        self.context = context or {}


@dataclass(frozen=True)
class StageOutcome:
    notes: str
    details: Optional[Dict[str, Any]] = None


StageHandler = Callable[[], StageOutcome]


def ensure_output_dir() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


COMMAND_LOG: List[Dict[str, Any]] = []


def reset_command_log() -> None:
    COMMAND_LOG.clear()


def get_command_log() -> List[Dict[str, Any]]:
    return [dict(entry) for entry in COMMAND_LOG]


def truncate_output(payload: Optional[str], *, limit: int = 4000) -> str:
    if not payload:
        return ""
    if len(payload) <= limit:
        return payload
    truncated = len(payload) - limit
    return payload[:limit] + f"… <truncated {truncated} characters>"


def run_command(
    command: list[str], *, env: Optional[Dict[str, str]] = None
) -> subprocess.CompletedProcess[str]:
    command_display = " ".join(command)
    print(f"[boss] running: {command_display}")
    started_at = datetime.now(timezone.utc)
    start_perf = time.perf_counter()
    log_entry: Dict[str, Any] = {
        "command": list(command),
        "started_at": started_at.isoformat(),
    }
    try:
        command_env = dict(DEFAULT_ENV)
        if env:
            command_env.update(env)
        result = subprocess.run(
            command,
            check=True,
            env=command_env,
            capture_output=True,
            text=True,
        )
        duration = time.perf_counter() - start_perf
        log_entry.update(
            {
                "status": "PASS",
                "duration_seconds": round(duration, 3),
                "stdout": truncate_output(result.stdout),
                "stderr": truncate_output(result.stderr),
            }
        )
        COMMAND_LOG.append(log_entry)
        if result.stdout:
            print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
        if result.stderr:
            print(result.stderr, end="" if result.stderr.endswith("\n") else "\n")
        return result
    except FileNotFoundError as exc:  # pragma: no cover - defensive
        duration = time.perf_counter() - start_perf
        log_entry.update(
            {
                "status": "FAIL",
                "duration_seconds": round(duration, 3),
                "error": str(exc),
            }
        )
        COMMAND_LOG.append(log_entry)
        raise StageExecutionError(
            "COMMAND-NOT-FOUND",
            f"Comando não encontrado: {command[0]} ({exc})",
            context=log_entry,
        ) from exc
    except subprocess.CalledProcessError as exc:
        duration = time.perf_counter() - start_perf
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if stdout:
            print(stdout, end="" if stdout.endswith("\n") else "\n")
        if stderr:
            print(stderr, end="" if stderr.endswith("\n") else "\n")
        log_entry.update(
            {
                "status": "FAIL",
                "duration_seconds": round(duration, 3),
                "returncode": exc.returncode,
                "stdout": truncate_output(stdout),
                "stderr": truncate_output(stderr),
            }
        )
        COMMAND_LOG.append(log_entry)
        raise StageExecutionError(
            "COMMAND-FAIL",
            f"'{command_display}' retornou código {exc.returncode}",
            context=log_entry,
        ) from exc


def health_probe() -> int:
    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802
            if self.path == "/health":
                payload = json.dumps({"status": "ok"}).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            else:
                self.send_response(404)
                self.end_headers()

        def log_message(self, format: str, *args: Any) -> None:  # noqa: A003 - match BaseHTTPRequestHandler signature
            return

    class Server(socketserver.TCPServer):
        allow_reuse_address = True

    with Server(("127.0.0.1", 0), Handler) as httpd:
        port = httpd.server_address[1]
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        try:
            url = f"http://127.0.0.1:{port}/health"
            deadline = time.time() + 5
            while time.time() < deadline:
                try:
                    with urllib.request.urlopen(url, timeout=1) as response:  # noqa: S310 - controlled local call
                        if response.status != 200:
                            raise StageExecutionError(
                                "HEALTH-STATUS",
                                f"HTTP {response.status} em {url}",
                                context={"url": url, "status": response.status},
                            )
                        payload = json.loads(response.read().decode("utf-8"))
                        if payload.get("status") != "ok":
                            raise StageExecutionError(
                                "HEALTH-PAYLOAD",
                                f"Payload inesperado em {url}: {payload}",
                                context={"url": url, "payload": payload},
                            )
                        return port
                except StageExecutionError:
                    raise
                except Exception:
                    time.sleep(0.1)
            raise StageExecutionError(
                "HEALTH-TIMEOUT",
                f"Timeout ao validar {url}",
                context={"url": url, "timeout_seconds": 5},
            )
        finally:
            httpd.shutdown()
            thread.join()


def stage_s1() -> StageOutcome:
    run_command(["ruff", "check", "scripts/boss_final"])
    run_command(["ruff", "format", "--check", "scripts/boss_final"])
    pytest_targets = [
        "tests/test_prompt_extras.py",
        "tests/test_release_manifest.py::ReleaseManifestTests::test_build_release_metadata_derives_version",
    ]
    run_command(["pytest", "-q", *pytest_targets])
    port = health_probe()
    return StageOutcome(
        notes=(
            "Lint, format, pytest básico (prompt_extras + release_metadata) e health check responderam"
            f" em 127.0.0.1:{port}."
        ),
        details={"health_port": port, "pytest_targets": pytest_targets},
    )


def stage_s2() -> StageOutcome:
    cargo_env = {"CARGO_TERM_COLOR": "always"}
    run_command(["cargo", "fetch"], env=cargo_env)
    run_command(["cargo", "build", "--locked", "--all-targets"], env=cargo_env)
    run_command(["cargo", "test", "--locked", "--all-targets"], env=cargo_env)
    run_command(["bash", "scripts/microbench_dec.sh"], env=cargo_env)
    return StageOutcome(
        notes="Cargo fetch/build/test e microbench determinístico concluídos sem violações.",
    )


def stage_s3() -> StageOutcome:
    run_command(["bash", "scripts/obs_probe_synthetic.sh"])
    evidence_path = (
        BASE_DIR / "out" / "obs_gatecheck" / "evidence" / "synthetic_probe.json"
    )
    if not evidence_path.exists():
        raise StageExecutionError(
            "S3-EVIDENCE",
            f"Arquivo esperado não encontrado: {evidence_path}",
            context={"expected_path": str(evidence_path)},
        )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    ok = int(payload.get("ok", 0))
    total = int(payload.get("total", 0))
    ratio = float(payload.get("ok_ratio", 0.0))
    notes = f"Smoke observability executado ({ok}/{total} requisições OK, razão {ratio:.4f})."
    return StageOutcome(
        notes=notes,
        details={
            "evidence": str(evidence_path.relative_to(BASE_DIR)),
            "ok": ok,
            "total": total,
            "ratio": ratio,
        },
    )


def stage_s4() -> StageOutcome:
    run_command(["bash", "scripts/s4_bundle.sh"])
    bundles = sorted(
        (BASE_DIR / "out").glob("s4_evidence_bundle_*.zip"),
        key=lambda path: path.stat().st_mtime,
    )
    if not bundles:
        raise StageExecutionError(
            "S4-BUNDLE",
            "Nenhum bundle s4_evidence_bundle_*.zip gerado em out/.",
            context={"glob": "out/s4_evidence_bundle_*.zip"},
        )
    bundle = bundles[-1]
    sha_path = Path(f"{bundle}.sha256")
    if not sha_path.exists():
        raise StageExecutionError(
            "S4-SHA",
            f"SHA esperado ausente: {sha_path}",
            context={"sha_path": str(sha_path)},
        )
    notes = f"Bundle ORR lite gerado ({bundle.name}) com SHA registrado."
    return StageOutcome(
        notes=notes,
        details={
            "bundle": str(bundle.relative_to(BASE_DIR)),
            "sha": str(sha_path.relative_to(BASE_DIR)),
        },
    )


def stage_s5() -> StageOutcome:
    dashboard_path = (
        BASE_DIR
        / "dashboards"
        / "grafana"
        / "scorecards_quorum_failover_staleness.json"
    )
    if not dashboard_path.exists():
        raise StageExecutionError(
            "S5-DASHBOARD", f"Dashboard ausente: {dashboard_path}"
        )
    run_command(["jq", "-e", "select(.schemaVersion == 38)", str(dashboard_path)])
    run_command(["jq", "-e", ".panels | length == 5", str(dashboard_path)])
    run_command(["jq", "-e", 'all(.panels[]; .type == "stat")', str(dashboard_path)])
    data = json.loads(dashboard_path.read_text(encoding="utf-8"))
    schema_version = data.get("schemaVersion")
    panel_count = len(data.get("panels", []))
    notes = f"Dashboard scorecards validado via jq (schemaVersion={schema_version}, painéis stat={panel_count})."
    return StageOutcome(
        notes=notes,
        details={
            "dashboard": str(dashboard_path.relative_to(BASE_DIR)),
            "schemaVersion": schema_version,
            "panel_count": panel_count,
        },
    )


def stage_s6() -> StageOutcome:
    report = generate_report()
    summary = report.get("summary", {})
    status = summary.get("status", "fail").upper()
    if status not in {"PASS", "FAIL"}:
        raise StageExecutionError(
            "S6-STATUS",
            f"Status inválido retornado pelo scorecard: {status}",
            context={"summary": summary},
        )
    notes = f"Scorecards {summary.get('passing', 0)}/{summary.get('total_metrics', 0)} verificados."
    details = {
        "report_path": str(S6_OUTPUT_DIR.relative_to(BASE_DIR)),
        "bundle_sha256": report.get("bundle_sha256"),
        "summary": summary,
    }
    if status == "FAIL":
        raise StageExecutionError(
            "S6-GUARD",
            notes,
            context={
                "summary": summary,
                "report_path": str(S6_OUTPUT_DIR.relative_to(BASE_DIR)),
                "bundle_sha256": report.get("bundle_sha256"),
            },
        )
    return StageOutcome(notes=notes, details=details)


STAGE_HANDLERS: Dict[str, StageHandler] = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def write_stage_files(stage: str, payload: Dict[str, Any]) -> None:
    ensure_output_dir()
    json_path = OUTPUT_DIR / f"{stage}.json"
    status_path = OUTPUT_DIR / f"{stage}.status"
    json_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    status_path.write_text(payload["status"] + "\n", encoding="utf-8")


def execute_stage(stage: str) -> Dict[str, Any]:
    handler = STAGE_HANDLERS.get(stage)
    if handler is None:
        raise StageExecutionError("UNKNOWN-STAGE", f"Stage desconhecido: {stage}")
    generated_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    reset_command_log()
    try:
        outcome = handler()
    except StageExecutionError as exc:
        notes = f"{ERROR_PREFIX}-{exc.code}:{exc.detail}"
        payload: Dict[str, Any] = {
            "schema_version": 1,
            "stage": stage,
            "status": "FAIL",
            "generated_at": generated_at,
            "notes": notes,
        }
        detail_payload: Dict[str, Any] = {"error_code": exc.code, "detail": exc.detail}
        if exc.context:
            detail_payload["context"] = exc.context
        command_log = get_command_log()
        if command_log:
            detail_payload["commands"] = command_log
        payload["details"] = detail_payload
        return payload
    except Exception as exc:  # pragma: no cover - defensive fallback
        notes = f"{ERROR_PREFIX}-UNEXPECTED:{exc}"
        payload = {
            "schema_version": 1,
            "stage": stage,
            "status": "FAIL",
            "generated_at": generated_at,
            "notes": notes,
            "details": {"exception": repr(exc)},
        }
        command_log = get_command_log()
        if command_log:
            payload["details"]["commands"] = command_log
        return payload
    payload = {
        "schema_version": 1,
        "stage": stage,
        "status": "PASS",
        "generated_at": generated_at,
        "notes": outcome.notes,
    }
    details: Dict[str, Any] = {}
    if outcome.details:
        details.update(outcome.details)
    command_log = get_command_log()
    if command_log:
        details["commands"] = command_log
    if details:
        payload["details"] = details
    return payload


def main() -> int:
    parser = ArgumentParser(description="Executa guardas de sprint para o Boss Final")
    parser.add_argument(
        "--stage", required=True, help="Identificador do estágio (s1..s6)"
    )
    args = parser.parse_args()
    stage = args.stage.lower().strip()
    result = execute_stage(stage)
    write_stage_files(stage, result)
    print(f"{result['status']} {stage}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
