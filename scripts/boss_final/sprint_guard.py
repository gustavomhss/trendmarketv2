#!/usr/bin/env python3
from __future__ import annotations

import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List

BASE_DIR = Path(__file__).resolve().parents[2]
OUTPUT_ROOT = BASE_DIR / "out" / "q1_boss_final" / "stages"
SCORECARD_DIR = BASE_DIR / "out" / "s6_scorecards"

StageRunner = Callable[[Path, List[str]], str]


class StageError(RuntimeError):
    def __init__(self, message: str) -> None:
        super().__init__(message)
        self.message = message


def run_command(stage_dir: Path, logs: List[str], command: List[str], description: str) -> None:
    result = subprocess.run(command, capture_output=True, text=True)
    log_entry = [f"$ {' '.join(command)}", result.stdout.strip(), result.stderr.strip()]
    logs.append("\n".join(filter(None, log_entry)))
    if result.returncode != 0:
        raise StageError(f"{description} falhou com código {result.returncode}")


def stage_s1(stage_dir: Path, logs: List[str]) -> str:
    run_command(
        stage_dir,
        logs,
        [sys.executable, "-m", "pytest", "-q", "tests/scorecards"],
        "Testes de scorecards",
    )
    return "Testes de scorecards executados com sucesso."


def stage_s2(stage_dir: Path, logs: List[str]) -> str:
    run_command(
        stage_dir,
        logs,
        [sys.executable, "-m", "compileall", "services"],
        "Compilação dos serviços",
    )
    return "Compilação dos módulos de serviço concluída."


def stage_s3(stage_dir: Path, logs: List[str]) -> str:
    dashboard = BASE_DIR / "dashboards" / "grafana" / "scorecards_quorum_failover_staleness.json"
    content = json.loads(dashboard.read_text(encoding="utf-8"))
    titles = [panel.get("title") for panel in content.get("panels", [])]
    logs.append(f"Painéis carregados: {titles}")
    expected = [
        "Quorum ratio",
        "Failover time p95 (s)",
        "Replica staleness p95 (s)",
        "CDC lag p95 (s)",
        "Oracle divergence (%)",
    ]
    if titles != expected:
        raise StageError("Painéis do dashboard divergentes do contrato.")
    return "Dashboard de observabilidade validado com cinco painéis mandatórios."


def stage_s4(stage_dir: Path, logs: List[str]) -> str:
    thresholds = BASE_DIR / "s6_validation" / "thresholds.json"
    metrics = BASE_DIR / "s6_validation" / "metrics_static.json"
    for path in (thresholds, metrics):
        data = json.loads(path.read_text(encoding="utf-8"))
        logs.append(f"Validado {path.name} com version={data.get('version')}")
    return "Bundles de thresholds e métricas conferidos."


def stage_s5(stage_dir: Path, logs: List[str]) -> str:
    run_command(
        stage_dir,
        logs,
        [sys.executable, "-m", "json.tool", "schemas/report.schema.json"],
        "Validação do schema de report",
    )
    return "Schema de report JSON validado."


def stage_s6(stage_dir: Path, logs: List[str]) -> str:
    run_command(
        stage_dir,
        logs,
        [sys.executable, "scripts/scorecards/s6_scorecards.py"],
        "Geração do scorecard",
    )
    if SCORECARD_DIR.exists():
        for artefact in ["report.json", "bundle.sha256", "guard_status.txt"]:
            source = SCORECARD_DIR / artefact
            if source.exists():
                shutil.copy2(source, stage_dir / artefact)
    return "Scorecard gerado e artefatos copiados."


STAGES: Dict[str, StageRunner] = {
    "s1": stage_s1,
    "s2": stage_s2,
    "s3": stage_s3,
    "s4": stage_s4,
    "s5": stage_s5,
    "s6": stage_s6,
}


def write_stage_outputs(stage: str, status: str, notes: str, logs: List[str], stage_dir: Path) -> None:
    stage_dir.mkdir(parents=True, exist_ok=True)
    (stage_dir / "guard_status.txt").write_text(f"{status}\n", encoding="utf-8")
    data = {
        "stage": stage,
        "status": status,
        "timestamp_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        "notes": notes,
    }
    (stage_dir / "stage.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    (stage_dir / "logs.txt").write_text("\n\n".join(logs) + "\n", encoding="utf-8")


def run_stage(stage: str) -> int:
    if stage not in STAGES:
        raise SystemExit(f"BOSS-E-STAGE: Estágio desconhecido {stage}")
    stage_dir = OUTPUT_ROOT / stage
    stage_dir.mkdir(parents=True, exist_ok=True)
    logs: List[str] = []
    runner = STAGES[stage]
    try:
        notes = runner(stage_dir, logs)
    except StageError as exc:
        write_stage_outputs(stage, "FAIL", exc.message, logs, stage_dir)
        print(f"FAIL {stage.upper()} {exc.message}")
        return 1
    except Exception as exc:  # pragma: no cover - robust fallback
        write_stage_outputs(stage, "FAIL", f"Erro inesperado: {exc}", logs, stage_dir)
        print(f"FAIL {stage.upper()} {exc}")
        return 1
    else:
        write_stage_outputs(stage, "PASS", notes, logs, stage_dir)
        print(f"PASS {stage.upper()} {notes}")
        return 0


def parse_args(argv: List[str]) -> str:
    if len(argv) != 3 or argv[1] != "--stage":
        raise SystemExit("Uso: sprint_guard.py --stage <s1|s2|s3|s4|s5|s6>")
    return argv[2]


def main(argv: List[str]) -> int:
    stage = parse_args(argv)
    return run_stage(stage)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
