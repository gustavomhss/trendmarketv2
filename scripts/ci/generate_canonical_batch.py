#!/usr/bin/env python3
from __future__ import annotations
from datetime import datetime, timezone
from pathlib import Path
import sys

# Garante que o repo root (<repo>/) esteja no sys.path para permitir "services.*"
ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.oracle.normalizer.normalizer import build_event  # noqa: E402
from services.oracle.normalizer.merkle_append_only import write_batch  # noqa: E402

def iso_now_z() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")

def main() -> None:
    now = datetime.now(timezone.utc).replace(microsecond=0)
    raw_events = [
        {
            "title": "Evento Workflow 1",
            "lang": "pt",
            "category": "mercado",
            "source": "operador",
            "observed_at": iso_now_z(),
            "payload": {"valor": 1},
        },
        {
            "title": "Evento Workflow 2",
            "lang": "es",
            "category": "salud",
            "source": "ministerio",
            "observed_at": iso_now_z(),
            "payload": {"valor": 2},
        },
    ]
    events = [build_event(evt) for evt in raw_events]
    Path("out/evidence/S7_event_model").mkdir(parents=True, exist_ok=True)
    write_batch(events, batch_ts=now)
    print("[S7] canonical batch generated")

if __name__ == "__main__":
    main()
