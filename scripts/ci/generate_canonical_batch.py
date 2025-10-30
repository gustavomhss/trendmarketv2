"""Utility to synthesise a canonical batch for CI validation."""
from __future__ import annotations

from datetime import datetime, timezone

from services.oracle.normalizer.merkle_append_only import write_batch
from services.oracle.normalizer.normalizer import build_events


def _isoformat_now(now: datetime) -> str:
    return now.replace(microsecond=0).isoformat().replace("+00:00", "Z")


def main() -> None:
    now = datetime.now(timezone.utc)
    observed = _isoformat_now(now)

    raw_events = (
        {
            "title": "Evento Workflow 1",
            "lang": "pt",
            "category": "mercado",
            "source": "operador",
            "observed_at": observed,
            "payload": {"valor": 1},
        },
        {
            "title": "Evento Workflow 2",
            "lang": "es",
            "category": "salud",
            "source": "ministerio",
            "observed_at": observed,
            "payload": {"valor": 2},
        },
    )

    normalised = [dict(event) for event in build_events(raw_events, now=now)]
    write_batch(normalised, batch_ts=now)


if __name__ == "__main__":
    main()
