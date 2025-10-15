# OBS-6 — Staleness Gauge
**Objetivo:** `data_freshness_seconds` (now - last_event_ts) por `source`.
**Aceite:** gauge monotônico não-negativo; testes com fixtures.
**Artefatos:** cálculo no app/pipeline; export do gauge.
**Evidências:** `metrics_unit.json` com amostra válida; D2 renderizado.
