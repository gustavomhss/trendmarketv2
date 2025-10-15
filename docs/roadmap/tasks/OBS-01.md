# OBS-1 — SDK & Wiring OTel
**Objetivo:** Exportar métricas/traços/logs via OTLP; expor histogram de latência e gauges base.
**Aceite:** /metrics com séries; Collector recebe spans; logs com trace_id.
**Artefatos:** `src/**`, `ops/otel/collector-dev.yaml`.
**Evidências:** `out/obs_gatecheck/evidence/metrics_unit.json`, `trace_log_smoke.json`.
