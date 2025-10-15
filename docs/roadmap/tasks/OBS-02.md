# OBS-2 — OTel Collector (Dev)
**Objetivo:** Subir o Collector (dev) com OTLP→Prom/Tempo/Loki + tail sampling.
**Aceite:** health ok (`/healthz`), pipelines `metrics|traces|logs` ativos; spans com status/error coletados.
**Artefatos:** `ops/otel/collector-dev.yaml`.
**Evidências:** `out/obs_gatecheck/evidence/t1_scan.json` (otel=UP), screenshots/CLI dos pipelines.
