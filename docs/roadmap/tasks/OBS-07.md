# OBS-7 — CDC Lag Gauge
**Objetivo:** `cdc_lag_seconds` (consumer_wallclock - origin_commit_ts) por stream/partition.
**Aceite:** lag cresce sob throttle, reduz normalizando consumo; não negativo.
**Artefatos:** cálculo + export; Collector recebendo.
**Evidências:** D2 painel CDC; watchers W‑OBS‑003 disparando em simulação.
