# OBS-3 — Prometheus Scrape
**Objetivo:** Garantir séries e p75/p95 calculáveis.
**Aceite:** métricas `amm_op_latency_seconds_*` acessíveis; `histogram_quantile` em 5m retorna valores.
**Artefatos:** exporter/app com `/metrics`; Prom (service do workflow) em execução.
**Evidências:** query salva (D1), `out/.../goldens_queries.json` (quando disponível).
