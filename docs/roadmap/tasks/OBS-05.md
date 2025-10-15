# OBS-5 — Logs (Loki)
**Objetivo:** Logs JSON com `trace_id`/`span_id` e correlação.
**Aceite:** consulta por `trace_id` retorna linha do erro/span lento.
**Artefatos:** appenders JSON; `ops/security/log_denylist.json` aplicado.
**Evidências:** `trace_log_smoke.json`.
