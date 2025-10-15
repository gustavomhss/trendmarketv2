# OBS-4 — Tracing (Tempo/Jaeger)
**Objetivo:** Spans nomeados + atributos AMM + exemplars ligados às métricas.
**Aceite:** ver `amm.swap`, `amm.add_liquidity`, `cdc.consume`, `pricing.quote` no Tempo; link de exemplar a partir de p95.
**Artefatos:** instrumentação no app; Collector (traces) ativo.
**Evidências:** `out/.../golden_traces.json` = TRUE para operações principais.
