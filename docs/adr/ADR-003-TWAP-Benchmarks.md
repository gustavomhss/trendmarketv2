# ADR-003 — Benchmarks de TWAP

- **Status:** Accepted
- **Data:** 2024-03-04
- **Contexto:** Necessário validar performance e precisão de cálculo do TWAP sob diferentes regimes de mercado.
- **Decisão:** Estabelecer suíte de benchmarks para `engine::dec_paths::{match_core, route_fast, twap_update}` com limites de média/desvio (1.20 ms/0.15 ms; 0.70 ms/0.10 ms; 0.45 ms/0.08 ms) e cenário de cauda p99 (`dec_tail`). Resultados devem ser capturados em `microbench.txt` e `dec_flame_p99.svg`.
- **Consequências:**
  - Execução periódica via job opcional no CI.
  - Necessidade de manter harness determinístico em `sim/`.
  - Base para tuning de garbage collection e caches.
