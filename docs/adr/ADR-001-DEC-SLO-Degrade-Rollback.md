# ADR-001 — Estratégia de Degrade e Rollback para o DEC

- **Status:** Accepted
- **Data:** 2024-03-04
- **Contexto:** O DEC precisa manter p95 ≤ 800 ms em alta carga. Falhas de performance exigem mecanismo previsível de degrade/rollback.
- **Decisão:** Implementar gatilhos automáticos baseados em `slo_budget_breach`. Ao detectar p95 > 0,8 s por 5 min, aplica-se degrade controlado (redução de features, caches agressivos). Persistindo por 5 min adicionais, executa-se rollback para versão estável anterior.
- **Consequências:**
  - Melhor previsibilidade operacional e alinhamento com runbook `dec_slo`.
  - Necessidade de instrumentação adicional (`dec:recovered:10m`).
  - Incremento na complexidade do pipeline de deployment, mitigado por scripts `make prega`.
