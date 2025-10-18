# Policy Manifesto — Sprint 2

Promovemos as seguintes regras para o modo org:

1. **`web_cwv_regression`** sai do beta após três sprints verdes consecutivas.
2. **`mbp_resolution_sla`** entra como gate obrigatório com alerta dedicado e runbook em <10 min.
3. **`cdc_lag`** mantém bloqueio automático para p95 > 120 s com canal DEC/PM.

Os budgets e watchers devem ser aprovados no Comitê SLO semanal, com logs de decisão arquivados em `out/orr_gatecheck/evidence/policy_engine_report.json`.
