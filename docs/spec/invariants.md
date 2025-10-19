# Invariantes de Segurança, Liveness e Ordem Temporal (S4 • v1.4)

## Safety (I)

- **I1 — No-Trade-After-Resolve:** nenhuma quote é processada após `resolved_at` do respectivo mercado.
- **I2 — Backward-Compatible Schemas:** evoluções preservam campos obrigatórios e tipos; remoções exigem janela e waiver.
- **I3 — TWAP Bound:** divergência absoluta do TWAP ≤ 1.0% enquanto `market.status != "frozen"`.
- **I4 — Zero-PII Logs:** pipelines de logs expurgam campos classificados como PII antes de persistir/exportar.
- **I5 — Fail-Closed CI:** deploy bloqueado quando `schema_drift>0`, `contract_break=true` ou testes dbt falham.

## Liveness (L)

- **L1 — Rollback Timely:** incidente de SLO dispara rollback ≤ 10 min após `slo_budget_breach`.
- **L2 — CDC Recovery:** `cdc:lag_p95_seconds:5m` retorna ≤ 120 s em até 20 min após mitigação.
- **L3 — ADR Publication:** ADRs 001–003 aceitos antes do Gate M2.

## Ordem Temporal (O)

- **O1 — Pipeline DEC:** medir DEC → detectar `breach` → acionar SRE → executar degrade/rollback → recuperar DEC ≤ 0,8 s; janela ≤ 10 min.
- **O2 — Schema Governance:** mudança de schema → `schema_compat_check` no CI → {pass → merge, fail → bloqueio}; sem bypass sem waiver aprovado.
