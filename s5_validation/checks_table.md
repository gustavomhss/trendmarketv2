Check ID | Status | Evidência (arquivo:linha) | Valor encontrado | Spec Anchor | Observação
---|---|---|---|---|---
ORCL-001 | pass | services/oracles/aggregator.py:L15-L125 | Mediana com `quorum_needed = ceil(2N/3)`, staleness ≤30s e divergência ≤1% | B.1 Oráculos | Cobertura de quorum/staleness/divergência confirmada.
TWAP-001 | pass | services/oracles/twap.py:L9-L138 | Deque 60s, failover ≤60s para fonte secundária, cálculo ∑(price·Δt)/60s | B.1 TWAP 60s | Failover gera evento `failover` auditável.
FEES-001 | pass | services/fees/engine.py:L9-L105 | Cooldown 300s, clamp e |Δfee| limitado a ±0.20 por atualização | B.1 Fees | Controle de delta separado do cooldown.
MOD-001 | pass | services/moderation/service.py:L12-L143 | Métodos pause/resume/appeal com RBAC e escrita JSONL | B.1 Moderação | Audit log assinado via hash SHA-256.
AUTO-001 | pass | services/auto_resolution/service.py:L220-L561 | Resolução automática, auditoria JSONL, métricas e eventos estruturados | B.1 Auto-resolução | Gera registro com quorum, truth e metadados.
AUTO-002 | mismatch | services/auto_resolution/service.py:L14-L520 | `AGREEMENT_THRESHOLD=0.6` definido mas `quorum_ok` ignora `agreement_score` | B.1 Auto-resolução | Recomendar aplicar limiar para reforçar ≥2/3 de votos.
SIM-001 | pass | tools/sim_harness.py:L47-L143 | Harness determinístico (`SEED=42`), cenários spike/gap/burst, relatórios JSON | B.1 Simulações determinísticas | Eventos TWAP capturados e persistidos.
DBT-001 | pass | .github/workflows/_s4-orr.yml:L420-L443 | Step executa `dbt deps/debug/run/test` com DuckDB 1.8.0 | B.6 DBT | Perfil DuckDB provisionado automaticamente.
DBT-002 | pass | target/run_results.json:L1-L120 & 71eb32†L1-L11 | 50 resultados `success` (100%) no `run_results.json` | B.6 DBT | Execução offline validada.
WORK-001 | pass | .github/workflows/s4-exec.yml:L43-L54 | Inputs booleanos consumidos com `fromJSON(... || 'false')` | B.3 Workflows | Wrapper mantém contratos reutilizáveis.
WORK-002 | pass | .github/workflows/_s4-orr.yml:L410-L534 | Steps "S5 Simulation — ..." e "S5 DBT (DuckDB) — ..." + upload `s4-orr-evidence` (`out/**`, `target/**`, `logs/**`) | B.3 Workflows | Ordem preservada e artifact `if-no-files-found: warn`.
OBS-001 | pass | observability/prometheus/slo.rules.yml:L1-L96 | Regras para `staleness_ms`, `diverg_pct`, `quorum_ratio`, `failover_time_s`, `delta_fee_5m` | B.8 Observabilidade | Inclui alertas para auto-resolve.
OBS-002 | fail | observability/grafana/dashboards/s5_mbp_scale.json:L1-L220 | Painéis cobrem staleness/divergência/fees/moderação/simulações, mas sem `quorum_ratio` ou `failover_time` | B.8 Observabilidade | Adicionar visibilidade das métricas canônicas faltantes.
DOC-001 | pass | api/openapi.yaml:L8-L158 | Endpoints `/oracle/quote`, `/moderation/pause`, `/resolve/apply` com schemas v1 | B.7 OpenAPI & Schemas | Estrutura satisfaz requisitos mínimos.
SCHEMA-001 | pass | schemas/oracle.quote.v1.json:L1-L29; schemas/moderation.action.v1.json:L1-L32; schemas/fee.update.v1.json:L1-L44 | `schema_version=1`, campos obrigatórios e tipos coerentes | B.7 Schemas | JSON Schema 2020-12 adotado.
SEC-001 | pass | d08d67†L1-L2 | Varredura de segredos (`AKIA/ASIA/AZia/PK`) sem ocorrências | B.9 Segurança | Sem credenciais em texto plano.
HYGIENE-001 | pass | 17b934†L1-L2; e8c1be†L1-L2 | Sem CRLF ou TAB em `.github/workflows` | B.5 Higiene | Arquivos UTF-8/LF.
