# S4 — v1.4 FINAL (Gate Pre-GA M2)

> **Codex Engenheiro** — Operar em excelência Steve Jobs × Donald Knuth. Saída idempotente, sem placeholders, com provas executáveis.
> **Painel Oficial:** Donald Knuth, Steve Jobs, Fernando Pérez, Alan Kay, Leslie Lamport, Vitalik Buterin.

---

## 0) Contexto e Objetivo

- **Sprint:** Q1 • S4 — MVP Hardening + CE$ Fundações.
- **Meta:** Endurecer o MVP do MBP e fechar CE$ Fundações com **Gate Pre-GA (M2) aprovado**.

---

## 1) SLOs e Critérios de Aceite (não negociáveis)

| Domínio | SLO | Valor | Observações |
| --- | --- | --- | --- |
| Performance (DEC) | p95 ≤ 800 ms (60 min @ 120 rps) | 5xx = 0, erro de orquestração = 0 | thresholds aplicados em k6 + Prometheus |
| CDC | `lag p95 ≤ 120 s` (tabelas quentes) | `mbp_markets`, `mbp_quotes`, `mbp_resolutions`, `mbp_abuse_events` | coleta contínua |
| Dados | `schema_drift=0`, `data_contract_break=false`, `dbt tests=pass` | inclui regras A106/A87/A89 | fail-closed |
| Governança | Hook Coverage ≥ 98%, Audit Coverage ≥ 99% (rolling 24h) | watchers automáticos | métricas Prom/CI |
| FE (RUM) | INP p75 ≤ 200 ms | sem regressão | ingest Prom format |
| Segurança | SBOM/SAST/Secrets sem críticos; logs 0 PII | Trivy, Semgrep, Gitleaks | bloqueia merge |
| Âncora | Evidence Pack com SHA-256 + Merkle root + tag Git `anchor-M2-<root>` | scripts dedicados | torna release auditável |

---

## 2) Invariantes, Liveness e Ordem Temporal

1. **Materializar invariantes:** `docs/spec/invariants.md` com Safety (I1..I5), Liveness (L1..L3) e Ordem Temporal (O1..O2).
2. **Formalização TLA+:** `docs/spec/tla/dec_pre_ga.tla` com Init/Next/Safety/Liveness compatíveis com TLC/Apalache.
3. **Verificação opcional:** job de CI off-by-default para rodar TLC/Apalache e anexar relatório quando habilitado.

---

## 3) Fronteiras Arquiteturais & Reprodutibilidade

- Estruturar/validar diretórios: `engine/`, `data/` (`cdc/`, `analytics/dbt/`), `obs/` (`ops/prom/`, `ops/otel/`, `dashboards/`), `fe/` (`rum/`, `web/`), `schemas/`, `docs/` (`adr/`, `runbooks/`, `spec/`, `demo/`), `scripts/`, `sim/` (harness).
- Harness atual deve permanecer compatível com a separação futura (S5: `sim/` como serviço independente).
- **ENV pinado:** manter `requirements.lock`, `Cargo.lock`, `package-lock.json`, `ops/containers/orr.Dockerfile` com digest fixo.
- **Reprodutibilidade:** gerar `docs/REPRO.md` com 6 passos “do zero ao `make prega`”.

---

## 4) Entregáveis Obrigatórios

1. **Makefile** (`prega`, `env.pin`, `orr`, `bundle`, `anchors`, `flame`, `micro`, `dbt.docs`, `rum.docs`, `nb.perf`). `make prega` = env pin → ORR → bundle → anchors → export perf notebook.
2. **Scripts:**
   - `scripts/env_pin_check.sh` (checa ferramentas, locks e versões; falha se divergente).
   - `scripts/orr_s4_run.sh` (120 rps/60 m, coleta DEC/CDC, `dbt build`, schema compat, scanners, RUM snapshot, governança, bundle staging).
   - `scripts/s4_bundle.sh` (zipa evidências, ADRs, rules; gera SHA-256).
   - `scripts/anchor_root.py`, `scripts/anchor_integrity.sh` (Merkle root + tag Git `anchor-M2-<root>`).
   - `scripts/microbench_dec.sh` e `scripts/flamegraph_hotpaths.sh` (inclui cenário `--scenario dec_tail` com `dec_flame_p99.svg`).
3. **Observabilidade:**
   - `ops/prom/rules_s4.yaml` (DEC p95, CDC lag, SchemaDrift, Hook/Audit coverage, SLOBudgetBreach, CDCLagHigh, recuperação pós-rollback).
   - `ops/prom/decision_gap.rules.yaml` + `docs/runbooks/decision_gap.md`.
4. **Dados/Contratos/dbt:**
   - `analytics/dbt/models/mbp/schema.yml`, `analytics/dbt/models/mbp/README.md` (≥95% docs, lineage, owners).
   - `analytics/dbt/profiles/profiles.yml` pinado.
   - Publicar docs dbt como artifact (CI executa `dbt docs generate` + upload `catalog.json`, `manifest.json`, `index.html`).
5. **Schema Registry:**
   - `schemas/mbp/quotes/v1.2.0.json` e `scripts/schema_compat_check.py` (fail-closed para breaking). Guardar diff em `EVI/schema_diff.txt`.
6. **ADRs Accepted:** `docs/adr/ADR-001-DEC-SLO-Degrade-Rollback.md`, `ADR-002-Resolution-Engine-Regra.md`, `ADR-003-TWAP-Benchmarks.md`.
7. **Runbooks:** `docs/runbooks/dec_slo.md`, `cdc_lag.md`, `schema_registry.md`, `decision_gap.md`.
8. **RUM → Prom:** `fe/rum/collector.js`, `fe/rum/server.js` (porta 9314, métrica `web_vitals_inp_ms{page,env}`), `fe/rum/collector_publish.js`. Snapshot `/metrics` → `EVI/web_inp_snapshot.json`.
9. **CI (GitHub Actions):** `_s4-orr.yml` (reusável endurecido) e `s4-exec.yml` (dispatcher). Incluir jobs opcionais (off-by-default) para TLA e microbench (limites Knuth).
10. **Measurement Sheet:** `ops/obs/measurement_s4.csv` com KPIs definidos.
11. **ORR & Evidências:** k6 script `tests/perf/dec_120rps_60m.js`, métricas DEC/CDC exportadas, RUM snapshot, relatórios Trivy/Semgrep/Gitleaks, microbench/flame (`dec_flame.svg`, `dec_flame_p99.svg`), relatórios TLA (quando habilitado), âncora (`ANCHOR.json`, `ANCHOR.txt`, tag git), bundle `out/s4_evidence_bundle_<UTC>.zip` + `.sha256`.
12. **PR & Release:** cabeçalho do PR com `ANCHOR_ROOT`, link do Evidence Pack e resumo do `make prega`. Release com `ANCHOR_ROOT`, SHA-256 do bundle e lista de artefatos. Tags `s4-v1.4` e `anchor-M2-<root>`.
13. **Demo One-Pager:** `docs/demo/s4_prega_onepager.md` com roteiro em 7 passos + bloco “60s para ler o `make prega`”.

---

## 5) DoR / DoD

- **DoR:** ambientes `dev/stage` estáveis, acessos a APM/Logs/Traces/RUM, registry/CI ativos, drafts A106/A87/A89 prontos, painéis S3 operacionais, owners confirmados, locks presentes.
- **DoD:** SLOs atendidos, ORR bundle com SHA-256 + âncora, ADRs publicados, workflows verdes, release S4 publicada, nenhum waiver aberto.

---

## 6) Riscos e Mitigações

| Risco | Watcher/Hook | Mitigação |
| --- | --- | --- |
| DEC p95 > 800 ms | `slo_budget_breach` | degrade/rollback, profiling, hotfix, cache, GC, roteamento |
| CDC lag > 120 s | `cdc_lag` | degrade/rollback, otimizar ingest, partições, backpressure |
| Schema/Contracts | `schema_registry_drift` / `data_contract_break` | bloquear deploy, hotfix MINOR, revisão |
| dbt failures | `dbt_test_failure` | bloquear merge até correção |
| CWV/INP regressão | `web_cwv_regression` | rollback FE, otimizar hydration/preload |

---

## 7) Execução do Codex

1. Seguir esta spec literalmente; instruções em `AGENTS.md` continuam válidas exceto quando conflitarem com esta versão.
2. Scripts/CI sem placeholders e determinísticos. Sem dependências locais/sudo obrigatório.
3. Tudo essencial deve entrar no Evidence Pack.
4. Tag/âncora obrigatórias antes do PR.
5. Painel Oficial = gate de revisão (NOTA ≥ 9,6).

> **Checklist final:** gerar patch, rodar `make prega`, publicar Evidence Pack (com SHA-256 e ANCHOR_ROOT), abrir PR + release com informações completas.
