---
id: kb/product/briefings/ce_product_brief_v_2_0_ultra_gold
title: "CreditEngine$ — Product Brief v2.0 (Bíblia do CE)"
version: "v2.7 — Ultra Gold (Merged with CE$ MVP v6.0)"
date: "2025-09-07"
timezone: America/Bahia
owner: PO Agent (GPT)
stewards: [Produto, Engenharia, Dados, Risco]
doc_type: product_brief
policy:
  knowledge_scope: "Somente Master List (A1–A110) e Blocos 1–12."
  citation_rule: "Todo ponto técnico referencia packs (ex.: A106-DATA-CONTRACTS-ADV)."
  no_placeholders: true
links:
  - kb/blocos/1..12
  - kb/po/creditengine/po_ops_manual_five_star_v1_5
watchers:
  required: [$1, okr_risk_alignment_watch]
---

# 0) Sumário Executivo (1 página)
O **CreditEngine$ (CE)** é um sistema modular para **decisão e precificação de crédito** com **observabilidade, governança e resiliência** embutidas desde o design. Ele integra **dados transacionais** (CDC), **contratos de dados** (compat/backward), **mecanismos de leilão e preço**, **oráculos de mercado**, **serving de modelos** e **hooks automáticos de decisão** (A110) que ligam **métricas→ações** sem intervenção manual.

**Objetivos-chave (North Star + KRs)**  
- **NSM**: *Time‑to‑Preço‑Válido* p75 ≤ **0.5 s** (p95 ≤ **0.8 s**) para a jornada de decisão, alinhado aos SLOs de P1 (A71–A72).  
- **KRs**: (i) ≥ **95%** das decisões com **trilha de auditoria** (A90/A93), (ii) **CDC lag p95 ≤ 120s** (A105/A88), (iii) **Drift PSI ≤ 0.2** e **KS ≤ 0.1** (A84), (iv) **Staleness de oráculo < 30s** (A104), (v) **SRM=OK** em experimentos (A83).

**Entrega em ondas (0–90 dias)**  
- **Fundações (P5/P1)**: CDC+Contracts+Tables (A105–A89–A86) + Decision Core/Hooks (A110) + Observabilidade (A71–A72).  
- **Mercado (P2/P3/P4)**: Leilões (A10), FX quoting/roteamento (A98–A100), Oráculos (A104).  
- **Modelos (P6)**: Serving/Monitoring (A81/A84) + A/B (A83).  
- **Governança & XP (P7/P8)**: MRM/Postmortem/BCDR/OKRs (A90–A93/A109) + Portais/FE (A74–A80/A77).

**Governança**: nenhum deploy sem **watchers verdes** e **hooks ativos**; exceções tramitam por **waiver** (A106) com prazo e rollback previstos.

---

## 0.1 Premissas & Não‑Objetivos
**Premissas**: (i) fontes de dados acessíveis via CDC (A105/A88); (ii) contratos e semântica definidos por domínio (A106/A87); (iii) modelo exportável para serving (A81); (iv) observabilidade padrão OTel (A71–A72); (v) formal necessário onde houver risco crítico (A103); (vi) portais internos protegidos (A77).  
**Não‑objetivos**: emissão de dívida própria; app externo para cliente final; marketplace público de risco (nesta v2).

## 0.2 Critérios de Sucesso & Baselines (ligados a hooks A110)
| KPI | Baseline | Gate (Go/No‑Go) | Hook (A110) | Owner |
|---|---:|---:|---|---|
| Time‑to‑Preço‑Válido p75 | 0.5 s | p95 ≤ 0.8 s | `latency>0.8s•5m•degrade` | SRE/PO |
| CDC lag p95 | 120 s | ≤ 120 s | `lag>120s•5m•degrade+tickets` | DC/PY |
| Drift PSI/KS | PSI ≤ 0.2; KS ≤ 0.1 | dentro da faixa | `psi>0.2•24h•rollback` | ML |
| Oráculo staleness | < 30 s | < 30 s | `>30s•5m•TWAP+failover` | BC |
| SRM A/B | OK | OK | `srm_fail•run•pause+audit` | ST |
| CWV INP | ≤ 200 ms p75 | ≤ 200 ms p75 | `inp>200ms•24h•rollback_FE` | FE |

## 0.3 Artefatos por Fase
- **Catálogo de Produtos/Features** (Seções 2/7).  
- **Roadmap & Gates** (Seção 10).  
- **Briefing vFinal** (este).  
- **Backlog PO‑ready** (gerado a partir das features).  
- **Matriz Épico→Papéis→Packs** (time de agentes).  
- **Hooks A110** (YAML) e **Contratos de Dados** (A106/A87).  
- **Golden Notebooks** quando cabível (A94/A95/A97).  

## 0.4 Matriz de Rastreabilidade (Requisitos ↔ Packs ↔ Watchers ↔ Hooks)
| Requisito | Packs | Watchers | Hook padrão |
|---|---|---|---|
| Dados confiáveis | A105/A88/A106/A87/A86/A89 | `cdc_lag_watch`, `data_contract_break_watch`, `schema_registry_drift_watch`, `dbt_test_failure_watch` | `lag>120s•degrade` |
| Decisão rápida | A110/A81/A84/A83 | `metrics_decision_hook_gap_watch`, `model_drift_watch`, `slo_budget_breach_watch` | `psi>0.2•rollback` |
| Mercado robusto | A104/A103/A98–A100 | `formal_verification_gate_watch`, `slo_budget_breach_watch` | `staleness>30s•TWAP` |
| Segurança web | A77/A74–A80 | `web_cwv_regression_watch`, `api_breaking_change_watch` | `inp>200ms•rollback_FE` |
| Alinhamento a OKRs | A109 | `okr_risk_alignment_watch` | `okr_gap•run•ajustar_prioridade` |

---

## 0.5 Quality Gates — Master Checklist (Go/No‑Go por fase)
- [ ] **Watchers do escopo**: verdes por ≥24h contínuas  
- [ ] **Hooks A110**: ativos e com evidência de *dry‑run*  
- [ ] **Contratos de dados** (A106/A87): CI de compat OK + *schema tests* dbt OK  
- [ ] **BCDR** (A91–A92): *tabletop* ≤ 90 dias  
- [ ] **MRM/Postmortem** (A90/A93): docs atualizadas; backlog de ações crítico = 0  
- [ ] **KPIs de fase**: atingidos (ou risco/mitigação aprovada por ADR)  
- [ ] **Artefatos publicados**: catálogo/roadmap atualizados; ADRs e waivers versionados  
|---|---|---|
| Dados confiáveis | A105/A88/A106/A87/A86/A89 | `cdc_lag_watch`, `data_contract_break_watch`, `schema_registry_drift_watch`, `dbt_test_failure_watch` | `lag>120s•degrade` |
| Decisão rápida | A110/A81/A84/A83 | `metrics_decision_hook_gap_watch`, `model_drift_watch` | `psi>0.2•rollback` |
| Mercado robusto | A104/A103/A98–A100 | `formal_verification_gate_watch`, `slo_budget_breach_watch` | `staleness>30s•TWAP` |
| Segurança web | A77/A74–A80 | `web_cwv_regression_watch` | `inp>200ms•rollback_FE` |

---

# 1) Problema, Contexto e Escopo
## 1.1 Problema
Precificar e decidir em crédito sob **volatilidade de dados** (mercado/FX) e **qualidade variável** de fontes internas demanda **SLA de resposta baixo**, **precisão**, **trilha de auditoria** e **resiliência** a incidentes.

## 1.2 Oportunidade
Automatizar **fim‑a‑fim**: da ingestão (CDC) e contratos de dados até **leilões de funding**, **hedge FX**, **serving de modelos** e **gates automáticos**, elevando **conversão**, reduzindo **custo de capital** e **risco operacional**.

## 1.3 Fora de escopo (v2)
Emissão de instrumentos próprios de dívida, *mobile app* externo para cliente final e marketplace público de risco **não** entram nesta v2.

---

# 2) Catálogo de Produtos/Serviços (ordem cronológica)
> Para cada item: **propósito, usuários, entradas, saídas, SLAs/KPIs, dependências, riscos/controles, watchers, packs**.

## P1 — Decision & Pricing Core
- **Propósito**: decidir (aprovar/condicionar/negar) e precificar taxa com justificativa.  
- **Usuários**: originação, risco, operações.  
- **Entradas**: dados transacionais/score; cotações (opcional).  
- **Saídas**: decisão, taxa proposta, trilha de auditoria (A90/A93).  
- **SLAs/KPIs**: p95 ≤ 800 ms; ≥ 70% automação.  
- **Dependências**: P5 (CDC/Contracts), P6 (modelos).  
- **Riscos/controles**: leakage/model drift; MRM (A90).  
- **Watchers**: `metrics_decision_hook_gap_watch`, `model_drift_watch`.  
- **Packs**: A110, A81, A84, A83, A90–A93.

## P2 — Auctions (Funding)
- **Propósito**: alocar funding via leilão reverso/clearing.  
- **SLAs**: p95 ≤ 500 ms; fill ≥ 90%.  
- **Watchers**: `slo_budget_breach_watch`.  
- **Packs**: A10, A28.

## P3 — FX Quoting & Hedging
- **Propósito**: cotações FX e roteamento ótimo com *toxicity filters*.  
- **SLAs**: spread eficaz; *fill ratio* ≥ 95%.  
- **Watchers**: `fx_delta_benchmark_watch`, `slo_budget_breach_watch`.  
- **Packs**: A98–A100.

## P4 — Oracles & Market Data Gateway
- **Propósito**: fluxos de preço robustos (TWAP/heartbeats/deviation).  
- **SLAs**: staleness < 30s; uptime ≥ 99.9%.  
- **Watchers**: `formal_verification_gate_watch`.  
- **Packs**: A104, A103, A102.

## P5 — Data Foundation (CDC, Contracts, Tables, dbt)
- **Propósito**: dados confiáveis e versionados.  
- **SLAs**: lag CDC p95 ≤ 120 s; incompat ratio=0.  
- **Watchers**: `cdc_lag_watch`, `data_contract_break_watch`, `schema_registry_drift_watch`, `dbt_test_failure_watch`.  
- **Packs**: A105, A88, A86–A89, A106, A87.

## P6 — ML Serving & Monitoring
- **Propósito**: servir modelos com baixa latência e segurança.  
- **SLAs**: P99 ≤ alvo; warmup/dynamic batching; drift PSI/KS em faixa.  
- **Watchers**: `model_drift_watch`.  
- **Packs**: A81, A84, A83.

## P7 — Governança & Resiliência
- **Propósito**: MRM, postmortem, BCDR e OKRs.  
- **Watchers**: `postmortem_action_breach_watch`, `bcdr_test_freshness_watch`, `okr_risk_alignment_watch`.  
- **Packs**: A90–A93, A109.

## P8 — Experience Layer (FE/Mobile)
- **Propósito**: portais internos/dashboards com segurança web.  
- **SLAs**: CWV p75 verdes (LCP≤2.5s, INP≤200ms, CLS≤0.1).  
- **Watchers**: `web_cwv_regression_watch`.  
- **Packs**: A74–A80, A77.

---

# 3) Personas e Jornadas E2E
- **Originação** → **Decision Core** (P1) → **Auctions** (P2) → **FX Hedge** (P3) → **Liquidação**.  
- **Dados**: sistemas de origem → **CDC** (P5) → **Lakehouse** (A86) → **dbt** (A89) → **dashboards**.  
- **Modelos**: desenvolvimento → **serving** (A81) → **monitoramento** (A84) → **A/B** (A83) → **rollback** via **A110**.

Cada jornada tem **telemetria OTel (A71–A72)**, **contratos de dados (A106/A87)** e **gates**; incidentes passam por **postmortem (A93)**.

---

# 4) Requisitos
## 4.1 Funcionais (amostra)
- Decidir e precificar com justificativas (A90).  
- Leilão/clearing com trilha de auditoria (A10/A28).  
- FX: delta conventions e roteamento (A98–A100).  
- Oráculos com TWAP/heartbeats (A104).  
- CDC, contratos, tabelas, dbt (A105–A89–A86).  
- ML serving + drift/DQ (A81/A84).

## 4.2 Não‑funcionais
- **Latência**: P1 p95 ≤ 800 ms; P2 p95 ≤ 500 ms; P4 staleness < 30s.  
- **Confiabilidade**: uptime ≥ 99.9% em serviços críticos.  
- **Segurança**: CSP nonce/Trusted Types/CSRF (A77); chaves e ECDSA/EdDSA/BLS (A102).  
- **Governança**: MRM/BCDR/Postmortem/OKRs (A90–A93/A109).

---

# 5) Arquitetura Lógica (texto)

## 5.1 Entidades e Eventos Canônicos (dados)
- **pricing_events** (A106/A87): decisão/price, qualidade, origem.  
- **oracle_ticks** (A104): preço, fonte, staleness, TWAP.  
- **fx_quotes** (A98–A100): par, bid/ask, rota, *toxicity*.  
- **cdc_offsets** (A105/A88): posição e lag por origem.

## 5.2 Contratos de Fronteira
Todos via **A106** (compat backward) com **tests dbt/expectations** (A89/A87) e CI.

## 5.3 APIs (exemplo Decision Core)
**Request**
```json
{"applicant_id":"...","features":{"income":12000,"score":712},"fx_pair":"USD/BRL","ts":"2025-09-07T10:00:00Z"}
```
**Response**
```json
{"decision":"approved","rate_bps":1520,"explain":["policy:income_ratio","model:v1.3"],"audit_id":"dec#123"}
```

## 5.4 SLOs por Serviço & Watchers
| Serviço | SLO principal | Watchers | Packs |
|---|---|---|---|
| Decision Core | p95 ≤ 800ms | `slo_budget_breach_watch`, `metrics_decision_hook_gap_watch` | A110, A81, A84 |
| Auctions | p95 ≤ 500ms | `slo_budget_breach_watch` | A10, A28 |
| Oracles | staleness < 30s | `formal_verification_gate_watch` | A104, A103 |
| CDC | lag p95 ≤ 120s | `cdc_lag_watch` | A105, A88 |
| Data Contracts/dbt | compat OK/tests OK | `data_contract_break_watch`, `schema_registry_drift_watch`, `dbt_test_failure_watch` | A106, A87, A89 |
| ML Serving | P99 ≤ alvo; drift controlado | `model_drift_watch` | A81, A84 |
| FE/Portais | INP p75 ≤ 200ms | `web_cwv_regression_watch` | A74–A80, A77 |
json
{"applicant_id":"...","features":{"income":12000,"score":712},"fx_pair":"USD/BRL","ts":"2025-09-07T10:00:00Z"}
```
**Response**
```json
{"decision":"approved","rate_bps":1520,"explain":["policy:income_ratio","model:v1.3"],"audit_id":"dec#123"}
```
**Camada Dados (P5)**: fontes → Debezium (A105/A88) → Lakehouse (A86) → dbt (A89) → métricas & semântica (A87).  
**Camada Mercado (P3/P4)**: oracles (A104) → gateways → roteamento FX (A100).  
**Camada Decisão (P1/P6)**: Decision Core + Model Serving (A81) com monit (A84), A/B (A83), hooks (A110).  
**Camada Observabilidade/Gov (P7)**: OTel (A71–A72), MRM (A90), BCDR (A91–A92), Postmortem (A93).  
**Camada Experiência (P8)**: Next.js/FE (A74–A75) com segurança web (A77).

**Contratos de Fronteira** (todos via **A106**): payloads, versões, compatibilidade e rollback definidos; schema tests e CI (A87/A89).

---

# 6) Decisão & Algoritmos (resumo com exemplos)
- **Auctions (P2)**: leilão reverso; **exemplo**: 4 provedores ofertam custo de capital; clearing por prioridade de taxa e capacidade (A10/A28).  
- **FX (P3)**: **delta conventions** (spot/forward/premium), **roteamento** com filtros de *toxicity* (VPIN) (A98–A100).  
- **Modelos (P6)**: serving com **dynamic batching** e **TensorRT/FP16/INT8** onde suportado (A81); **drift** PSI/KS (A84).  
- **Hooks (A110)**: cada KPI com limiar/ação, ex.: **PSI>0.2 → rollback**; **SRM falho → freeze teste**.

---

# 7) Métricas→Ações (A110) — Biblioteca‑base
Formato: `<KPI> • limiar • janela • ação • owner • evidência/log • rollback`  
- Lag CDC • >120s • 5m • degrade p/ tabela quente + ticket DC • DC • trace#cdc • yes  
- PSI (drift) • >0.2 • 24h • rollback baseline + abrir ST‑ML‑retrain • ML • ml#001 • yes  
- Oráculo staleness • >30s • 5m • fallback TWAP + failover • BC • orc#123 • yes  
- SRM • p<0.05 • run • pausar leitura + auditoria de instrumentação • ST • ab#srm • n/a  
- CWV INP • >200ms • 24h • rollback de feature + otimização • FE • rum#web • yes

---

# 8) Cenários & Simulações (operacionais)
> Roteiros prontos para *tabletop* ou execução assistida; cada cenário lista **entradas**, **passos**, **hooks** e **resultados esperados**.

## C1 — **Staleness de Oráculo**
- **Entrada**: fonte primária cai; secundária ativa.  
- **Passos**: staleness>30s → hook aciona TWAP (5m) → failover → auditoria.  
- **Hooks**: `staleness>30s` (A110).  
- **Resultado**: cotações continuam; logs/alertas completos; postmortem se >15min.

## C2 — **Drift de Modelo**
- **Entrada**: PSI=0.25 em 24h.  
- **Passos**: rollback baseline → abrir retraining → A/B com *holdout*.  
- **Hooks**: `PSI>0.2` (A110).  
- **Resultado**: latência estável; métricas recuperam.

## C3 — **CDC Lag**
- **Entrada**: burst de escrita eleva lag p95>120s.  
- **Passos**: degrade mode (tabela quente), investigar slot/checkpoint; rebalance; compaction.  
- **Hooks**: `lag>120s` (A110).  
- **Resultado**: sistema segue útil; backlog CDC normalizado.

## C4 — **SRM em A/B**
- **Entrada**: distribuição de tráfego anômala.  
- **Passos**: pausar leitura; revisar *bucketing*; checar instrumentação; reiniciar teste.  
- **Hooks**: `ab_srm_watch`.  
- **Resultado**: testes confiáveis, sem *peeking*.

## C5 — **Explosão de Latência (FE)**
- **Entrada**: INP>200ms p75.  
- **Passos**: rollback de feature; revisar code‑split; image perf; CDN cache.  
- **Hooks**: `web_cwv_regression_watch`.  
- **Resultado**: CWV normaliza; conversão preservada.

## C6 — **BCDR Tabletop**
- **Entrada**: região primária indisponível.  
- **Passos**: ativar DR; checar RPO/RTO; *rehealthchecks*; checklist A91.  
- **Hooks**: `bcdr_test_freshness_watch`.  
- **Resultado**: failover controlado e reversível.

## C7 — **FX Shock**
- **Entrada**: gap de 150 bps na abertura.  
- **Passos**: rotas com *toxicity filter*; spreads adaptativos; circuit breakers.  
- **Hooks**: `slo_budget_breach_watch`.  
- **Resultado**: proteção de preço; auditoria de decisões.

## C8 — **Schema Drift**
- **Entrada**: coluna renomeada na origem.  
- **Passos**: `schema_registry_drift_watch` alerta → CI falha → rollback; abrir waiver se necessário (A106).  
- **Resultado**: compat preservada; documentação atualizada.

## C9 — **dbt Tests Failing**
- **Entrada**: `unique`/`not_null` falha.  
- **Passos**: corrigir fonte/transform; reexecutar; postmortem se recorrente.  
- **Hooks**: `dbt_test_failure_watch`.  
- **Resultado**: dados estáveis.

## C10 — **Auction Stress**
- **Entrada**: pico de 3× provedores.  
- **Passos**: scaler→autoscale; batching; circuit breaker; logs.  
- **Watchers**: `slo_budget_breach_watch`.  
- **Resultado**: clearing estável, auditoria íntegra.

---

# 9) Exemplos Didáticos (com *artefatos*)
## 9.1 Contrato de dados `pricing_events` (A106/A87)
```yaml
contract_id: ce.pricing_events.v1
owner: Data Contracts (DC)
schema:
  id: string (pk)
  ts: timestamp
  decision_id: string
  price_bps: int
  fx_pair: string
  source: enum[primary,secondary]
  quality: int range[0,100]
compatibility: backward
expectations:
  - not_null: [id, ts, decision_id, price_bps]
  - range: { field: quality, min: 0, max: 100 }
  - accepted_values: { field: source, values: [primary, secondary] }
slas:
  freshness: { p95_sec_max: 120 }
waivers: none
```

## 9.2 Hook de drift (A110/A84)
```yaml
hook: model_drift_guard
kpi: psi
threshold: 0.2
window: 24h
action: rollback_to: model_baseline_v0_9
owner: ML
log: ml#psi_guard_001
rollback: yes
```

## 9.3 Leilão (A10) — micro‑simulação
- **Lances**: P1 1.12%/R$10MM; P2 1.15%/R$20MM; P3 1.20%/R$15MM; P4 1.08%/R$5MM.  
- **Clearing**: ordena por taxa ascendente até atender demanda; P4 (5) + P1 (10) + P2 (5 de 20) = **clearing 1.12%** em **R$20MM**, **residual** P2=15, P3=15.  
- **Auditoria**: registra *ledger* de lances, tempo e fonte.

---

# 10) Roadmap & Gates (0–90 dias)
> **Critério de saída de cada fase**: *todos* watchers do escopo **verdes**, **hooks ativos** e **artefatos publicados** (contratos, hooks, notebooks/goldens quando cabível).
**T0–T2 (Semanas 1–4)** — P5/P1 fundações: CDC (A105/A88), Contracts (A106/A87), Tables/dbt (A86/A89), Hooks base (A110).  
**Gates**: `data_contract_break_watch=ok`, `cdc_lag_watch p95<=120s`, *schema tests* dbt ok.

**T3–T4 (5–8)** — P2/P3/P4: Auctions (A10/A28), FX (A98–A100), Oracles (A104/A103).  
**Gates**: `formal_verification_gate_watch=ok`, `slo_budget_breach_watch=ok`.

**T5 (9–10)** — P6: Serving/Monitoring (A81/A84) + A/B (A83).  
**Gates**: `model_drift_watch=ok`, SRM ok.

**T6 (11–12)** — P7: MRM/Postmortem/BCDR/OKRs (A90–A93/A109).  
**Gates**: `bcdr_test_freshness_watch=ok`, backlog de ações=0.

**T7 (13–14)** — P8: Portais/FE (A74–A80/A77) + segurança web (A77).  
**Gates**: `web_cwv_regression_watch=ok`.

---

# 11) Riscos & Controles (Top 10)
| Risco | Sinal | Controle/mitigação | Packs | Watchers |
|---|---|---|---|---|
| Dados ruídos/defasados | Freshness baixa | Contratos + expectations + freshness | A106/A87 | `data_contract_break_watch`, `schema_registry_drift_watch` |
| Drift de modelo | PSI/KS alto | Rollback + retrain + A/B | A84/A110/A83 | `model_drift_watch` |
| Oráculo manipulável | Desvio grande | TWAP/heartbeats + formal | A104/A103 | `formal_verification_gate_watch` |
| FX toxicity | VPIN ↑ | Filtros + roteamento | A100 | `slo_budget_breach_watch` |
| CDC backlog | Lag ↑ | Degrade + DLQ + compaction | A105/A88 | `cdc_lag_watch` |
| SRM em A/B | Split errado | Pausa + auditoria | A83 | `ab_srm_watch` |
| XSS/CSRF | Alerts CSP/IDS | CSP nonce + Trusted Types + CSRF | A77 | `web_cwv_regression_watch` |
| BCDR falho | Drill atrasado | Tabletop + runbook | A91–A92 | `bcdr_test_freshness_watch` |
| SLO estourado | p95/p99 ↑ | Circuit breakers + rate limit | A71–A72 | `slo_budget_breach_watch` |
| MRM incompleto | Gate bloqueado | Docs e aprovações | A90 | `metrics_decision_hook_gap_watch` |

---


# 12) OKRs de Produto (ligados a hooks)
- **KR1**: ≥95% decisões com trilha/auditoria → se <95%, **abrir ação** e **bloquear release** (A110).  
- **KR2**: CDC p95 ≤ 120s → se >120s, **degrade** + ticket.  
- **KR3**: Drift dentro de faixa → se > limiar, **rollback**.  
- **KR4**: SRM OK → se falho, **pausa** e **instrumentação**.

---

# 13) Registro de Decisões (ADR) & Waivers (A106)
## 13.1 ADR (modelo)
```
ID • Data • Contexto • Opções • Trade‑offs • Decisão • Impactos • Packs citados • Owners
```
## 13.2 Waiver (modelo)
```
ID • Dataset/Contrato • Mudança • Justificativa • Prazo • Risco • Rollback • Aprovação
```

---

# 13) Como usar este Brief com o Agente P.O.
1) Gere o **Product Catalog** (Seção 2) com packs citados.  
2) Derive o **Feature Catalog** com ACE+hooks (Seção 7).  
3) Monte o **Roadmap & Gates** (Seção 10).  
4) Dele **Backlog** PO‑ready (histórias com telemetria).  
5) Forme a **equipe de agentes** por épico (matriz papéis→packs).  
6) Planeje **Sprints** e aprove com o checklist de watchers.

---

# 14) Apêndices
## 14.1 Mapeamento de Requisitos → Packs
- **Dados**: A105, A88, A106, A87, A86, A89.  
- **Decisão & Modelos**: A110, A81, A84, A83.  
- **Mercado**: A10, A28, A98–A100, A104, A103, A102.  
- **Gov/Resiliência**: A90–A93, A109, A91–A92.  
- **FE/Sec**: A74–A80, A77.

## 14.2 Glossário
- **Hook (A110)**: mapeamento métrica→ação automático.  
- **PSI/KS (A84)**: métricas de drift.  
- **TWAP (A104)**: *time‑weighted average price*.  
- **CDC (A105/A88)**: captura de dados de mudança.  
- **dbt (A89)**: transformação declarativa.  
- **MRM (A90)**: gestão de risco de modelo.  
- **BCDR (A91–A92)**: continuidade/recuperação.  
- **SRM (A83)**: *sample ratio mismatch*.


---

# 15) Segurança & Privacidade de Dados (A108)
- **Minimização**: somente dados necessários ao propósito declarado.  
- **Governança**: classificação de dados e retenção por domínio; *audit trail*.  
- **Consentimento/Legitimidade**: registrar base legal por fluxo; *data mapping* por contrato (A106).  
- **Direitos do titular**: processos para acesso/retificação/eliminação.  
- **Controles técnicos**: encriptação em trânsito/repouso; segregação; *key rotation*; *secrets* geridos; mascaramento em ambientes não‑prod.  
- **Hooks**: `dp_budget_breach_watch` (quando aplicável).  

---

# 16) Estratégia de Testes & Validação
- **Dados**: dbt tests (unique/not_null/accepted_values/relationships), expectations, *freshness*.  
- **Serviços**: unit/integration/contract tests; *golden tests* para APIs críticas.  
- **Modelos**: validação offline, *shadow*, *canary*, A/B com SRM.  
- **Resiliência**: *chaos drills* (A91–A92), tabletop.  
- **Performance**: *load tests* por serviço com metas SLO.  
- **Evidência**: dashboards por fase + anexos de logs/traces.

---

# 17) Runbooks (índice)
- **RB‑ORC‑001**: staleness > 30s → TWAP + failover  
- **RB‑ML‑002**: PSI>0.2 → rollback + retrain  
- **RB‑CDC‑003**: lag>120s → degrade + compaction  
- **RB‑AB‑004**: SRM → pausar e auditar  
- **RB‑FE‑005**: INP alto → rollback + otimizações  
- **RB‑DBT‑006**: tests falhando → corrigir/reativar CI

---

# 18) Versionamento & Controle de Mudanças
- **ADRs**: toda decisão registrada (Seção 13).  
- **Waivers**: prazo/risco/rollback obrigatório (A106).  
- **SemVer** para artefatos (vMAJOR.MINOR.PATCH).  
- **Changelog** mantido por release.  

---

# 19) Índice de Packs Referenciados
A10, A28, A41–A43, A71–A72, A74–A80, A77, A81–A84, A86–A89, A90–A93, A94–A97, A98–A100, A101–A104, A105, A106, A107, A108, A109, A110.


---

# 20) Measurement Plan & KPI Dictionary (ligado a A110)
> Como medir cada KPI, de onde vem o dado, qual janela, e qual ação dispara.

| KPI | Fonte de verdade | Amostragem/Janela | Cálculo/Obs. | Hook (A110) | Owner |
|---|---|---|---|---|---|
| Time‑to‑Preço‑Válido | traces OTel (A71–A72) • span: `decision.core` | contínua • janelas 5m/24h | p75/p95 por rota | `latency>0.8s•5m•degrade` | SRE/PO |
| CDC lag p95 | `cdc_offsets` (A105/A88) | 1m • janela 15m | lag por origem | `lag>120s•5m•degrade` | DC/PY |
| Drift PSI/KS | métricas de monit. (A84) | 1h • janela 24h | PSI/KS por feature/model | `psi>0.2•24h•rollback` | ML |
| Staleness oráculos | `oracle_ticks` (A104) | 10s • janela 5m | `now()-tick.ts` | `>30s•5m•TWAP` | BC |
| SRM A/B | logs de experimento (A83) | por execução | χ² de alocação | `srm_fail•run•pause` | ST |
| INP (CWV) | RUM/FE (A74–A80) | contínua • janela 24h | p75 por página | `inp>200ms•24h•rollback` | FE |

---

# 21) Governance Gates (estendidos)
**Pré‑merge**: contratos (A106) ok; tests dbt ok (A89); hooks definidos (A110).  
**Pré‑deploy**: *dry‑run* de hooks; *shadow/canary* (A83/A84); dashboards prontos.  
**Pós‑deploy (24h)**: watchers verdes; sem regressão de SLO; ADR/Changelog publicado.  
**Exceções**: apenas via **waiver (A106)** com prazo/rollback.

---

# 22) Telemetry & Tracing Spec (OTel mínimo)
- **Spans essenciais**: `decision.core`, `auction.match`, `fx.router`, `oracle.fetch`, `cdc.reader`, `dbt.run`, `ml.infer`.  
- **Atributos padrão**: `trace_id`, `pack_id`, `dataset`, `model_version`, `hook_id`, `watcher`, `latency_ms`, `status`.  
- **Eventos**: `hook.trigger`, `rollback.apply`, `waiver.start/stop`, `slo.violation`.  
- **Logs**: correlacionados por `trace_id` e `audit_id`.

---

# 23) Data Lineage & DQ Controls Matrix
| Dataset | Origem | Transform | Expect/Tests | Watchers | Packs |
|---|---|---|---|---|---|
| pricing_events | app → CDC | dbt marts | not_null/range/accepted_values | `data_contract_break_watch`, `dbt_test_failure_watch` | A106/A87/A89 |
| oracle_ticks | providers → gateway | normalize | freshness/staleness | `formal_verification_gate_watch` | A104/A103 |
| fx_quotes | LPs/venues | enrich | range/relationships | `slo_budget_breach_watch` | A98–A100 |
| cdc_offsets | Debezium | n/a | monotonic/heartbeat | `cdc_lag_watch` | A105/A88 |

---

# 24) Change Management Flows
- **Schema Change (A106)**: proposta → CI compat → revisão → deploy controlado → docs/waiver (se precisar).  
- **Model Change (A84)**: validação offline → shadow → canary → full; hooks de rollback prontos.  
- **Experiment Launch (A83)**: check SRM → plano de métrica → janela mínima → relatório final.  
- **Data Source Onboarding**: contrato + expectativas + lineage + watchers configurados.

---

# 25) Working Agreements (Squad de Agentes)
- **WIP máx**: 7 histórias • por papel: 2 em paralelo.  
- **SLA de resposta**: alertas críticos ≤ 15 min; *waivers* ≤ 24 h.  
- **Handoffs**: DoR/DoD por papel; demo em toda história.  
- **Reuniões**: daily 15’; planning/weekly 45’; review/retro no fim do sprint.

---

# 26) Audit Pack (Evidências obrigatórias)
- **Para cada release**: prints de dashboards, logs de hooks, lista de watchers e status, ADRs, *schema diffs*, *dbt run results*, *canary report*.  
- **Retenção**: por release/por trimestre.

---

# 27) Release & Rollback Patterns
- **Canary** por % tráfego → *auto‑rollback* em limiar de erro/latência.  
- **Blue/Green** com *switch back* assistido por hook.  
- **Feature flags** para FE/serviços com toggle seguro.

---

# 28) FAQ & Pitfalls
- **“Posso liberar sem watcher?”** Não. Defina hook e watcher antes.  
- **“Schema mudou e quebrou dbt”**: rollback e abrir waiver (A106).  
- **“SRM falhou”**: pause, instrumente, reinicie.  
- **“Drift alto mas métricas ok”**: faça *holdout*, confirme com KS/PSI por segmento.

---

# 29) Mini‑Checklists (cola rápida)
- **Feature**: ACE G/W/T • Hook A110 • Riscos/controles • Packs • Telemetria.  
- **História**: ACE/hook/watchers • tasks ≥2 • demo • evidência.  
- **Sprint**: capacidade ok • gates definidos • demo por história • postmortems zerados.


---

# 30) Latency Budget & Capacity Model
> Divisão do *budget* de latência por camada e dimensionamento de capacidade.

## 30.1 Orçamento de latência (p95)
| Camada | Meta p95 | Observações |
|---|---:|---|
| FE/Edge (RUM→Gateway) | 60 ms | CDN quente; TLS modern; keep-alive |
| Decision API (ingress→handler) | 80 ms | leitura leve de cache/params |
| Feature Fetch/Enrichment | 120 ms | só síncrono se indispensável |
| Model Serving (A81) | 180 ms | Triton com dynamic batching + concurrency |
| Oracles/FX reads | 140 ms | preferir dados *quentes* e TWAP |
| Persistência/Auditoria | 60 ms | *write-ahead* + fila assíncrona |
| **Total** | **≤ 640 ms** | sobra p/ jitter/rede até **0.8 s** p95 |

## 30.2 Capacidade e *headroom*
- **QPS alvo** por rota; **concurrency** por *pod*; **utilização** (60–70%) para absorver picos.  
- **Lei de Little** + **percentil alvo** para filas: dimensionar concorrência tal que `ρ < 0.7`.  
- **Triton**: `dynamic_batching{max_queue_delay_microseconds}` + perf curves para achar “joelho” (A81).  
- **Headroom**: ≥ 30% para serviços críticos (SRE).

---

# 31) Cost & Resource Model (Cloud/GPU)
| Recurso | Driver de custo | Alavanca de redução |
|---|---|---|
| GPU para serving | QPS, *batch size*, *precision* | FP16/INT8; *autoscale* por latência |
| Egress/Ingress | volume de eventos/quotes | compressão, TTL, *coalescing* |
| CDC infra | *throughput*, slots | *compaction*, *heartbeat*, *checkpoint* |
| Storage Lakehouse | snapshots/time-travel | retenção orientada a auditoria |

**Fórmula simples**: `custo_mensal ≈ (GPU_horas×$) + (VM_horas×$) + (GB_egr×$) + (GB_stg×$)` com *mix* por fase do roadmap. 

---

# 32) Threat Model (STRIDE) & Controles (A77/A103/A108)
| Ameaça | Vetor | Controle | Packs |
|---|---|---|---|
| Spoofing (oráculos) | fonte forjada | BLS/EdDSA + *pinning*/allowlist | A102/A104 |
| Tampering (schemas) | alteração de payload | contratos + CI compat | A106/A87 |
| Repudiation | falta de trilha | *audit trail* + `audit_id` | A90/A93 |
| Info Disclosure | logs sensíveis | *redaction* + *masking* | A108 |
| DoS (FE/API) | pico tráfego | rate-limit + *circuit breaker* | A71–A72 |
| Elevation | chaves/roles | KMS/HSM + *least privilege* | A102/A108 |

---

# 33) Especificações Formais (amostra de invariantes) — A103
```
Invariant ORACLE_FALLBACK:
  if staleness(now, last_tick) > 30s then price_used == TWAP(5m)
Invariant CONTRACT_BACKWARD_COMPAT:
  for all consumers vN: parse(schema_vN, payload_vN+1) succeeds
Invariant AUCTION_CLEARING:
  allocated <= supply && price == min{rate | cumulative(capacity) >= demand}
```

---

# 34) Experiment Design & Power — A83
- **Objetivo**: detectar Δ mínimo relevante `δ` com poder 80% e α=5%.  
- **Tamanho de amostra (aprox.)**: `n_arm ≈ 16·σ²/δ²` (proporções → use *pooled*).  
- **Checklist**: SRM ok; *bucketing* estável; janela mínima; *peeking* controlado; métricas guardrails.

---

# 35) SLOs & Error Budgets
| Serviço | SLO | Orçamento de erro/mês |
|---|---|---|
| Decision Core | 99.9% | ~43m 49s |
| Oracles | 99.95% | ~21m 54s |
| FE/Portais | 99.9% | ~43m 49s |
**Política**: ao consumir >50% do orçamento, **congelar lançamentos** do serviço e priorizar confiabilidade.

---

# 36) Data Governance Playbook — A87/A106/A108
1) **Classificar** datasets e mapear base legal.  
2) **Contratar** (A106) com expectations (A87) e CI.  
3) **Monitorar** freshness/qualidade → watchers.  
4) **Auditar** trimestralmente contratos/waivers.  
5) **Desligar** fontes sem dono/sem contrato.

---

# 37) Incident Response Matrix (watcher→runbook)
| Watcher | Severidade | Runbook | SLA resposta |
|---|---|---|---|
| `data_contract_break_watch` | Crítica | RB‑DBT‑006 | ≤ 15 min |
| `cdc_lag_watch` | Alta | RB‑CDC‑003 | ≤ 15 min |
| `model_drift_watch` | Alta | RB‑ML‑002 | ≤ 30 min |
| `formal_verification_gate_watch` | Crítica | RB‑ORC‑001 | imediato |
| `web_cwv_regression_watch` | Média | RB‑FE‑005 | ≤ 24 h |

---

# 38) Catálogo de Serviços & APIs (detalhado)
**decision.core** — POST `/decision`  
Campos obrigatórios; *idempotency-key*; cabeçalho `x-pack-id`.  
**oracle.gateway** — GET `/price?pair=USD/BRL` + `/twap`  
**fx.router** — POST `/quote` + parâmetros de rota/LP.

---

# 39) Backlog Taxonomy & Prioridade
- **Níveis**: épico → *feature set* → história → task.  
- **Prioridade**: `impacto×(1-risco) / esforço`.  
- **Bloqueio**: história sem ACE/hook/watchers → **não planeja**.

---

# 40) Biblioteca Estendida de Hooks (A110)
- **Erro 5xx API** • `rate>1%•15m•rollback_release`  
- **p95>target** • `>0.8s•5m•scale_out+throttle`  
- **Fill<90% leilão** • `2h•ajustar_params+review_lp`  
- **Spread FX↑** • `run•reforçar_filtros+limites`  
- **OKR gap** • `run•repriorizar_backlog`.

---

# 41) Multi‑Região & BCDR (A91–A92)
- **Topo**: *active/standby*; replicação CDC; *health checks* síncronos.  
- **Failover**: *DNS cutover* + *warm caches* + *readiness gates*.  
- **Reversão**: *post‑mortem* + *data reconciliation* + *drain* controlado.

---

# 42) Observability Dashboards (spec)
- **Latency & Error** por rota; **Hook Coverage**; **CDC Lag**; **Drift PSI/KS**; **CWV**; **SLO burn rate**.  
- **Drill‑downs** por `trace_id`, `pack_id`, `hook_id`.

---

# 43) Aceite & Demo Scripts (templates)
- **Roteiro**: objetivo → casos de teste → dados → passos → evidências (prints/links) → critérios de aceite.  
- **Resultado**: aprovado/reprovado + próximos passos.

---

# 44) Golden Notebooks (índice sugerido)
- **GN‑FX‑001**: delta conventions/VPIN  
- **GN‑ORC‑002**: TWAP/heartbeats/deviation  
- **GN‑ML‑003**: PSI/KS e *retraining*

---

# 45) Integration Test Harness
- **Contrato**: Gherkin (Given/When/Then) + datasets sintéticos.  
- **Critério**: 100% das histórias com pelo menos 1 cenário executável.

---

# 46) DPIA / PIA (A108) — Template
- **Escopo, Dados, Base legal, Riscos, Medidas, Residual, Aprovação**.  
- **Integração**: anexar ao ADR quando decisão toca dados pessoais.

---

# 47) Estratégia de Migração (LOE)
- **Fases**: *lift‑and‑shift* mínimo → hardening → otimização.  
- **Cutover**: *canary* + *feature flags* + *fallbacks*.

---

# 48) Tuning de Serving (A81/A84)
- **Batch**: aumentar até joelho da curva sem violar p95.  
- **Concurrency**: múltiplas filas por modelo.  
- **Precisions**: FP16/INT8 com validação de acurácia.  
- **Warmup**: ativar perfis por rota.

---

# 49) Exemplos de ADR & Waiver (preenchidos)
**ADR‑001**: Escolha de TWAP 5m — opções (EMA/TWAP) — decisão: TWAP por robustez a picos — Packs: A104/A103 — Owners: BC/PO.  
**Waiver‑DC‑017**: renomear `price_bps` → `rate_bps` — prazo 14d — rollback pronto — A106.


---

# 50) Smart Contracts & On‑Chain Integration (A101–A104)
> Camada opcional, **pilotável**. Objetivo: reforçar integridade, auditoria e automação de funding/hedge. Sempre com **A103 (formal)** em pontos críticos e **A108 (proteção de dados)**.

## 50.1 Casos de uso (prioridade)
1) **Attestation de preços e decisões**: gravar **hash** (Merkle root) de *oracle ticks* e de **audits** de decisão (sem PII; A108).  
2) **Escrow de Funding & Clearing** (P2): contrato segura compromissos e liquida alocações do **leilão reverso** com regras públicas.  
3) **Settlement de Hedge** (P3): registrar execuções de hedge (resumo) e referências de preço (A104).  
4) **Governança técnica**: *feature flags* on‑chain para pausas de emergência (pausable/circuit‑breaker) — acionadas por **hooks A110**.

## 50.2 Padrões de design
- **Separação função/dados** • **Events-first** para auditabilidade • **Checks‑effects‑interactions** • *Time‑locks* e *nonces* contra replay • *Rate‑limit* por rota.  
- **Oráculos (A104)**: *pull* (contrato consulta) ou *push* (attesters). TWAP/heartbeats/deviation implementados **off‑chain**, com só **provas/raiz** on‑chain.  
- **Formais (A103)**: invariantes em seções 33/54.

## 50.3 Interface (pseudo‑ABI) — Attestation de Preços
```solidity
interface PriceAttestor {
  event PriceStamped(bytes32 feedId, uint256 price, uint64 ts, bytes20 auditId);
  function submit(bytes32 feedId, uint256 price, uint64 ts, bytes calldata sig, bytes20 auditId) external;
}
```
**Invariantes**: (i) `ts` monotônico por `feedId`; (ii) `abs(price_t - TWAP_5m) <= maxDeviation` salvo `circuit_break`; (iii) assinatura válida (A102).

## 50.4 Interface — Escrow de Funding (leilão reverso)
```solidity
interface ReverseAuctionEscrow {
  event BidCommitted(bytes32 lp, bytes32 commitment, uint64 round);
  event BidRevealed(bytes32 lp, uint256 rateBps, uint256 capacity, uint64 round);
  event Cleared(uint64 round, uint256 clearingRateBps);
  function commit(bytes32 round, bytes32 commitment) external; // commit = H(rate,cap,nonce)
  function reveal(bytes32 round, uint256 rateBps, uint256 capacity, bytes32 nonce) external;
  function settle(uint64 round) external; // executa clearing e distribui alocação
}
```
**Anti‑front‑running**: **commit‑reveal** + *reveal window* + *slashing* se não revelar. **Fairness**: *tie‑break* por compromisso mais antigo.

## 50.5 Watchers & Hooks (on‑chain)
- `formal_verification_gate_watch` (A103) — bloquear *deploy* sem provas mínimas.  
- `metrics_decision_hook_gap_watch` — pausa de emergência em *feature flag*.  
- `api_breaking_change_watch` — sem mudanças na ABI sem *bump*/ADR.

---

# 51) Tokenização de Ativos & Exposições (A101–A104/A108)
> **Opcional (piloto)** e sujeito a avaliação regulatória. Objetivo: melhorar **liquidez**, **transparência** e **auditoria** de exposições de crédito/funding.

## 51.1 Padrões de representação
- **Fungível (pool/tranche)**: *shares* que representam frações de um pool de funding.  
- **Não‑fungível (claim)**: *tokens unitários* que representam contratos específicos (ex.: decisão ou parcela securitizada).  
- **Metadados**: **hash** de contrato de dados (A106), `audit_id`, `quality`, *jurisdição*. **Sem PII** (A108).

## 51.2 Ciclo de vida (estado)
`Minted → Locked (escrow) → Settled (clearing) → Redeemed → Default/Workout`  
**Regras**: *whitelist* de participantes (A108), *cap tables*, *freeze* por incidentes (hook A110), *events* para trilha.

## 51.3 Precificação & Oráculos
- **Preço primário** por clearing (P2).  
- **Marcação** por curvas/riscos (QU) e **FX** (P3) → **attestation** de preços/FX (50.3) com TWAP/heartbeats (A104).  
- **Hooks**: `spread>limiar` → revisão de parâmetros/roteamento.

## 51.4 Controles
- **Jurídico/Regulatório**: *whitelists*, limites, KYC/KYB (representados por *flags* e não por dados sensíveis).  
- **Privacidade (A108)**: *data minimization*, mascaramento em *events*; `audit_id` como chave de correlação.

---

# 52) Mercados de Previsão (Prediction Markets) — Sinais & Incentivos
> **Opcional/piloto**. Não substitui modelos/quorum de risco; **agrega sinal** de participantes qualificados. Sempre com **A104** para referências de preço e **A83** para avaliação causal.

## 52.1 Objetivo
Extrair **probabilidades implícitas** (ex.: default, *spread widening*, falha de oráculo) para **stress tests** e *early warnings*.

## 52.2 Mecanismos
- **Apostas em eventos binários/escalares** (ex.: “PSI>0.2 amanhã?”).  
- **Score de previsão** com regras próprias (ex.: *log score*).  
- **Colaterais & limites** para evitar manipulação; *cooldown* e *position limits*.

## 52.3 Integração com o CE
- **Sinais → hooks**: limiares de variação de probabilidade disparam análises (não ações diretas).  
- **Experimentos (A83)**: testar utilidade do sinal vs *baselines* com SRM OK.  
- **Auditoria**: `audit_id` e *events* de mercado de previsão separados de dados de clientes.

## 52.4 Watchers
- `formal_verification_gate_watch` (se houver contrato), `metrics_decision_hook_gap_watch` (limites de ação), `okr_risk_alignment_watch` (não desviar de KRs).

---

# 53) Leilões Reversos — Protocolo & Clearing (A10/A28)
## 53.1 Fluxo canônico
1) **Anúncio** de demanda e limites.  
2) **Commit** de lances (hash).  
3) **Reveal** dos lances (janela definida).  
4) **Clearing**: ordenar por taxa ascendente, **acumular capacidade** até demanda; taxa de **clearing = menor taxa** que cobre demanda.  
5) **Settlement**: registrar alocações (on‑chain opcional) e eventos de auditoria.

## 53.2 Algoritmo de clearing (pseudo)
```text
sort(bids, by=rate)
alloc=0; clearing=NA
for b in bids:
  take = min(b.capacity, demand-alloc)
  alloc += take
  if alloc >= demand and clearing==NA:
     clearing = b.rate
return clearing, allocations
```

## 53.3 Edge cases & fairness
- **Empate de taxa** → *tie‑break* por tempo de commit; 
- **Não‑revelou** → *slash* e bloquear próximo round;  
- **LP dominante** → *cap* por participante;  
- **Anti‑sniping** → janelas fixas;  
- **Transparência**: *events* por fase.

## 53.4 Observabilidade
- **Métricas**: *fill ratio*, tempo de clearing, *spread* vs mercado.  
- **Watchers**: `slo_budget_breach_watch`, `api_breaking_change_watch` (versão de regras), `formal_verification_gate_watch` (se ON‑chain).

---

# 54) Verificação, Provas & Testes (A103)
## 54.1 Invariantes (amostra)
- **ORACLE_FALLBACK**: se `staleness>30s` então `price_used==TWAP(5m)`.  
- **CONTRACT_BACKWARD_COMPAT**: consumidor `vN` consegue processar `payload vN+1`.  
- **AUCTION_CLEARING**: `allocated <= supply` e `clearing==min taxa que cobre demanda`.

## 54.2 Property‑based Testing (pseudocode)
```python
@given(bids=strategy_of_bids())
def test_clearing(bids):
    clearing, allocs = clear(bids)
    assert sum(allocs) <= demand
    assert clearing == min_rate_that_covers(demand, bids)
```

## 54.3 Gates de release
- `formal_verification_gate_watch=ok` nos contratos críticos;  
- *Test harness* verde (histórias com cenários executáveis, seção 45);  
- ADR publicado (seção 49) com trade‑offs e owners.

---

# 55) Compliance & Operação (on/off‑chain)
- **Dados pessoais** ficam **off‑chain**; on‑chain registra **hashes/audits** (A108).  
- **Waivers (A106)** para mudanças de schema; *time‑box* e rollback.  
- **Segurança**: chaves (A102), `least privilege`, *key rotation*; *pausable* para incidentes.  
- **Observabilidade**: correlacionar `audit_id`/`trace_id` com `tx_hash`.


---

# 56) Notação, Unidades e Convenções (Revisão Knuth)
- Símbolos: PSI (Population Stability Index), KS (Kolmogorov–Smirnov), Delta_s (limite de staleness), tau_TWAP (janela TWAP), p95 (percentil 95).
- Unidades: latência em ms; staleness em s; taxas em bps; volumes em R$; lag CDC em s.
- Tempo: timestamps ISO‑8601 em UTC; timezone de exibição America/Bahia.
- IDs canônicos: audit_id (auditoria), trace_id (OTel), pack_id (KB), hook_id (A110), tx_hash (on‑chain).
- Arredondamento: persistência usa round half‑even.

---

# 57) Definições Algorítmicas (Revisão Knuth)
## 57.1 TWAP e deviation
```
TWAP_tau(t) = média (ponderada no tempo) do preço numa janela de tamanho tau que termina em t.
Regra de fallback: usar TWAP_5m se staleness(t) > 30s OU |price(t) - TWAP_5m(t)| > d_max.
```

## 57.2 VPIN (sinal de toxicity simplificado)
```
VPIN = média, por janelas de volume equivalente, do desbalanceamento |Vb - Vs| / (Vb + Vs).
Routers evitam rotas com VPIN acima do limiar theta.
```

## 57.3 Clearing do Leilão Reverso
Ordene lances por taxa ascendente; acumule capacidade até a demanda; a taxa de clearing é a menor taxa que cobre a demanda (ver §53.2). Empates: tie‑break determinístico por tempo de commit.

## 57.4 PSI e KS (resumo)
- PSI: soma, por bins fixos, de (p - q) * ln(p/q) com mass mínima.
- KS: maior distância entre CDFs empíricas das duas amostras.

---

# 58) Obrigações de Correção (Pré/Pós‑condições) — Knuth
- Decision Core:
  - Pré: contrato de dados válido (A106/A87), features definidas, modelo carregado.
  - Pós: latência p95 ≤ 800ms, audit trail persistido, hook coverage = 100% para KPIs críticos.
- Oracles:
  - Pré: fonte primária e backup ativos; tau_TWAP=5m configurado.
  - Pós: staleness<30s ou TWAP aplicado; logs assinados (A102).
- CDC:
  - Pré: replication slots, heartbeats e DLQ prontos.
  - Pós: lag p95≤120s; offsets monotônicos; expectations ok.

---

# 59) Reprodutibilidade & Ambiente (Revisão Pérez)
- Ambiente padrão: container ghcr.io/creditengine/ce:prod-<semver> (Python 3.11, Triton, dbt-core, OTel SDK, Debezium client).
- Seeds determinísticos: variável CE_RANDOM_SEED; hashes de datasets; time-freeze com fixtures.
- Dados: snapshots com time-travel (A86), versionados via contract_id.version (A106); sem PII (A108).
- Makefile (pseudocode):
```
make data.snap   # baixa snapshot + valida expectations
make dbt.run     # models + tests
make serve.test  # inicia serviços em modo canário
make hooks.dry   # executa hooks A110 em dry-run
make nb.all      # executa Golden Notebooks (ver §60)
```
- Artefatos: salvar em artifacts/<release>/ com manifesto (sha256) e links para trace_id/audit_id.

---

# 60) Golden Notebooks — Especificação Executável (Pérez)
| Notebook   | Objetivo                             | Entradas           | Saídas/Evidências                              |
|------------|--------------------------------------|--------------------|-----------------------------------------------|
| GN‑FX‑001  | Validar delta conventions/VPIN       | fx_quotes (§23)    | gráficos de delta; VPIN por janela; report.html |
| GN‑ORC‑002 | Validar TWAP/heartbeats/deviation    | oracle_ticks       | staleness e fallback; twap_validation.json     |
| GN‑ML‑003  | Drift PSI/KS                         | amostras prod vs ref | psi.csv, ks.json, recomendação de rollback   |

Execução: `make nb.all` gera artefatos com timestamp/commit e anexa ao Audit Pack (§26).

---

# 61) Harness de Teste Executável (Pérez)
- Estrutura: tests/e2e/ com cenários Gherkin (Given/When/Then) e fixtures versionadas.
- Comando: `pytest -m e2e --maxfail=1 -q`.
- Critério: 100% das histórias planejadas têm pelo menos um cenário executável e evidência no Audit Pack.

---

# 62) Proveniência & Fingerprinting de Dados
- Merkle root por batch de pricing_events e oracle_ticks; raiz anexada em attestations on‑chain (§50).
- Carimbo de tempo confiável (RFC 3161) opcional; correlacionar com audit_id.

---

# 63) Traceability Bridge: OTel ↔ Dados ↔ Notebooks
- Do trace para dado: trace_id → audit_id → partições de pricing_events.
- Do dado para notebook: contract_id.version → runner do GN (FX/ORC/ML).
- Dos notebooks para gates: sucesso dos GNs é pré‑requisito de Go/No‑Go.

---

# 64) Quality Gates (Extensão Knuth + Pérez)
- Literate: toda seção técnica referencia packs e define pré/pós‑condições.
- Executable: hooks dry‑run, harness e2e, golden notebooks executados; evidências arquivadas (§26).
- Bloqueio: ausência de qualquer evidência → No‑Go.

---

# 65) Log da Auditoria Knuth + Pérez
- Notação/unidades validadas (latência ms, staleness s, bps).
- Definições formais acrescidas (TWAP, VPIN, clearing) e fórmulas PSI/KS.
- Reprodutibilidade especificada (container, seeds, snapshots, make targets).
- Ponte OTel↔Dados↔Notebooks↔Gates verificada.
- Status: APTA para entrega; sem pendências conhecidas.


---

# 66) Visão de Produto — Narrativa Estendida
> **O que é o CE, para quem é, por que existe e como transforma o dia a dia.**

**Proposta central**: o **CreditEngine$ (CE)** é o *sistema nervoso de decisão de crédito* que conecta dados confiáveis (CDC+Contracts), mercado (oráculos/FX), modelos (serving/monitoring) e governança (MRM/BCDR/Postmortem), com **decisões auditáveis** em **latência sub‑segundo**. A chave é **acoplar métricas→ações (A110)** e contratos de fronteira (A106/A87) em todo lugar.

**Para quem**: times de **originação, risco, tesouraria, operações e produto**.  
**Resultados**: aprovações mais rápidas, custo de funding otimizado, risco operacional reduzido, *paper trail* perfeito para auditorias.

**Como entrega valor (4 alavancas)**  
1) **Velocidade com confiança** — SLOs claros, observabilidade (A71–A72) e hooks (A110).  
2) **Dados de qualidade** — CDC (A105/A88), contratos/testes (A106/A87/A89).  
3) **Mercado e preços robustos** — Oráculos TWAP/heartbeats (A104), FX routing (A98–A100).  
4) **Resiliência e governança** — MRM/Postmortem/BCDR/OKRs (A90–A93/A109).

**Transformação do fluxo**  
Entrada (eventos transacionais) → **CDC** → **Lakehouse** → **dbt** → **Decision Core** → (opcional) **Auctions/FX/Hedge** → Persistência de **audit trail** → Telemetria e **hooks**.

---

# 67) Casos de Uso & Fluxos (detalhados)
1) **Originação instantânea**: pedido → features → decisão/taxa (≤0.8s p95) → justificativa (A90) → auditoria (A93).  
2) **Funding diário**: lotes de demanda → **leilão reverso** (A10/A28) → clearing/settlement.  
3) **Hedge FX**: exposição detectada → cotações/rotas (A98–A100) → execução → attestation (opcional, §50).  
4) **SecOps**: *schema drift* ou quebra de contrato (A106/A87) → rollback/waiver controlado.  
5) **ML Ops**: drift PSI/KS (A84) → rollback/retrain/experimento (A83) com **hook** (A110).  
6) **BCDR**: simulação de perda de região (A91–A92) → failover e retorno controlado.

Cada fluxo referencia **packs**, define **watchers** e tem **runbook**.

---

# 68) Mapa de Ideias & Apostas Adjacentes
- **Workbench de Simulação** (goldens §60) — *what‑if* de taxas/FX/lag CDC com hooks em *dry‑run* (A110).  
- **Catálogo de Modelos** com *rollbacks* e *policy routing* (A81/A84/A90).  
- **On‑chain Attestations & Escrow** (piloto) para integridade de funding/hedge (§50).  
- **Marketplace interno de dados** com contratos e *expectations* (A106/A87).  
- **Portais de decisão** (Next.js) com CWV verdes (A74–A80/A77).  
- **Prediction Signals** (mercado de previsões, §70) como **sinal auxiliar**.

---

# 69) Alavancas de Valor (KPIs → impacto)
- **Conversão** ↑ por decisões rápidas e claras (NSM; §0.2).  
- **Custo de funding** ↓ por alocações eficientes (P2).  
- **Perdas** ↓ por drift/ruído contidos (A84/A106).  
- **Opex** ↓ por automação de hooks/waivers e menos incidentes (A110/A93/A91).

---

# 70) Mercados de Previsão — *Blueprint* Operacional
> **Objetivo**: agregar sinais probabilísticos **externos ou internos qualificados** sobre eventos relevantes ao CE (ex.: *drift amanhã*, *lag CDC p95>120s hoje*, *spread FX alarga ≥X bps*). **Não substitui modelos**; funciona como **sinal auxiliar** para **experimentos/planos de contingência**.

## 70.1 Princípios de design
- **Observacional, não executivo**: sinais **não** disparam ações diretas; viram **hipóteses** testadas (A83) e **checkpoints** de planejamento.  
- **Incentivos corretos**: regras e pontuação que recompensam **calibração** (sem especificar fórmula no código-fonte do brief; detalhamento fica nos notebooks §60).  
- **Resolução clara**: cada mercado define **evento, janela, fonte e método de resolução** (ex.: `oracle_ticks`, `cdc_offsets`).  
- **Segurança e ética**: sem PII (A108), *whitelist* de participantes, *limits* e monitoramento de abuso.

## 70.2 Tipos de mercado suportados
- **Binário**: evento acontece/não (ex.: “PSI>0.2 em 24h?”).  
- **Escalar**: valor em faixa (ex.: “lag CDC p95 amanhã?”).  
- **Composto**: combinação de sinais (ex.: “staleness>30s **e** spread FX≥X?”).  
Cada contrato define **unidade**, **faixas**, **datas** e **fontes**.

## 70.3 Especificação de contrato (modelo)
```yaml
market_id: pm.drift.psi.24h.v1
question: "PSI do modelo M ultrapassa 0.2 nas próximas 24h?"
resolution:
  source: monitoring.ml (A84)
  method: janela_movel_24h
  criteria: PSI>0.2 por >=1 janela
participation:
  eligibility: whitelist
  limits: position<=X, cooldown>=Yh
outcomes: [yes, no]
telemetry:
  links: [trace_id, audit_id]
```

## 70.4 Integração com o CE
- **Dados**: mercados consomem fontes do próprio CE (`oracle_ticks`, `cdc_offsets`, `fx_quotes`).  
- **Sinais → análises**: shifts de probabilidade **criam histórias** (ex.: “planejar contingência para lag CDC”) e/ou **gatilhos de experimento** (A83).  
- **Watchers existentes**: `metrics_decision_hook_gap_watch` (garante mapeamento), `okr_risk_alignment_watch` (não desvia do plano), `formal_verification_gate_watch` (se on‑chain).  
- **Hooks A110** (modo insight): `prob_shift>θ•janela•abrir_análise+propor_experimento`.

## 70.5 Controles de abuso e manipulação
- **Governança**: *whitelists*, *position limits*, avaliação de anomalias.  
- **Auditoria**: logs vinculados a `audit_id`; registros off‑chain e, se aplicável, *hash* on‑chain (§50).  
- **Transparência**: documentação pública interna dos contratos (perguntas, critérios, fontes).

## 70.6 Métricas de qualidade do mercado
- **Calibração** das probabilidades vs eventos resolvidos (avaliada nos notebooks §60).  
- **Latência de resolução**: tempo entre fechamento e confirmação.  
- **Utilidade operacional**: % de hipóteses úteis que geram ação planejada (não automática).

## 70.7 Exemplos de contratos (prontos)
**PM‑CDC‑LAG‑24H**  
- **Pergunta**: “Lag CDC p95 excede 120s amanhã?”  
- **Resolução**: `cdc_offsets` (A105/A88) com janela 24h.  
- **Ação (insight)**: se prob sobe >θ, priorizar otimização de slots/compaction.

**PM‑ORC‑STALENESS‑TODAY**  
- **Pergunta**: “Staleness de oráculo >30s p95 na janela de hoje?”  
- **Resolução**: `oracle_ticks` (A104).  
- **Ação (insight)**: preparar *runbook* de failover e testar TWAP.

**PM‑FX‑SPREAD‑WIDEN**  
- **Pergunta**: “Spread FX alarga ≥ X bps na próxima sessão?”  
- **Resolução**: `fx_quotes` (A98–A100).  
- **Ação (insight)**: revisar filtros de *toxicity*.

## 70.8 Piloto em 2 sprints
- **Sprint 1**: definir 3 contratos (CDC/ORC/FX); dashboards; notebooks de avaliação (§60).  
- **Sprint 2**: exercício de *tabletop* com eventos simulados; medir calibração/utilidade; ADR.

---

# 71) Storytelling do Produto (Exemplos narrativos)
- **Antes**: decisões lentas, dados quebrando, sem trilha.  
- **Depois**: latência sub‑segundo, contratos de dados, oráculos robustos, decisões com justificativa e rollback automático; planejamento guiado por sinais (mercado de previsões) e **evidência executável** (goldens/harness).

---

# 72) Perguntas Frequentes de Produto
- **É só uma “regra” glorificada?** Não; é um *engine* com dados confiáveis, modelos servidos, **hooks** e **governança**.  
- **E se o mercado errar?** Ele é **sinal auxiliar**; decisões operacionais passam por **experimentos** e **gates**.  
- **Dá pra usar sem on‑chain?** Sim. On‑chain é **piloto opcional** (attestations/escrow), sempre com A103/A108.


---

# 73) Documento Mestre & ADRs Herdados (do CE$ MVP v6.0)
**Hierarquia**: prevalece a **Master KB** mais recente até ADR formal.  
**ADRs ativos**: **ADR‑001** (SLA default ≤6h notificação/execução) e **ADR‑002** (taxa mínima de serviço 0,50% no desembolso).  
**Convenções**: unidades em **bps/days/seconds**; valores **centavos (off‑chain)**/**wei (on‑chain)**; timestamps **UTC**; **APR** base 365 vs **CDI** 252; ordem de operações de arredondamento em §78.4.

---

# 74) CE$ Marketplace P2P — Descrição Integrada
**O que é**: marketplace P2P com **leilão reverso uniform‑price adaptado CE$**, **LoanVault** (liquidez até colateral) e liquidação via **CE$**. Objetivo: reduzir custo, ampliar acesso, padronizar risco.  
**Perfis**: Tomador PF/PJ; Credor PF/Institucional; Parceiros (score/bancos/antifraude); Comitê de Risco **consultivo** (Fase 0).  
**Jornada**: pedido → ofertas → média ponderada → aceite parcial/final → LoanVault liquida → (default) governança de credores (abandono/transferência >R$2k/renegociação/judicialização conjunta/venda secundária).  
**Escopo MVP**: leilão reverso, LoanVault, CE$, UX 3 telas + fallback; logs imutáveis (hash, JSON/KYC schema); integrações mínimas; Governança Fase 0.

---

# 75) Protocolo — Algoritmo Uniform‑Price Adaptado (CE$)
1. **Ordenar** por menor **APR**; **tie‑breakers**: (i) maior volume, (ii) timestamp mais antigo, (iii) hash do lance.  
2. **Aceitar** lances até 100% do pedido.  
3. **Oversubscription**: distribuir **pró‑rata por valor** na margem.  
4. **Taxa final** \(APR_{bps}\) = `Σ(amount_i_cent · apr_i_bps) / Σ(amount_i_cent)` (centavos).  
5. **Eventos** registrados com **hash**; **transparência**: publicar composição final + `apr_weighted_bps` + `hash_calc` no `LoanConfirmed`.

## 75.1 Anti‑manipulação (parâmetros)
- **Step mínimo**: **5 bps**; **máx. ofertas/credor**: **3**; **cooldown** cancelamento: **60s**.  
- **Anti‑sniping**: lances nos **últimos 120s** estendem +120s (máx. +600s).  
- **Taxa mínima**: ≥ **6% a.a.** (Fase 0).  
- **Sinais Sybil**: KYC/contas bancárias, correlação IP/dispositivo → **sinal** para *review* (comitê consultivo).

## 75.2 Validade & Reserva
- **TTL da oferta**: **24h** (expira silenciosamente).  
- **Reserva de capital**: somente em `LoanConfirmed`.  
- **OfferUpdated** preserva `offer_id` e aplica cooldown.

## 75.3 Fallback UX
- Estados `RequestOnHold`/`RequestFilled`/`RequestAutoCancelled`; **SLA ≤2h**; mensagens‑modelo no Apêndice §89‑F.  
- Capital **não trava**; ao retomar, **recalcular** pool e expirações.

## 75.4 Ordem de operações & Arredondamento
1) calcular **pró‑rata** em **centavos**; 2) fechar soma = valor do pedido (ajuste ±1 centavo na última linha); 3) calcular `apr_weighted_bps` **após** pró‑rata; 4) persistir `hash_calc` (ordem determinística); 5) conversão para **wei** somente no on‑chain.

---

# 76) Mercado Secundário
**Frações** negociáveis como "preço por R$1 de face"; passo mínimo **R$0,01** (off‑chain)/**1 wei** (on‑chain).  
Eventos: `DebtAuctionStarted`, `DebtTraded`, `DebtAuctionClosed`.  
**Invariantes**: soma das frações ≤ 100%; preço ≥ 0; logs com hash.

---

# 77) Máquina de Estados & Eventos (originação→liquidação)
`AuctionCreated` → (`OfferPlaced`|`OfferUpdated`|`OfferCancelled`)* → `RequestFilled`? → `LoanPartiallyFilled`? → `LoanConfirmed` → (`LoanPrepaid`|`LoanDefaulted`|`LoanClosed`)  
Fallback pode ocorrer em paralelo (`RequestOnHold`/`RequestAutoCancelled`).  
**Eventos extra**: `RepresentationEngaged` (judicialização conjunta).

---

# 78) Política de Pré‑pagamento (MVP‑safe)
**Permitida** a qualquer tempo; **sem multa**; juros **pro‑rata die** até liquidação.  
**Taxa de serviço (0,50%)** aplicada **uma única vez** no desembolso.  
Evento: `LoanPrepaid { principal_pago, juros_pro_rata, saldo }`.

---

# 79) Tokenomics (CE$)
**Colateral**: 130% cripto pequena; 105% cripto grande; 100% fiat (reavaliação: 24h cripto / 7d fiat).  
**Paridade 1:1** via oráculos (quorum 2/3); **mint** no funding; **burn** na liquidação/prepagamento; **sem rewards** no MVP.  
**Monitor de colateral** alerta < 102% do alvo (sem *margin call* no MVP).

---

# 80) Risco & Compliance (MVP)
**PF**: CPF/Receita/listas/PEP/conta vinculada. **PJ**: CNPJ/representante; reforço > R$50k.  
**Transações atípicas**: limiar inicial > R$50k/dia agregado (relacionados).  
**Cripto**: Chainalysis.  
**Logs KYC/AML**: JSON + hash; **retenção 5 anos**; RBAC; auditoria de leitura.

---

# 81) Métricas & OKRs (com CDI)
**APR anual** base 365; converter para **252** p/ comparar com **CDI**:  
`APR_252 = (1+APR)^(252/365) − 1` (aprox. simples para dashboard).  
**KPIs**: Funding ≤24h; Pool ≥65% antes do aceite; NPL30 ≤3%; Ativação D7 ≥40%; Retenção D30 ≥60%.  
**Qualidade do Leilão**: cancelamento <15% por credor/auction; % leilões com anti‑sniping <25%; **HHI** ≤ 0,35.

---

# 82) UX & Acessibilidade
**3 telas** (Pedido/Ofertas/Customização) + **fallback**; cálculo em tempo real e **aceite parcial**.  
**Mobile‑first**, EN/PT, ícones claros; foco visível, contraste AA, navegação por teclado, ARIA.

---

# 83) Segurança & Observabilidade (MVP)
Logs/eventos **JSON** com **SHA‑256** e **assinatura**; versionamento de schema (semver).  
Criptografia em trânsito (**TLS 1.3**) e em repouso (**AES‑256**).  
**RBAC**; auditoria de leitura KYC.  
Backups diários verificados; retenção ≥ 30 dias.  
Incidentes: SEV‑1 ≤1h; SEV‑2 ≤4h; SEV‑3 ≤24h.

---

# 84) Governança & Roadmap por Fases
**Fase 0**: centralizada; juros mínimo **6%**; comitê de risco **consultivo** (sem poder de decisão).  
**Fase 1**: tokenholders definem parâmetros.  
**Fase 2**: comitê tokenizado parcial.  
**Fase 3**: descentralizada.

---

# 85) Restrições MVP
SLA fallback ≤2h; SLA default ≤6h (ADR‑001); taxa mínima 0,50% (ADR‑002); sem incentivos; Governança Fase 0.

---

# 86) Exemplos & Simulações (numéricas)
**Taxa média ponderada**: 3k×10% + 5k×12% + 2k×14% ÷ 10k = **11,8% a.a.** (`hash_calc`).  
**Pró‑rata na margem**: pedido 10k; ofertas: 6k@10%, 3k@11%, 4k@12% → aceita 6k + 3k + **1k pró‑rata** do último; APR = média ponderada.  
**Ajustes de centavos**: distribuir centavos; corrigir ±1 na última linha; persistir composição final.

---

# 87) Schemas JSON (mínimos)
```json
{"AuctionEvent":{"id":"uuid","ts":"utc_iso","type":"string","payload_hash":"hex"}}
```
```json
{"Offer":{"offer_id":"uuid","auction_id":"uuid","lender_id":"uuid","amount_centavos":0,"apr_bps":0,"ts":"utc_iso","status":"PLACED|UPDATED|CANCELLED|EXPIRED"}}
```
```json
{"LoanConfirmed":{"auction_id":"uuid","composition":[{"offer_id":"uuid","amount_centavos":0,"apr_bps":0}],"apr_weighted_bps":0,"hash_calc":"hex"}}
```
```json
{"KYCLog":{"subject_id":"uuid","type":"PF|PJ","checks":["SERASA","PEP","SANCTIONS"],"result":"PASS|REVIEW|FAIL","reviewer":"id","ts":"utc_iso"}}
```

---

# 88) Mensagens‑Modelo (Fallback)
**Tomador**: “Seu pedido está em espera (até 2h) enquanto validamos integrações. Você não precisa agir agora.”  
**Credor**: “Seu capital **não foi travado**; confirmaremos ao final da validação do pedido.”  
**Auto‑cancel**: “Pedido cancelado sem custos. Você pode republicar a qualquer momento.”

---

# 89) Gate A — Critérios de Aceite (MVP)
- Algoritmo, anti‑manipulação, TTL e tie‑breakers **implementáveis** e descritos.  
- **Logs** e **schemas** publicados; hash/assinatura ativos.  
- **UX 3 telas** + fallback com mensagens‑modelo.  
- **KPIs** com fórmulas e bases (365/252) definidas.  
- **Taxa mínima 0,50%** aplicada e **capital só trava** em `LoanConfirmed`.  
- **Governança Fase 0** e hierarquia Master KB respeitadas.

---

# 90) ADRs Recomendados (a formalizar)
Oráculos & quorum (sug. 2/3); faixas cripto pequena/grande; step mínimo 5 bps; máx. ofertas=3; cooldown=60s; anti‑sniping=120s (+600s); retenção de logs (5 anos) e RBAC; limiar de transações atípicas; conversões APR↔252 fixadas no data‑layer.

---

# 91) Glossário (aditivo CE$)
CE$, LoanVault, NPL30 (>30 days), uniform‑price adaptado CE$ (média ponderada), APR (365), CDI (252), HHI, RequestOnHold/RequestAutoCancelled.

---

# 92) Amarrações com Packs & Watchers (cross‑walk)
- **A10/A28 (Leilões)** → `slo_budget_breach_watch`, `api_breaking_change_watch` (regras/versões).  
- **A98–A104 (FX/Oráculos)** → `formal_verification_gate_watch`, `oracle_divergence_watch`.  
- **A106/A87/A89 (Contratos/dbt)** → `data_contract_break_watch`, `schema_registry_drift_watch`, `dbt_test_failure_watch`.  
- **A110 (Hooks)** → `prob_shift>θ` (mercado de previsões modo insight).  
- **A108 (Privacidade)** → `dp_budget_breach_watch` (quando aplicável).

---

# 93) Status de Integração
**Merged** com o CE$ MVP v6.0 em **todas** as seções críticas (produto, protocolo, tokenomics, métricas, UX, segurança, governança, gate). Alinhado aos packs A1–A110 e às expansões §50–§72 deste brief. Sem placeholders.

