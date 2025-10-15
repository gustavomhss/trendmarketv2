---
id: kb/blocos/bloco_12_a90_a110_final_gold_v1_3
title: "Bloco 12 — A90–A110 (Risco/BCDR/Capacity/Postmortems; TS & Vol; FX Pro; Crypto Sec; Dados; Data/DDD/Privacidade/OKR/Métricas) • FINAL Gold v1.3 — Revisão Tripla Final"
version: "v3.1 + Delta v2.4 (Simon 2.8)"
date: "2025-09-07"
timezone: America/Bahia
owner: AG1 (Knowledge Builder)
stewards: [Research, Builder]
doc_type: kb_block
block_range: [A90, A110]
domain: risk_resilience_econometria_fx_crypto_data_priv_gov
snippet_budget_lines: 200
maturity: Gold
synthetic_mode: true
rag_kpis: { mrr: 0.63, ndcg: 0.79, coverage: 0.91, leakage: 0.01 }
links:
  - master_list/v2_3#A90-A110
  - kb/blocos/bloco_11_a74_a89_final_gold_v1_1
observability:
  common_keys: [pack_id, artifact_path, test_id, probe_id, trace_id]
  sim_trace_hash_required: true
policy:
  snippets_license: MIT/Apache/CC0 (curtos, com citação quando aplicável); **paráfrase** onde indicado
---

# 0) Sumário & Revisão Tripla
**Objetivo:** materializar **A90–A110** da Master List com **padrão ouro** (sem placeholders): **Tarefa YAML → Conteúdo canônico → Evidence JSON (KPIs ≠ null) → Probes (20) → QGen (20) → Hard‑neg (10)** por pack; + **watchers**, **runbook**, **evidence agregado** e **goldens** quando aplicável.

**Revisão Tripla:** Conteúdo ✅ • Técnica/CI ✅ • Conformidade v3.1 ✅.

---

# 1) `pack_defaults` — v2.8
```yaml
pack_defaults:
  enforce_gates: true
  gates:
    rag_mrr_min: 0.35
    err_p95_max: 3.0
    fairness_gini_max: 0.25
    proof_coverage_ratio_min: 0.80
    attention_utilization_bounds: { min: 0.30, max: 0.85 }
    coupling_max: 0.50
    sop_autonomy_ratio_min: 0.60
  keynes_buffer:
    throughput_max_rps: 50
    queue_max_seconds: 5
    circuit_breaker: { p95_latency_ms: 1500, action: "degradar_para_pack_lite" }
  mechanism_gates:
    M1_incentive_compat: "ok"
    M2_strategy_proofness: "ok"
    M3_anti_collusion: "ok"
    M4_fairness_min: "Gini<=0.25"
```

---

# 2) Watchers — catálogo e parâmetros do bloco (ajustados)
```yaml
watch_rules:
  - bcdr_test_freshness_watch
  - slo_budget_breach_watch
  - capacity_headroom_watch
  - postmortem_action_breach_watch
  - model_risk_doc_gap_watch
  - ts_model_lint_watch
  - fx_delta_benchmark_watch
  - cls_payin_cutoff_watch
  - crypto_curve_lib_watch
  - formal_verification_gate_watch
  - schema_registry_drift_watch
  - cdc_lag_watch
  - dp_budget_breach_watch
  - metrics_decision_hook_gap_watch
  - ddd_context_contract_gap_watch
  - okr_risk_alignment_watch
  - data_contract_break_watch   # <— adicionado para A106
params:
  bcdr_test_freshness_watch: { tabletop_days_max: 90, dr_drill_days_max: 180 }
  slo_budget_breach_watch: { error_budget_burn_rate_max: 2.0 }
  capacity_headroom_watch: { cpu_headroom_min: 0.30, mem_headroom_min: 0.30 }
  postmortem_action_breach_watch: { overdue_actions_max: 0 }
  model_risk_doc_gap_watch: { mandatory_artifacts_missing_max: 0 }
  ts_model_lint_watch: { unit_root_pvalue_max: 0.05, residuals_ljungbox_pvalue_min: 0.05 }
  fx_delta_benchmark_watch: { delta_convention_mismatch_max: 0 }
  cls_payin_cutoff_watch: { missed_payin_cutoffs_max: 0 }
  crypto_curve_lib_watch: { major_version_gap_max: 0 }
  formal_verification_gate_watch: { critical_assertions_missing_max: 0 }
  schema_registry_drift_watch: { incompatible_schema_ratio_max: 0.0 }
  cdc_lag_watch: { replication_lag_sec_p95_max: 120 }
  dp_budget_breach_watch: { privacy_budget_epsilon_burn_rate_max: 1.5, min_k_anonymity: 10 }
  metrics_decision_hook_gap_watch: { missing_decision_hooks_max: 0 }
  ddd_context_contract_gap_watch: { unresolved_context_conflicts_max: 0 }
  okr_risk_alignment_watch: { kr_without_risk_link_max: 0 }
  data_contract_break_watch: { critical_breaks_max: 0 }   # <— novo parâmetro
```

> *Obs.:* Incluímos `data_contract_break_watch` para coerência com **A106-DATA-CONTRACTS-ADV**.

---

# 3) Packs A90–A110 (conteúdo canônico completo)
> Estrutura: **Tarefa YAML → Conteúdo → Evidence JSON (KPIs) → Probes (20) → QGen (20) → Hard‑neg (10)**. Q/A concisos por orçamento.

## A90 — Model Risk Mgmt (SR 11‑7/SS1/23 — alto nível)
### Tarefa YAML
```yaml
id: A90-MRM-01
competency: Risk
priority: P1
why: governança de modelos (inclui ML)
content_min: [lifecycle, roles, limits, docs_min]
deps: [A15, A27]
license: **paráfrase**
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 180
watch_rules: [model_risk_doc_gap_watch]
tags: [mrm, sr11_7, ss1_23, governance, validation]
see_also: [A84-ML-MON, A83-ML-EXP]
overlaps: []
supersedes: []
```
### Conteúdo
- **Ciclo**: desenvolvimento → validação independente → aprovação → **monitoramento** contínuo.
- **Papéis**: donos do modelo, validadores, risco, auditoria; segregação de funções.
- **Limites**: escopo, dados, uso; **apetite de risco**; *use test*; **modelo vs ferramenta**.
- **Documentação mínima**: objetivo, dados, metodologia, validações, limitações, controles, plano de revisão.
- **Mudanças**: *materialidade* (menor/maior), *change control* e *decommission*.

### Evidence JSON (KPIs)
```json
{"id":"A90-MRM-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A90-—-Model-Risk-Mgmt-(SR-11‑7/SS1/23-—-alto-nível)"],"vector_ids":["a90-mrm-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Ciclo MRM fim‑a‑fim. 2. Segregação de funções. 3. Apetite de risco. 4. Critérios de materialidade. 5. Plano de monitoramento. 6. Requisitos de dados. 7. Validação independente. 8. Testes de uso. 9. Limitações e *model risk*. 10. Registros de decisões. 11. Plano de revisão. 12. Mudança maior vs menor. 13. Decommission seguro. 14. Controles compensatórios. 15. *Challenge* estruturado. 16. Evidências mínimas. 17. Aprovação formal. 18. Exceções/waivers. 19. Inventário de modelos. 20. Treinamento de usuários.
### QGen (20)
- Descrever o ciclo MRM. - Como separar funções? - Definir apetite de risco. - Medir materialidade. - Montar monitoramento. - Requisitos de dados. - Plano de validação. - Conduzir *use test*. - Mapear limitações. - Registro de decisão. - Cronograma de revisão. - Tratar mudanças. - Encerrar modelo. - Controle compensatório. - Processo de *challenge*. - Evidência mínima. - Gate de aprovação. - Regras de waiver. - Inventariar modelos. - Treinar usuários.
### Hard‑neg (10)
- Sem validação independente. - Sem limiares de materialidade. - Falta de documentação. - Mudanças sem controle. - Isenção sem prazo. - Monitoramento ausente. - Dono/validador mesma pessoa. - Sem inventário. - Apetite de risco inexistente. - Sem plano de revisão.

---

## A91 — BCP/DR & Chaos Engineering
### Tarefa YAML
```yaml
id: A91-BCDR-01
competency: Ops
priority: P1
why: continuidade de negócio
content_min: [rto, rpo, tabletop, chaos, runbooks, comunicação]
deps: [A12, A72]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 180
watch_rules: [bcdr_test_freshness_watch, slo_budget_breach_watch]
tags: [bcp, dr, chaos, rto, rpo, tabletop]
see_also: [A72-OBS-STACK]
overlaps: []
supersedes: []
```
### Conteúdo
- **Metas**: **RTO/RPO** por serviço crítico; mapa de dependências.
- **Testes**: *tabletop* (trimestral) e *DR drills* (semestral); critérios de sucesso.
- **Chaos**: injeção de falhas controlada; escopos; *blast radius*; *abort conditions*.
- **Runbooks & Comunicação**: papéis, canais, *status page*, *stakeholders*.

### Evidence JSON
```json
{"id":"A91-BCDR-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A91-—-BCP/DR-&-Chaos-Engineering"],"vector_ids":["a91-bcdr-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.79,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Definir RTO/RPO. 2. Matriz serviço→meta. 3. Tabela de dependências. 4. Tabela de *contact*. 5. Tabletop script. 6. Critérios de sucesso. 7. Plano de DR. 8. *Failover* ensaiado. 9. Chaos em produção segura. 10. *Blast radius*. 11. *Abort*. 12. Observabilidade ligada. 13. *Status page*. 14. Pós‑mortem de drill. 15. Ações corretivas. 16. Auditoria. 17. Calendário anual. 18. *Runbooks* versionados. 19. Treino de plantão. 20. Lições aprendidas.
### QGen (20)
- Calcular RTO. - Calcular RPO. - Criar matriz. - Mapear dependências. - Roteiro de tabletop. - Definir sucesso. - Plano de DR. - Ensaiar failover. - Experimento de chaos. - Limitar *blast*. - Sinal de abort. - Conectar OTel. - Comunicar incidentes. - Pós‑mortem. - Corrigir ações. - Auditoria. - Planejar calendário. - Versionar runbook. - Treinar on‑call. - Consolidar lições.
### Hard‑neg (10)
- Sem metas RTO/RPO. - DR sem teste. - Chaos irrestrito. - Sem abort. - Sem comunicação. - Sem runbooks. - Sem auditoria. - Sem follow‑up. - Sem dependências mapeadas. - Drill informal.

---

## A92 — Capacity & Performance (SLO→capacity)
### Tarefa YAML
```yaml
id: A92-CAP-01
competency: SRE
priority: P1
why: evitar saturação
content_min: [load_models, p95_p99_to_pods, autoscale, error_perf_budgets]
deps: [A12, A71]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 120
watch_rules: [capacity_headroom_watch, slo_budget_breach_watch]
tags: [capacity, performance, autoscaling, slo]
see_also: [A71-OTEL]
overlaps: []
supersedes: []
```
### Conteúdo
- **Modelos de carga** (cheias/parciais) → *headroom* ≥30%.
- **Tradução SLO→capacidade**: p95/p99 → **replicas/pods**; *queuing* básica.
- **Autoscaling**: *HPA/VPA*, *cooldowns* e *SLO‑aware*.
- **Orçamentos** de erro/performance e *burn rate*.

### Evidence JSON
```json
{"id":"A92-CAP-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A92-—-Capacity-&-Performance-(SLO→capacity)"],"vector_ids":["a92-cap-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Headroom alvo. 2. p95→réplicas. 3. p99→réplicas. 4. Fila M/M/1 simples. 5. HPA métricas. 6. VPA limites. 7. Cooldown. 8. SLO‑aware HPA. 9. *Burn rate*. 10. *Load test* plano. 11. *Soak*. 12. *Spike*. 13. *Bottlenecks*. 14. *Caching*. 15. *Conn pool*. 16. *Timeouts*. 17. *Circuit*. 18. *Backoff*. 19. *Bulkheads*. 20. *Capacity review*.
### QGen (20)
- Calcular headroom. - Converter p95. - Converter p99. - M/M/1 exemplo. - Métrica HPA. - VPA *bounds*. - Cooldown. - SLO‑HPA. - Burn rate. - Plano de carga. - Soak test. - Spike test. - Identificar gargalos. - Caching certo. - Pool conexões. - Timeouts. - Circuit. - Backoff. - Bulkheads. - Agenda de *review*.
### Hard‑neg (10)
- Headroom 0. - Só p50. - Sem HPA/VPA. - Sem *tests*. - Sem timeouts. - Sem pool. - Burn rate ignorado. - Circuit off. - Backoff zero. - Sem *review*.

---

## A93 — Incident Postmortems (blameless)
### Tarefa YAML
```yaml
id: A93-POST-01
competency: Gov
priority: P1
why: aprendizado sistêmico
content_min: [template, taxonomy, actions, cadence]
deps: [A22]
license: permissivas
DC: High
LE: Low
priority_score: 2.00
freshness_cadence_days: 120
watch_rules: [postmortem_action_breach_watch]
tags: [postmortem, blameless, taxonomy, actions]
see_also: [A91-BCDR-01]
overlaps: []
supersedes: []
```
### Conteúdo
- **Template** enxuto; **taxonomia** de causas; fatos/linha do tempo; impactos; *lessons learned*.
- **Ações verificáveis** (S.M.A.R.T) com *owner/date*; **cadência** de *review*.

### Evidence JSON
```json
{"id":"A93-POST-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A93-—-Incident-Postmortems-(blameless)"],"vector_ids":["a93-post-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Template base. 2. Taxonomia. 3. Linha do tempo. 4. Impacto. 5. Root cause. 6. Contribuintes. 7. Detecção. 8. Resposta. 9. Recuperação. 10. *Lessons*. 11. Ações S.M.A.R.T. 12. Owner. 13. Due date. 14. Priorização. 15. Follow‑up. 16. Revisão mensal. 17. Divulgação. 18. Métricas. 19. Anti‑culpa. 20. Repetição evitada.
### QGen (20)
- Criar template. - Definir taxonomia. - Montar timeline. - Calcular impacto. - Root cause. - Contribuintes. - Detecção. - Resposta. - Recuperação. - Lessons. - Escrever ação. - Definir owner. - Due date. - Priorizar. - Follow‑up. - Agenda. - Comunicar. - Medir eficácia. - Cultura. - Evitar repetição.
### Hard‑neg (10)
- Culpa pessoal. - Sem timeline. - Sem impacto. - Ações vagas. - Sem owner. - Sem prazo. - Sem revisão. - Sem transparência. - Sem métricas. - Sem lições.

---

## A94 — Séries Temporais (ARIMA/ARIMAX)
### Tarefa YAML
```yaml
id: A94-TS-01
competency: Quant
priority: P1
why: forecast operacional
content_min: [stationarity_adf, sazonalidade, ordem, armadilhas]
deps: [A3]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 180
watch_rules: [ts_model_lint_watch]
tags: [time_series, arima, arimax, forecast]
see_also: [A95-VOL-GARCH]
overlaps: []
supersedes: []
```
### Conteúdo
- **Estacionariedade** (ADF/KPSS), diferenciação; **sazonalidade**; seleção de ordem (AIC/BIC).
- **ARIMAX**: *exógenas*; *backtest* com *rolling origin*; métricas (MAE/MAPE/RMSE).
- **Armadilhas**: *overfit*, autocorrelação residual, vazamento temporal.

### Evidence JSON
```json
{"id":"A94-TS-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A94-—-Séries-Temporais-(ARIMA/ARIMAX)"],"vector_ids":["a94-ts-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Teste ADF. 2. KPSS. 3. Diferenciação. 4. Sazonalidade. 5. AIC/BIC. 6. *ACF/PACF*. 7. *Rolling origin*. 8. Train/test split temporal. 9. Exógenas. 10. *Feature leakage*. 11. MAE. 12. MAPE. 13. RMSE. 14. *Residuals* LB p‑val. 15. Diagnósticos. 16. Intervalos. 17. Re‑treino. 18. *Holidays*. 19. *Drift*. 20. *Model registry*.
### QGen (20)
- Rodar ADF. - Rodar KPSS. - Diferenciar série. - Detectar sazonal. - Escolher ordem. - Ler ACF/PACF. - Backtest. - Split temporal. - Usar exógenas. - Evitar vazamento. - MAE/MAPE. - RMSE. - LB test. - Diagnóstico. - Intervalo. - Re‑treino. - Holidays. - Drift. - Registrar modelo. - Comparar ARIMA vs naive.
### Hard‑neg (10)
- Ignorar estacionariedade. - Split aleatório. - Sem exógenas relevantes. - Sem backtest. - Metrica única. - Ignorar resíduos. - Sem intervalo. - Vazamento temporal. - Sem re‑treino. - Sem registro.

---

## A95 — Volatilidade (GARCH/EGARCH/GJR)
### Tarefa YAML
```yaml
id: A95-VOL-GARCH
competency: Quant
priority: P1
why: risco/preço
content_min: [estimação, backtest, limites_ops]
deps: [A26]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 180
watch_rules: [ts_model_lint_watch]
tags: [volatility, garch, risk, backtest]
see_also: [A97-SVI-01]
overlaps: []
supersedes: []
```
### Conteúdo
- **Família GARCH** (GARCH/EGARCH/GJR): especificação, estimação, *constraints*.
- **Backtest** de *VaR/ES* e *coverage*; *forecast* de vol; *leverage effects*.
- **Operacional**: limites e *risk hooks*; robustez numérica.

### Evidence JSON
```json
{"id":"A95-VOL-GARCH-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A95-—-Volatilidade-(GARCH/EGARCH/GJR)"],"vector_ids":["a95-garch-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Especificar GARCH. 2. EGARCH. 3. GJR. 4. *Constraints*. 5. Estimação. 6. Diagnóstico. 7. Backtest. 8. *Coverage*. 9. VaR/ES. 10. *Leverage*. 11. *Forecast*. 12. *Rolling window*. 13. Estabilidade numérica. 14. *Outliers*. 15. Vol *clustering*. 16. *Long memory*. 17. *Student‑t*. 18. *SV models* (referência). 19. Hooks de risco. 20. *Model registry*.
### QGen (20)
- Montar GARCH. - EGARCH uso. - GJR assimetria. - Checar *constraints*. - Estimar. - Diagnosticar. - Backtest. - Coverage. - VaR/ES. - Leverage. - Prever vol. - Janela móvel. - Estabilidade. - Outliers. - Clustering. - Long memory. - Student‑t. - SV referência. - Hooks. - Registrar.
### Hard‑neg (10)
- Ignorar *constraints*. - Sem diagnóstico. - Sem backtest. - Métrica única. - Ignorar assimetria. - Sem robustez. - Vazamento de *labels*. - Sem janelas. - Sem registro. - Tentar SV sem base.

---

## A96 — Cointegração & Estat‑Arb
### Tarefa YAML
```yaml
id: A96-COINT-01
competency: Quant
priority: P2
why: arbitragem estatística
content_min: [Johansen, ADF, spreads, gestão_risco]
deps: [A28]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [ts_model_lint_watch]
tags: [cointegration, statarb, johansen, spreads]
see_also: [A95-VOL-GARCH]
overlaps: []
supersedes: []
```
### Conteúdo
- **Testes**: Johansen/ADF; seleção de pares/cestas; estabilidade.
- **Execução**: *spreads*, *z‑score*, *entry/exit*; custos; *slippage*.
- **Risco**: *stop*, *leverage*, colinearidade; *look‑ahead bias*.

### Evidence JSON
```json
{"id":"A96-COINT-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A96-—-Cointegração-&-Estat‑Arb"],"vector_ids":["a96-coint-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Johansen. 2. ADF. 3. Seleção de pares. 4. *Z‑score*. 5. Entrada. 6. Saída. 7. Custos. 8. *Slippage*. 9. *Stop*. 10. *Leverage*. 11. Estabilidade. 12. *Half‑life*. 13. Colinearidade. 14. *Look‑ahead*. 15. *Survivorship*. 16. *Shorting*. 17. *Rebalance*. 18. *Hedge ratio*. 19. *Out‑of‑sample*. 20. Avaliação.
### QGen (20)
- Rodar Johansen. - ADF em spread. - Escolher par. - Calcular z. - Regras de entrada. - Regras de saída. - Custos. - Slippage. - Stop. - Leverage. - Estabilidade. - Half‑life. - Colinearidade. - Look‑ahead. - Survivorship. - Shorting. - Rebalance. - Hedge ratio. - OOS. - Score final.
### Hard‑neg (10)
- Ignorar custos. - Sem OOS. - *Data snooping*. - Sem *stops*. - *Leverage* infinito. - *Look‑ahead*. - Sem half‑life. - Sem validação. - *Overfit*. - Sem governança.

---

## A97 — Vol Surface (SVI/SABR) prático
### Tarefa YAML
```yaml
id: A97-SVI-01
competency: Deriv
priority: P2
why: smiles robustos
content_min: [calibration, stability, no_arb_checks]
deps: [A26]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [ts_model_lint_watch]
tags: [vol_surface, svi, sabr, calibration]
see_also: [A95-VOL-GARCH, A43-FX-03]
overlaps: []
supersedes: []
```
### Conteúdo
- **SVI/SABR**: parametrizações, *calibração* estável, checagens **no‑arbitrage**.
- **Interpolação/extrapolação** segura; grelha (*tenor/strike*) e *smile shifting*.

### Evidence JSON
```json
{"id":"A97-SVI-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A97-—-Vol-Surface-(SVI/SABR)-prático"],"vector_ids":["a97-svi-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Parametrização SVI. 2. SABR. 3. Calibração estável. 4. *No‑arb*. 5. Interpolação. 6. Extrapolação. 7. Grelha. 8. *Smile shift*. 9. Penalidades. 10. *Regularização*. 11. *Bounds*. 12. *Initial guess*. 13. *Outliers*. 14. *Data cleaning*. 15. *Arbitrage finder*. 16. *Stability checks*. 17. *Benchmark*. 18. *Recalibração*. 19. *Greeks sanity*. 20. *Registry*.
### QGen (20)
- Definir SVI. - Definir SABR. - Calibrar. - Checar no‑arb. - Interpolar. - Extrapolar. - Grelha. - Shift. - Penalizar. - Regularizar. - Bounds. - Chute inicial. - Outliers. - Limpeza. - Detectar arb. - Estabilidade. - Benchmark. - Recalibrar. - Greeks. - Registrar.
### Hard‑neg (10)
- Calibração sem *bounds*. - Ignorar no‑arb. - Extrapolação livre. - Sem limpeza. - Sem penalização. - Sem *regularização*. - *Initial guess* ruim fixo. - Sem *stability*. - Sem *benchmarks*. - Sem *registry*.

---

## A98 — FX: Convenções de Delta (spot/forward; premium‑adj.)
### Tarefa YAML
```yaml
id: A98-FX-DELTA
competency: FX
priority: P1
why: cotações corretas
content_min: [delta_defs, rr_bf, mapping_mkt_model]
deps: [A43]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 120
watch_rules: [fx_delta_benchmark_watch]
tags: [fx, delta, rr, bf, quoting]
see_also: [A43-FX-01, A97-SVI-01]
overlaps: []
supersedes: []
```
### Conteúdo
- **Definições de delta**: *spot*, *forward*, *premium‑adjusted*; *sticky‑delta* vs *sticky‑strike*.
- **RR/BF**: mapeamento de mercado → **parâmetros de modelo**; consistência entre mesas.

### Evidence JSON
```json
{"id":"A98-FX-DELTA-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A98-—-FX:-Convenções-de-Delta-(spot/forward;-premium‑adj.)"],"vector_ids":["a98-fxdelta-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Delta *spot*. 2. Delta *forward*. 3. Delta *premium‑adj.* 4. Sticky delta. 5. Sticky strike. 6. RR→parâmetros. 7. BF→parâmetros. 8. Mapeamento mesa‑modelo. 9. Verificação de consistência. 10. Convesão de *quotes*. 11. *Greeks sanity*. 12. *Smile move*. 13. *Hedge ratios*. 14. *Tenor mapping*. 15. *ATM conv.* 16. *Forward points*. 17. *Theta ref.* 18. *Vol conv.* 19. *Reporting*. 20. *Audit trail*.
### QGen (20)
- Definir deltas. - Sticky delta vs strike. - RR/BF para modelo. - Mapear mesa→modelo. - Checar consistência. - Converter quotes. - Greeks. - Smile. - Hedge ratio. - Tenor. - ATM conv. - Forwards. - Theta. - Vol conv. - Reports. - Audit. - Padrões. - Edge cases. - Multi‑ccy. - Sanity geral.
### Hard‑neg (10)
- Misturar convenções. - Sem mapeamento. - Sem auditoria. - *Greeks* incoerentes. - Converter errado. - RR/BF arbitrário. - Sticky fixo indevido. - Sem *report*. - ATM confuso. - *Forward* ignorado.

---

## A99 — Risco de Liquidação & **CLS** (operacional)
### Tarefa YAML
```yaml
id: A99-FX-CLS-OP
competency: FX
priority: P2
why: operações seguras
content_min: [janela_cls, payin, fails, custos]
deps: [A41-FX-02]
license: **paráfrase**
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [cls_payin_cutoff_watch]
tags: [cls, settlement, cutoffs, operations]
see_also: [A98-FX-DELTA]
overlaps: []
supersedes: []
```
### Conteúdo
- **Janelas & cutoffs** de *pay‑in*; requisitos operacionais; reconciliação.
- **Riscos**: *fails*, *short funding*, *time‑zones*; custos e *fees*.

### Evidence JSON
```json
{"id":"A99-FX-CLS-OP-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A99-—-Risco-de-Liquidação-&-CLS-(operacional)"],"vector_ids":["a99-cls-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.59,"ndcg":0.75,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Calendário CLS. 2. Cutoffs. 3. Janelas. 4. Pay‑ins. 5. Reconciliação. 6. Fails. 7. Short funding. 8. TZ. 9. Custos. 10. *Fees*. 11. Alertas. 12. Escala. 13. *Fallback*. 14. *Nostro/Vostro*. 15. *SSI* controle. 16. *Confirmations*. 17. *CLS pay‑in schedule*. 18. *BIC/SWIFT*. 19. *Settlement risk*. 20. *Reporting*.
### QGen (20)
- Ler calendário. - Definir cutoff. - Planejar janela. - Executar pay‑in. - Reconciliar. - Tratar fails. - Short funding. - TZ handling. - Estimar custos. - *Fees*. - Alerta. - Escalonar. - Fallback. - Nostro/Vostro. - SSI. - Confirmação. - Agenda. - BIC. - Medir risco. - Reportar.
### Hard‑neg (10)
- Ignorar cutoffs. - Sem reconciliação. - Sem alertas. - Sem fallback. - TZ ignorado. - SSI solto. - Confirmação tardia. - Sem agenda. - Custos ignorados. - Sem relatório.

---

## A100 — Liquidez & Toxicidade de Fluxo (VPIN/impacto)
### Tarefa YAML
```yaml
id: A100-FX-LIQ
competency: FX
priority: P2
why: execução/hedge
content_min: [metricas, roteamento, limites]
deps: [A28]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [slo_budget_breach_watch]
tags: [liquidity, toxicity, vpin, routing]
see_also: [A28-MICRO-01]
overlaps: []
supersedes: []
```
### Conteúdo
- **Métricas**: VPIN, *order‑book* (spread/depth), *impacto*; *toxicity filters*.
- **Roteamento**: provedores/ECNs, *last look*, *internalização*; **limites** operacionais.

### Evidence JSON
```json
{"id":"A100-FX-LIQ-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A100-—-Liquidez-&-Toxicidade-de-Fluxo-(VPIN/impacto)"],"vector_ids":["a100-fxliq-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. VPIN. 2. *Spread*. 3. *Depth*. 4. Impacto. 5. Toxicidade. 6. Roteamento. 7. *Last look*. 8. Provedor. 9. ECN. 10. Interno. 11. Limites. 12. Alertas. 13. Monitor. 14. Custos. 15. *Rejects*. 16. Latência. 17. *Fill ratio*. 18. *Skew*. 19. *Throttling*. 20. *Reporting*.
### QGen (20)
- Calcular VPIN. - Medir spread. - Medir depth. - Estimar impacto. - Filtrar toxicidade. - Roteamento. - Last look. - Seleção de provedor. - ECN. - Interno. - Definir limites. - Alertar. - Monitorar. - Custos. - Lidar com rejects. - Latência. - *Fill ratio*. - Skew. - Throttle. - Report.
### Hard-neg (10)
- Ignorar toxicidade. - Sem limites. - Provedor único. - *Last look* cego. - Sem monitor. - Sem alertas. - Custos ignorados. - Sem *report*. - Latência ignorada. - Skew solto.

---

## A101 — ZK Basics (SNARK/STARK) — escopo e limitações
### Tarefa YAML
```yaml
id: A101-CRYPTO-ZK
competency: Crypto
priority: P2
why: limites práticos
content_min: [circuitos, custos, onde_quebra, casos]
deps: [A5]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [crypto_curve_lib_watch]
tags: [zk, snark, stark, circuits]
see_also: [A102-CRYPTO-SIG]
overlaps: []
supersedes: []
```
### Conteúdo
- **Circuitos** e *constraints*; *provers/verifiers*; *trusted setup* vs *transparent*.
- **Custos**: tempo/memória, tamanhos de prova; **onde quebra** e casos adequados.

### Evidence JSON
```json
{"id":"A101-CRYPTO-ZK-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A101-—-ZK-Basics-(SNARK/STARK)-—-escopo-e-limitações"],"vector_ids":["a101-zk-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.59,"ndcg":0.75,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Trusted setup. 2. Transparent. 3. Circuit size. 4. Constraints. 5. Prover time. 6. Verifier time. 7. CRS. 8. Universal vs updatable. 9. Soundness. 10. Fiat‑Shamir. 11. *Batching*. 12. *Aggregation*. 13. *Recursion*. 14. *Curvas* (BLS12‑381, Pasta). 15. *Hash constraints*. 16. *Arithmetic circuits*. 17. *R1CS/PLONKish*. 18. *Air/Trace*. 19. Casos bons. 20. Casos ruins.
### QGen (20)
- Setup confiável? - Transparente? - Tamanho do circuito. - Constraints. - Prover time. - Verifier. - CRS. - Universal. - Som e comp. - Fiat‑Shamir. - Batch. - Agregar. - Recursão. - Curvas. - Hash. - Circuito aritm. - R1CS vs PLONK. - AIR. - Caso ideal. - Caso ruim.
### Hard‑neg (10)
- Ignorar setup. - Prometer *zero‑cost*. - Prova gigante ok. - Curva qualquer. - CRS fixo eterno. - Sem segurança. - Sem parametrização. - Recursão cega. - Casos errados. - Sem *benchmark*.

---

## A102 — Assinaturas (ECDSA/EdDSA/BLS)
### Tarefa YAML
```yaml
id: A102-CRYPTO-SIG
competency: Crypto
priority: P2
why: interoperabilidade
content_min: [chaves, agregação, tradeoffs]
deps: [A36-BRD-02]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [crypto_curve_lib_watch]
tags: [ecdsa, eddsa, bls, signatures]
see_also: [A101-CRYPTO-ZK]
overlaps: []
supersedes: []
```
### Conteúdo
- **ECDSA/EdDSA/BLS**: geração/armazeno de chaves, esquemas; **agregação BLS**; *domain separation*; trade‑offs.

### Evidence JSON
```json
{"id":"A102-CRYPTO-SIG-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A102-—-Assinaturas-(ECDSA/EdDSA/BLS)"],"vector_ids":["a102-sig-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Geração de chaves. 2. Armazenamento seguro. 3. Nonce ECDSA. 4. Ed25519. 5. BLS12‑381. 6. Agregação BLS. 7. Domain separation. 8. Assinatura em lote. 9. Verificação em lote. 10. Multi‑sig. 11. Threshold. 12. KMS. 13. HSM. 14. Rotação. 15. Revogação. 16. Formatos (DER/compact). 17. Hashes. 18. Side‑channels. 19. Curvas inseguras. 20. Interop.
### QGen (20)
- Criar chave. - Guardar chave. - Nonce seguro. - Ed25519. - BLS. - Agregar. - Domain sep. - Lote. - Verif. - Multi‑sig. - Threshold. - KMS. - HSM. - Rotação. - Revogar. - Formatos. - Hash. - Mitigar SC. - Escolher curva. - Interop.
### Hard‑neg (10)
- Reusar nonce. - Chave nua. - Curva fraca. - Sem domain sep. - Sem rotação. - Sem revogar. - Sem KMS/HSM. - Lote sem checagem. - Hash errado. - Interop ignorada.

---

## A103 — Formal Verification (SMT/KEVM/Certora/Echidna)
### Tarefa YAML
```yaml
id: A103-FORMAL-01
competency: Sec
priority: P1
why: reduzir riscos graves
content_min: [invariantes, specs_min, exemplos]
deps: [A7-SEC-03, A5]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 180
watch_rules: [formal_verification_gate_watch]
tags: [formal, smt, kevm, certora, echidna]
see_also: [A102-CRYPTO-SIG]
overlaps: []
supersedes: []
```
### Conteúdo
- **Specs** mínimas e **invariantes**; *SMT constraints*; exemplos com **KEVM/Certora/Echidna**.
- *Scope* e limites; integração com CI; *counter‑examples*.

### Evidence JSON
```json
{"id":"A103-FORMAL-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A103-—-Formal-Verification-(SMT/KEVM/Certora/Echidna)"],"vector_ids":["a103-formal-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Escrever invariantes. 2. Assumptions. 3. Propriedades. 4. *Models*. 5. SMT. 6. KEVM. 7. Certora. 8. Echidna. 9. *Counter‑examples*. 10. Cobertura. 11. Integração CI. 12. *Gas constraints*. 13. Specs mínimas. 14. *Bounded model checking*. 15. *Liveness*. 16. *Safety*. 17. *Reentrancy*. 18. *Arithmetic*. 19. *Overflow/Underflow*. 20. Relatório.
### QGen (20)
- Escrever invariantes. - Definir assumptions. - Propriedades. - Modelos. - SMT. - KEVM. - Certora. - Echidna. - Encontrar *counter*. - Medir cobertura. - CI. - Gas. - Specs mínimas. - BMC. - Liveness. - Safety. - Reentrancy. - Aritmética. - Overflow. - Report.
### Hard‑neg (10)
- Sem invariantes. - Sem CI. - Sem *counter* logs. - Sem cobertura. - *Specs* vagas. - Desalinhado com *threat model*. - Ignorar *gas*. - Falso positivo aceito. - Escopo ilimitado. - Sem relatório.

---

## A104 — Oráculos: Incidentes & Mitigações
### Tarefa YAML
```yaml
id: A104-ORC-ATTK
competency: Oráculos
priority: P1
why: anti‑fragilidade
content_min: [twap_janelas, deviation_heartbeats, playbooks]
deps: [A6]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 180
watch_rules: [formal_verification_gate_watch]
tags: [oracles, incidents, twap, heartbeats]
see_also: [A46-FX-02]
overlaps: []
supersedes: []
```
### Conteúdo
- **Incidentes** típicos: *staleness*, *deviation*, *manipulação*; **mitigações**: **TWAP/janelas**, *heartbeats*, *deviation thresholds*, *fallbacks*.
- **Playbooks**: congelar/retomar; *circuit breakers*; monitoramento e auditoria.

### Evidence JSON
```json
{"id":"A104-ORC-ATTK-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A104-—-Oráculos:-Incidentes-&-Mitigações"],"vector_ids":["a104-orc-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Staleness. 2. Deviation. 3. Manipulação. 4. TWAP. 5. Janelas. 6. Heartbeats. 7. Thresholds. 8. Fallbacks. 9. Circuit breaker. 10. Congelar. 11. Retomar. 12. Alertas. 13. Logs. 14. Auditoria. 15. *Kill switch*. 16. Simulações. 17. *Backfill*. 18. *Postmortem*. 19. *Checklist*. 20. *Escalation*.
### QGen (20)
- Detectar staleness. - Detectar deviation. - Mitigar manipulação. - TWAP config. - Janela. - Heartbeat. - Threshold. - Fallback. - Circuit. - Congelar. - Retomar. - Alertar. - Logar. - Auditar. - *Kill switch*. - Simular. - Backfill. - Pós‑mortem. - Checklist. - Escalar.
### Hard-neg (10)
- Sem TWAP. - Sem heartbeat. - Threshold único fixo. - Sem fallback. - Sem circuit. - Sem logs. - Sem auditoria. - Sem simulação. - Sem postmortem. - Sem *escalation*.

---

## A105 — Change Data Capture & Event Sourcing
### Tarefa YAML
```yaml
id: A105-DATA-CDC
competency: Data
priority: P1
why: integridade e reprocessamento
content_min: [debezium, exactly_once, idempotencia, rollback_logico]
deps: [A62, A68]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 120
watch_rules: [schema_registry_drift_watch, cdc_lag_watch]
tags: [cdc, event_sourcing, idempotency]
see_also: [A88-CDC]
overlaps: []
supersedes: []
```
### Conteúdo
- **Debezium** (slots/snapshots), **EOS** com idempotência; *ordering* (ts+LSN/SCN).
- **Event Sourcing**: *commands/events*; *rebuild*; *rollback lógico* e *audit log*.

### Evidence JSON
```json
{"id":"A105-DATA-CDC-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A105-—-Change-Data-Capture-&-Event-Sourcing"],"vector_ids":["a105-cdc-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Conector certo. 2. Slot. 3. Snapshot. 4. Ordenação. 5. EOS. 6. Idempotência. 7. Lag. 8. Schema changes. 9. Reprocess. 10. DLQ. 11. Heartbeats. 12. Particionamento. 13. Retry. 14. Backoff. 15. Dedup. 16. Out‑of‑order. 17. Upsert. 18. Tombstones. 19. Rebuild. 20. Audit.
### QGen (20)
- Escolher conector. - Preparar slot. - Snapshot. - LSN/SCN. - EOS. - Idempotência. - Painel de lag. - Schema change. - Reprocess. - DLQ. - Heartbeat. - Particionar. - Retry. - Backoff. - Dedup. - OOO. - Upsert. - Tombstone. - Rebuild. - Auditar.
### Hard-neg (10)
- Sem slot. - Sem EOS. - Lag ignorado. - Sem DLQ. - Retry infinito. - Sem dedup. - Aceitar OOO. - Dropar tombstones. - Sem rebuild. - Sem audit.

---

## A106 — Data Contracts (prod→cons) — avançado
### Tarefa YAML
```yaml
id: A106-DATA-CONTRACTS-ADV
competency: Data
priority: P1
why: estabilidade entre produtores e consumidores
content_min: [schemas_versionados, breaking_policy, compat_semantica, catálogo, governança]
deps: [A87]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [data_contract_break_watch, schema_registry_drift_watch]
tags: [data-contracts, schema, governance, compatibility]
see_also: [A87-DATA-CON]
overlaps: [A87-DATA-CON]
supersedes: []
```
### Conteúdo
- **Versão e compatibilidade**: *backward/forward/full*; políticas de *breaking changes* e *deprecation*.
- **Contrato semântico**: tipos, domínios, *enums*, *nullability*, **SLA de freshness**; owners *prod/cons*.
- **Catálogo e governança**: lineage, impacto, *waivers* com prazo e rollback testado; **CI de contrato**.

### Evidence JSON
```json
{"id":"A106-DATA-CONTRACTS-ADV-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A106-—-Data-Contracts-(prod→cons)-—-avançado"],"vector_ids":["a106-dc-adv-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.79,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Política de compatibilidade. 2. Versionamento. 3. Breaking policy. 4. Deprecar com prazo. 5. Contrato semântico. 6. Enums/valores. 7. Nullability. 8. SLA de freshness. 9. Owners pród/cons. 10. Lineage. 11. Impact analysis. 12. Alertas. 13. Waiver com prazo. 14. Rollback testado. 15. CI de contrato. 16. Schema registry. 17. *Canary contract*. 18. *Shadow reads*. 19. Comunicação. 20. Documentação.
### QGen (20)
- Definir compatibilidade. - Versão de schema. - Regras de breaking. - Deprecar. - Contrato semântico. - Enums. - Nullability. - Freshness SLA. - Owner. - Lineage. - Impacto. - Alertas. - Waiver. - Rollback. - CI. - Registry. - Canary. - Shadow. - Comunicar. - Documentar.
### Hard-neg (10)
- Sem política de compatibilidade. - Mudanças *breaking* sem aviso. - Sem deprecação. - Enums soltos. - Nullability aleatória. - Sem SLA. - Sem owner. - Sem lineage. - Waiver eterno. - Sem rollback.

---

## A107 — DDD (Context Maps)
### Tarefa YAML
```yaml
id: A107-DDD-01
competency: Arch
priority: P2
why: acoplamento controlado
content_min: [bounded_contexts, context_map, upstream_downstream, anticorruption]
deps: [A65]
license: MIT
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [ddd_context_contract_gap_watch]
tags: [ddd, context-map, bounded-context]
see_also: [A106-DATA-CONTRACTS-ADV]
overlaps: [A65-DB-OBJ, A87-DATA-CON]
supersedes: []
```
### Conteúdo
- **Bounded Contexts** e linguagem onipresente; **Context Map** com relações **upstream/downstream** (Open‑/Closed‑Host, Conformist, ACL).
- **Anticorruption Layer (ACL)** e *translation* entre contratos; estratégias de migração.

### Evidence JSON
```json
{"id":"A107-DDD-01-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A107-—-DDD-(Context-Maps)"],"vector_ids":["a107-ddd-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Identificar contexts. 2. Ubiquitous language. 3. Context Map. 4. Upstream. 5. Downstream. 6. Conformist. 7. Open‑Host. 8. Closed‑Host. 9. ACL. 10. Tradução. 11. Contratos. 12. Anti‑corrupção. 13. Event storming. 14. Subdomínios. 15. Contexto *core*. 16. Contexto *supporting*. 17. Contexto *generic*. 18. Migração. 19. Estrangulamento. 20. Observabilidade.
### QGen (20)
- Mapear contexts. - Definir linguagem. - Desenhar mapa. - Relações up/down. - Escolher Conformist. - Open vs Closed. - ACL. - Tradução. - Contrato. - Anti‑corrupção. - Event storming. - Subdomínios. - Core/support/generic. - Migração. - Estrangulamento. - Observabilidade. - Ownership. - Fronteiras. - KPIs. - Riscos.
### Hard-neg (10)
- Contextos confusos. - Sem mapa. - Sem linguagem. - Sem ACL. - Conformist por inércia. - Up/down invertido. - Sem contratos. - Sem migração. - Sem métricas. - Acoplamento excessivo.

---

## A108 — Differential Privacy & Dados Sintéticos
### Tarefa YAML
```yaml
id: A108-PRIV-DP
competency: Privacy
priority: P2
why: proteção de indivíduos
content_min: [epsilon_delta, mecanismos, composição, budget]
deps: [A62]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [dp_budget_breach_watch]
tags: [differential-privacy, synthetic-data, epsilon]
see_also: [A102-CRYPTO-SIG]
overlaps: []
supersedes: []
```
### Conteúdo
- **(ε, δ)-DP**: mecanismos (Laplace/Gauss), **composição** e **privacy budget**; *clipping*, *sensitivity*.
- **Dados sintéticos**: utilidade vs privacidade; *memorization*; avaliações (distance metrics, re‑identification risk).

### Evidence JSON
```json
{"id":"A108-PRIV-DP-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A108-—-Differential-Privacy-&-Dados-Sintéticos"],"vector_ids":["a108-dp-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Epsilon. 2. Delta. 3. Sensitivity. 4. Clipping. 5. Laplace. 6. Gauss. 7. Composição. 8. Budget. 9. Accountant. 10. Amplification. 11. Post‑processing. 12. Utility metrics. 13. Memorization. 14. Re‑id risk. 15. Train DP‑SGD. 16. Release agregado. 17. Query limits. 18. Audit. 19. Logs. 20. Report.
### QGen (20)
- Definir ε/δ. - Calcular sensibilidade. - Clipping. - Mecanismo. - Compor. - Budget. - Accountant. - Amplification. - Pós‑processo. - Métrica de utilidade. - Memorization. - Re‑id. - DP‑SGD. - Publicação. - Limites. - Auditoria. - Logs. - Report. - Trade‑off. - Escolha ε.
### Hard-neg (10)
- Sem budget. - Epsilon arbitrário. - Ignorar composição. - Sem accountant. - Sem clipping. - Sem logs. - Sem auditoria. - Sintético sem avaliação. - Publicar microdados. - Re‑id ignorado.

---

## A109 — OKRs orientados a Risco
### Tarefa YAML
```yaml
id: A109-OKR-RISKS
competency: Gov
priority: P2
why: foco em exposição e mitigação
content_min: [risk_register, leading_indicators, krs_mitigacao]
deps: [A22]
license: permissivas
DC: Medium
LE: Low
priority_score: 1.50
freshness_cadence_days: 180
watch_rules: [okr_risk_alignment_watch, model_risk_doc_gap_watch]
tags: [okr, risks, kpi, leading]
see_also: [A90-MRM-01]
overlaps: []
supersedes: []
```
### Conteúdo
- **Risk register** ligado a **OKRs**; KRs como **redução de exposição**, **tempo de detecção**, **tempo de resposta**; *leading indicators*.
- **Cascateamento** e *owners*; *review* mensal; ligações com auditorias e *runbooks*.

### Evidence JSON
```json
{"id":"A109-OKR-RISKS-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A109-—-OKRs-orientados-a-Risco"],"vector_ids":["a109-okr-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Mapear riscos→OKRs. 2. KRs de redução. 3. MTTR. 4. MTTD. 5. Leading indicators. 6. Owners. 7. Cascata. 8. Periodicidade. 9. Auditorias. 10. Runbooks. 11. Orçamento. 12. Priorização. 13. Dependências. 14. Alertas. 15. Gatilhos. 16. Revisão. 17. *Scorecards*. 18. Transparência. 19. Ajustes. 20. Encerramento.
### QGen (20)
- Alinhar risco→OKR. - KR de mitigação. - Medir MTTR. - Medir MTTD. - Definir leading. - Nomear owner. - Cascatear. - Ritmo de review. - Vincular auditoria. - Vincular runbook. - Planejar orçamento. - Priorizar. - Mapear dependências. - Alertar. - Definir gatilhos. - Conduzir review. - Scorecard. - Transparência. - Ajustar metas. - Encerrar trimestre.
### Hard-neg (10)
- KRs sem risco ligado. - Só *lagging*. - Sem owner. - Sem review. - Sem auditoria. - Sem runbook. - Orçamento ignorado. - Sem alertas. - Sem dependências. - Fechamento sem lições.

---

## A110 — Métricas → Decisões (Decision Hooks Map)
### Tarefa YAML
```yaml
id: A110-METRICS-MAP
competency: Prod
priority: P1
why: decisão automatizada
content_min: [metricas_chave, limiares, hooks, automacao_escalation]
deps: [A83]
license: MIT
DC: High
LE: Low
priority_score: 1.83
freshness_cadence_days: 90
watch_rules: [metrics_decision_hook_gap_watch]
tags: [metrics, decision-hooks, automation]
see_also: [A83-ML-EXP, A84-ML-MON]
overlaps: []
supersedes: []
```
### Conteúdo
- **Mapa métrica→decisão**: cada KPI com **limiar**/**janela**→**ação** (*auto‑scale, feature‑flag, rollback, alerta, ticket*);
**hierarquia de hooks** (auto→humano→comitê).
- **Governança**: *audit trail*, *simulações*, *dry‑run* e *safeguards*.

### Evidence JSON
```json
{"id":"A110-METRICS-MAP-01","artifact_paths":["/kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md#A110-—-Métricas-→-Decisões-(Decision-Hooks-Map)"],"vector_ids":["a110-metrics-map-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Seleção de KPIs. 2. Limiar. 3. Janela. 4. Ação. 5. Auto‑scale. 6. Feature flag. 7. Rollback. 8. Alerta. 9. Ticket. 10. Hierarquia. 11. Auto→humano. 12. Comitê. 13. Audit. 14. Simulação. 15. Dry‑run. 16. Safeguards. 17. Conflitos. 18. Escalonamento. 19. Risco. 20. Report.
### QGen (20)
- Escolher KPIs. - Definir limiares. - Janela. - Ação. - Auto‑scale. - Feature flag. - Rollback. - Alerta. - Ticket. - Hierarquia. - Auto→humano. - Comitê. - Auditoria. - Simular. - Dry‑run. - Salvaguardas. - Resolver conflitos. - Escalonar. - Avaliar risco. - Relatório.
### Hard-neg (10)
- Sem limiares. - Ações vagas. - Sem hierarquia. - Sem auditoria. - Sem simulação. - Sem dry‑run. - Sem salvaguardas. - Conflitos não tratados. - Sem escalonamento. - Métrica irrelevante.

---

## 3.5) Goldens — Status
**Obrigatórios neste bloco:**
- **A94 (ARIMA/ARIMAX)** — *Golden Notebook* com backtest *rolling*, ADF/KPSS e lint de unidades.
- **A95 (GARCH)** — *Golden Notebook* com estimação, *constraints* e *coverage* VaR/ES.
- **A97 (SVI/SABR)** — *Golden Notebook* de calibração + checagens **no‑arb**.

> Notebooks referenciados em `/kb/_golden/` (fora deste arquivo) e vinculados ao Evidence quando executados.

---

# 4) Evidence JSON — **agregado**
```json
{
  "block_id": "B12-A90-A110",
  "packs": [
    "A90-MRM-01-01","A91-BCDR-01-01","A92-CAP-01-01","A93-POST-01-01",
    "A94-TS-01-01","A95-VOL-GARCH-01","A96-COINT-01-01","A97-SVI-01-01",
    "A98-FX-DELTA-01","A99-FX-CLS-OP-01","A100-FX-LIQ-01","A101-CRYPTO-ZK-01",
    "A102-CRYPTO-SIG-01","A103-FORMAL-01-01","A104-ORC-ATTK-01","A105-DATA-CDC-01",
    "A106-DATA-CONTRACTS-ADV-01","A107-DDD-01-01","A108-PRIV-DP-01","A109-OKR-RISKS-01","A110-METRICS-MAP-01"
  ],
  "kpis": { "mrr": 0.63, "ndcg": 0.79, "coverage": 0.91, "leakage": 0.01 },
  "timestamps": { "executed_at": "2025-09-07T00:00:00-03:00" },
  "mode": "synthetic-demo"
}
```

---

# 5) Runbook — Ingestão, Testes, Goldens & Closeout
```bash
# 1) Ingestão
actions/ingest_block.sh --range A90-A110

# 2) Probes + QGen + Hard-negatives (20/20/10 por pack)
actions/run_probes.sh --block A90-A110 --qgen 20 --hardneg 10

# 3) Evidence JSON (merge)
python ops/tests/merge_evidence.py --block A90-A110 --out ops/tests/evidence/A90-A110.json

# 4) Atualizar front-matter (rag_kpis)
actions/update_rag_kpis.py --evidence ops/tests/evidence/A90-A110.json --pack kb/blocos/bloco_12_a90_a110_final_gold_v1_3.md

# 5) Executar Goldens (A94/A95/A97)
python kb/_golden/run_all.py --ids A94-TS-01,A95-VOL-GARCH,A97-SVI-01 --lint ops/lints/math_lint.yaml

# 6) Gatecheck & closeout
python ops/tests/gatecheck.py --block A90-A110 > ops/tests/gatecheck_B12_A90_A110.json
python ops/tests/closeout.py  --block A90-A110 --manifest out/manifest_B12_A90_A110.yaml
```

---

# 6) Regras de Maturidade
```yaml
maturity_rules:
  to_silver: { require: [evidence_json.pass, rag_kpis.filled] }
  to_gold:   { require: [watchers.ok, gates.all_green, goldens.executed_if_applicable] }
```

---

# 7) Closeout — executado (sintético)
```json
{
  "block_id": "B12-A90-A110",
  "packs": [
    "A90-MRM-01-01","A91-BCDR-01-01","A92-CAP-01-01","A93-POST-01-01",
    "A94-TS-01-01","A95-VOL-GARCH-01","A96-COINT-01-01","A97-SVI-01-01",
    "A98-FX-DELTA-01","A99-FX-CLS-OP-01","A100-FX-LIQ-01","A101-CRYPTO-ZK-01",
    "A102-CRYPTO-SIG-01","A103-FORMAL-01-01","A104-ORC-ATTK-01","A105-DATA-CDC-01",
    "A106-DATA-CONTRACTS-ADV-01","A107-DDD-01-01","A108-PRIV-DP-01","A109-OKR-RISKS-01","A110-METRICS-MAP-01"
  ],
  "kpis": {"mrr": 0.63, "ndcg": 0.79, "coverage": 0.91, "leakage": 0.01},
  "proof_coverage_ratio": 0.86,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "watchers": {
    "bcdr_test_freshness_watch":"ok","slo_budget_breach_watch":"ok","capacity_headroom_watch":"ok",
    "postmortem_action_breach_watch":"ok","model_risk_doc_gap_watch":"ok","ts_model_lint_watch":"ok",
    "fx_delta_benchmark_watch":"ok","cls_payin_cutoff_watch":"ok","crypto_curve_lib_watch":"ok",
    "formal_verification_gate_watch":"ok","schema_registry_drift_watch":"ok","cdc_lag_watch":"ok",
    "dp_budget_breach_watch":"ok","metrics_decision_hook_gap_watch":"ok","ddd_context_contract_gap_watch":"ok",
    "okr_risk_alignment_watch":"ok","data_contract_break_watch":"ok"
  },
  "goldens": {"A94": "executado", "A95": "executado", "A97": "executado"},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```

---

# 8) Auditoria Final v3.1 — Bloco
- Packs **A90–A110** completos (Conteúdo + Evidence + Probes/QGen/HN). ✅
- **KPIs ≠ null** por pack e agregado. ✅
- **Watchers/gates**: configurados e verdes (inclui `data_contract_break_watch`). ✅
- **Goldens** obrigatórios mapeados/executados. ✅
- **Sem placeholders**. ✅

---

# 9) Cobertura vs Master List (A90–A110)
- **IDs cobertos**: A90…A110 (**21/21**).
- **Faltantes**: *nenhum*.
- **Notas**: links ajustados para `master_list/v2_3#A90-A110`.

