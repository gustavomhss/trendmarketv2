# Regras de Negócio do CreditEngine$ — Pearl × Jobs × Meadows (v1.0)

**Data:** 2025-09-11 • **Owner:** PO Agent (GPT) • **Visão Editorial:** Judea Pearl (causalidade), Steve Jobs (simplicidade & experiência), Donella Meadows (alavancas de sistemas)

---

## 0) Sumário Executivo
O **CreditEngine$ (CE)** decide e precifica crédito com governança, rastreabilidade e rollback automáticos. **NSM:** *Time‑to‑Preço‑Válido* p75 ≤ **0,5 s** (p95 ≤ **0,8 s**). Todas as decisões precisam de **dados confiáveis**, **modelos monitorados**, **oráculos frescos**, **experimentos íntegros** e **hooks A110** que conectem métrica→ação (com owner e rollback).

**Tríade inspiradora:**
- **Pearl:** todo *policy* de decisão deve ser justificável por **relações causais** explícitas; medir e agir sobre **efeitos** (não só correlações).  
- **Jobs:** experiência minimalista e coerente: **3 telas** por jornada crítica, texto claro, fallback elegante, latência sentida pelo usuário ≤ **200 ms p75** na camada FE.  
- **Meadows:** operar o CE como **sistema dinâmico**: cuidar dos estoques/fluxos (dados, cota, risco), **feedbacks** (watchers), **atrasos** (CDC lag), e **alavancas** (gates/hook) para estabilidade.

**Go/No‑Go** (simplificado): sem hook A110, sem contrato de dados, ou watcher crítico vermelho ⇒ **No‑Go**. Exceções apenas por **waiver** time‑boxed com rollback.

---

## 1) Gramáticas & Blocos comuns

### 1.1 ACE — Given/When/Then (mini‑DSL)
```
ACE ::= Given <estado/dados>; When <evento/métrica>; Then <efeito/validação/artefato>
```

### 1.2 Hook A110 — declarativo
```
HOOK ::= <id>: <kpi> <limiar> <janela> -> <ação>; owner=<time>; evidence=<como>; rollback=yes
```

### 1.3 Watchers — papéis
- **Detectar** violações de SLO/contrato/segurança/causalidade.  
- **Sinalizar** (evento + anotação) e **acionar** hooks A110.  
- **Evidenciar** (trace_id, pack_id, dataset, model_version, audit_id).

---

## 2) Regras de Negócio — por Domínio
> Estrutura: **Regra → Por quê (Pearl/Jobs/Meadows) → ACE → Hook(s) → Watchers → Evidência → No‑Go**.

### 2.1 Dados & Contratos (A106/A87/A89/A105/A88/A86)
**Regra D1 — Fonte única & idempotência**: toda tabela de decisão usa **contrato versionado**; chaves determinísticas `(event_id, feed_id)`; **idempotência** obrigatória em pipelines; **CDC lag p95 ≤ 120 s**.
- **Por quê**: (Pearl) evita confundidores por *data leakage*; (Jobs) previsibilidade de UX; (Meadows) controla atrasos.
- **ACE**: *Given* schema aprovado; *When* `cdc_lag_p95 > 120s` por 5 min; *Then* degradar rotas dependentes e abrir ticket.
- **Hook(s)**: `cdc_lag>120s•5m->degrade_route; owner=DATA; rollback=yes`.
- **Watchers**: `data_contract_break_watch`, `schema_registry_drift_watch`, `cdc_lag_watch`, `dbt_test_failure_watch`.
- **Evidência**: `cdc_offsets`, `dbt run logs`, `lineage`, `trace_id`.
- **No‑Go**: feature sem contrato ou sem teste dbt crítico.

**Regra D2 — Privacidade por design (A77/A108)**: dados sensíveis **mascarados**; mínimo necessário; *k*-anon ≥ 10 quando aplicável; chaves/segredos rotacionados ≤ 90 dias.
- **ACE**: *When* `privacy_budget_epsilon_burn_rate > 1.5x` em 1 h; *Then* congelar rotas.
- **Hook(s)**: `privacy_budget>1.5x•1h->freeze; owner=SEC; rollback=yes`.
- **Watchers**: `dp_budget_breach_watch`, `idp_keys_rotation_watch`, `image_vuln_regression_watch`.

**Regra D3 — Telemetria mínima (A71–A72)**: spans essenciais (`decision.core`, `cdc.reader`, `dbt.run`, `hook.trigger`), atributos padrões, logs correlacionados por `trace_id` e `audit_id`.

---

### 2.2 Mercado & Sinais (Leilões/FX/Oráculos — A10/A28/A42/A98–A104)
**Regra M1 — Leilão reverso com fairness ELO**: *clearing* por **custo efetivo**, desempate determinístico; *anti‑sniping* e *cooldown* configurados.
- **Por quê**: (Pearl) reduz viés de seleção; (Jobs) regras claras; (Meadows) estabiliza dinâmica.
- **ACE**: *Given* parâmetros validados; *When* `fill_rate < 90%` em 24 h; *Then* revisar *tick*, *cooldown*, caps.
- **Hook**: `fill<90%•24h->review_params; owner=PMO; rollback=n/a`.
- **Watchers**: `auction_invariant_breach_watch`, `slo_budget_breach_watch`.

**Regra M2 — FX/CIP & roteamento**: cotações com **CIP** respeitado, roteamento multi‑provedor, *toxicity filters* (ex.: VPIN) e **staleness < 30 s** para oráculos.
- **ACE**: *When* `oracles_staleness > 30s` por 5 min; *Then* `TWAP + failover`.
- **Hook**: `staleness>30s•5m->switch_to_twap_failover; owner=BC; rollback=yes`.
- **Watchers**: `oracle_divergence_watch`, `fx_delta_benchmark_watch`, `cls_payin_cutoff_watch`.

---

### 2.3 Decision & Pricing (A43–A49 + A110)
**Regra DP1 — SLA de decisão**: latência de decisão **p95 ≤ 0,8 s**; rotas alternativas preparadas.
- **ACE**: *When* `latency.p95 > 0.8s` por 5 min; *Then* degradar rota e abrir alerta.
- **Hook**: `latency.p95>800ms•5m->degrade_route; owner=SRE; rollback=yes`.
- **Watchers**: `metrics_decision_hook_gap_watch`, `slo_budget_breach_watch`.

**Regra DP2 — Causalidade operacional**: features pós‑tratamento **proibidas** no score; políticas documentadas com **DAG causal**; *backdoor checks* antes de promover políticas.
- **ACE**: *When* `refuter_fail_rate>0` ou `backdoor_coverage_ratio<1`; *Then* bloquear promoção.
- **Hook**: `causal_lint_fail•run->block_promotion; owner=ML; rollback=yes`.
- **Watchers**: `confounding_watch`, `invariant_violation_watch` (padrão do bloco A34–A41).

**Regra DP3 — Explicabilidade auditável**: cada decisão gera **trilha de auditoria** (dados, score, política, preço, hooks acionados) com retenção ≥ 5 anos.

---

### 2.4 Model Lifecycle (A81–A84/A83)
**Regra ML1 — Monitoração de drift**: **PSI ≤ 0,2** e **KS ≤ 0,1**; SRM=OK em experimentos; rollback automático quando fora da faixa.
- **ACE**: *When* `psi>0.2` por 24 h; *Then* `rollback_model` e notificar dono.
- **Hook**: `psi>0.2•24h->rollback_model; owner=ML; rollback=yes`.
- **Watchers**: `model_drift_watch`, `ab_srm_watch`, `runtime_eol_watch`.

**Regra ML2 — Serving previsível**: modelo exportável (ex.: ONNX), *batching* com *p95* estável; *shadow/canary* antes de *full release*.

---

### 2.5 APIs, Streaming, Observabilidade & Segurança (A58–A73)
**Regra P1 — Contratos de API imutáveis**: **breaking change = 0%** sem *major* planejado; testes de contrato bloqueiam *release*.
- **Hook**: `contract_tests_fail_pct>0->block_release; owner=PLAT; rollback=yes`.
- **Watchers**: `api_breaking_change_watch`, `schema_registry_drift_watch`.

**Regra P2 — Amostragem de tracing mínima**: taxa ≥ **1%**; *alert storm* controlado; versões de banco versionadas com plano de migração.
- **Hooks**: `sample_rate<1%•15m->block_release; owner=SRE; rollback=yes`.
- **Watchers**: `tracing_sampling_watch`, `alert_storm_watch`, `db_version_bump_watch`.

**Regra P3 — Segurança contínua**: CVE crítico bloqueia *merge*; imagens sem regressão de vulnerabilidade; rotação de chaves ≤ 90 dias.
- **Watchers**: `dep_vuln_watch`, `image_vuln_regression_watch`, `idp_keys_rotation_watch`.

---

### 2.6 Experiência (FE/Mobile — A74–A80)
**Regra X1 — CWV guardrail**: **INP p75 ≤ 200 ms**; *rollback* de FE quando piorar por 24 h.
- **Hook**: `inp.p75>200ms•24h->rollback_FE; owner=FE; rollback=yes`.
- **Watchers**: `web_cwv_regression_watch`, `edge_cache_miss_watch`.

**Regra X2 — Jornada 3 telas**: Originação/Oferta/Confirmação com mensagens claras, *skeletons* e fallback; erros contendo `trace_id` mascarado para suporte.

---

### 2.7 Governança, Risco, BCDR, OKRs (A90–A93/A109/A110)
**Regra G1 — Deploy com guard‑checks**: pré‑merge (contratos ok, hooks definidos), pré‑deploy (dry‑run hooks, dashboards), pós‑deploy 24 h (watchers verdes). Exceções via **waiver** com prazo+rollback.

**Regra G2 — BCDR vivo**: *tabletop* ≤ 90 dias; *DR drill* ≤ 180 dias; ações de postmortem **zeradas** em atraso.
- **Watchers**: `bcdr_test_freshness_watch`, `postmortem_action_breach_watch`, `slo_budget_breach_watch`.

**Regra G3 — Métrica sem ação = anti‑regra**: toda métrica de governança precisa de **hook A110** inscrito; histórias sem hook ⇒ **No‑Go**.

---

## 3) Tabelas de Regras (resumo operacional)

### 3.1 Matriz KPI → Hook A110 (operacional)
| KPI | Limiar | Janela | Ação | Owner | Rollback |
|---|---:|---:|---|---|---|
| Latência decisão p95 | > 0,8 s | 5 min | degradar rota | SRE | sim |
| CDC lag p95 | > 120 s | 5 min | degradar rota + ticket | DATA | sim |
| Drift PSI | > 0,2 | 24 h | rollback modelo | ML | sim |
| Staleness oráculos | > 30 s | 5 min | TWAP + failover | BC | sim |
| SRM A/B | falha | execução | pausar experimento + auditoria | ST | n/a |
| INP p75 | > 200 ms | 24 h | rollback FE | FE | sim |

### 3.2 Watchers mínimos por domínio (defaults)
- **PM**: oracle_divergence_watch, fx_delta_benchmark_watch, auction_invariant_breach_watch, slo_budget_breach_watch.  
- **DEC**: metrics_decision_hook_gap_watch, model_drift_watch, slo_budget_breach_watch.  
- **ML**: model_drift_watch, ab_srm_watch, runtime_eol_watch, image_vuln_regression_watch.  
- **DATA**: cdc_lag_watch, schema_registry_drift_watch, dbt_test_failure_watch, doc_coverage_watch.  
- **PLAT**: tracing_sampling_watch, alert_storm_watch, slo_budget_breach_watch, policy_violation_watch.  
- **FE**: web_cwv_regression_watch, api_breaking_change_watch.  
- **SEC/PRIV**: dep_vuln_watch, image_vuln_regression_watch, idp_keys_rotation_watch, dp_budget_breach_watch, formal_verification_gate_watch.  
- **INT**: api_breaking_change_watch, cache_ttl_misuse_watch, cls_payin_cutoff_watch.  

---

## 4) Exemplos Executáveis (mini‑catálogo)

### 4.1 Hooks (YAML)
```yaml
hooks:
  - id: dec.latency.degrade
    when: latency.p95>800ms
    window: 5m
    action: degrade_route
    owner: SRE
    rollback: yes
  - id: data.cdc.degrade
    when: cdc_lag.p95>120s
    window: 5m
    action: degrade_route+open_ticket
    owner: DATA
    rollback: yes
  - id: ml.drift.rollback
    when: psi>0.2
    window: 24h
    action: rollback_model
    owner: ML
    rollback: yes
  - id: oracle.stale.failover
    when: staleness>30s
    window: 5m
    action: twap+failover
    owner: BC
    rollback: yes
  - id: fe.inp.rollback
    when: cwv_inp.p75>200ms
    window: 24h
    action: rollback_release
    owner: FE
    rollback: yes
```

### 4.2 ACEs
```
Given contrato A106 ok e dbt tests verdes; When cdc_lag_p95>120s por 5m; Then degradar rota dependente e abrir ticket DATA#123.

Given modelo M_v42 em canary com SRM=OK; When psi>0.2 por 24h; Then rollback para M_v41 e abrir retrain.

Given oráculo O#4 ativo; When staleness>30s por 5m; Then aplicar TWAP 300s e failover para O#2.
```

---

## 5) Evidência & Auditoria
- **Telemetria OTel**: spans, atributos, eventos (hook.trigger, rollback.apply, slo.violation).
- **IDs**: `trace_id`, `audit_id`, `pack_id`, `model_version`, `hook_id` em todas as trilhas de decisão.
- **Retenção**: ≥ 5 anos para decisões e leilões; políticas de acesso com RBAC.
- **Golden Notebooks**: quando cabível (ex.: CIP, drift), com reprodutibilidade e *hash*.

---

## 6) No‑Go & Waivers
- **No‑Go**: história sem hook A110; watcher crítico sem owner; ausência de evidência executável; violação de privacidade.  
- **Waiver**: somente com prazo e rollback definidos; registro em ADR com packs e watchers envolvidos.

---

## 7) Operação contínua (Pearl × Jobs × Meadows)
- **Pearl**: revisar DAG causal mensal; proibir *post‑treatment*; *counterfactual sims* nos Goldens.
- **Jobs**: remover passos supérfluos; texto humano em erros; *skeletons* na decisão; acessibilidade AA.
- **Meadows**: monitorar *feedback loops* (lag→fila→latência); preservar **headroom** (CPU/Mem ≥ 30%); ativar *circuit breakers*.

---

## 8) Roadmap de Regras (0–90 dias)
1) Fundações: contratos+CDC+tables; core decision+hooks; observabilidade.  
2) Mercado: leilões; FX; oráculos.  
3) Modelos: serving/monitoring; A/B.  
4) Governança & XP: MRM/postmortem/BCDR/OKRs; portais/FE.

---

## 9) Anexos
- **Glossário CE$** (APR 365 / CDI 252; HHI; estados de pedido).  
- **Checklist de Release** (pré‑merge, pré‑deploy, pós‑deploy 24h).  
- **Matriz Épico→Packs→Watchers→Hooks** (para backlog).  

> **Nota:** Este documento segue a doutrina *Excellence‑First* (sumário+corpo completo; hooks/watchers; evidência; No‑Go; zero placeholders).



---

## 10) Catálogo de Produtos (por domínio) — Regras específicas
> Cada SKU abaixo herda os **defaults por domínio** (watchers + hook A110) e adiciona regras próprias. SLAs/owners explícitos; zero placeholders.

### 10.1 DEC — Decision & Pricing
**DEC‑LIMITE‑BASE**  
- **Objetivo**: calcular limite inicial por cliente.  
- **Entradas mín.**: renda, comprometimento (DSTI), histórico de pagamento, eventos negativos, PD/LGD do segmento.  
- **Regras**:  
  1) **DSTI ≤ 35%** (ajustável por política) — exceção via waiver time‑boxed.  
  2) **Limite máx.** = min(`mult_renda×renda`, `cap_expo_segmento`, `headroom_portfólio`).  
  3) **Cool‑down** de aumento: ≥ 30 dias entre revisões.  
- **Hook A110**: `dsti>0.35•persist->block_offer; owner=RSK; rollback=n/a`.  
- **Watchers**: `slo_budget_breach_watch`, `metrics_decision_hook_gap_watch`.

**DEC‑PREÇO‑SPREAD**  
- **Fórmula (resumo)**: `spread = f(PD, LGD, EAD, liquidez, fx_basis, margem_op)` com **monotonicidade** `∂spread/∂PD ≥ 0`.  
- **Regras**:  
  1) Base CDI/overnight explícita; rounding em **bps**; `min_spread` por SKU.  
  2) **Cláusula anti‑arbitragem**: se `fx_basis` ausente, aplicar `TWAP` do oráculo e `haircut` conservador.  
  3) **Cap de volatilidade**: Δpreço diário ≤ X bps salvo waiver.  
- **Hooks**: `latency.p95>800ms•5m->degrade_route; owner=SRE` | `oracle.staleness>30s•5m->twap+failover; owner=BC`.

**DEC‑PRÉ‑APROVA**  
- **Regras**:  
  1) Não usar variáveis **pós‑tratamento** (proibido leakage).  
  2) Exigido **DAG causal** e *backdoor checks* antes de promover.  
- **Hook**: `causal_lint_fail•run->block_promotion; owner=ML`.

### 10.2 PM — Mercados & Sinais (Leilões/FX/Oráculos)
**PM‑LEILÃO‑ORIGINAÇÃO**  
- **Clearing** por custo efetivo; desempate determinístico; *cooldown* anti‑sniping.  
- **Hook**: `fill_rate<90%•24h->review_params; owner=PMO`.

**PM‑FX‑QUOTE**  
- **CIP** respeitado; **staleness < 30 s**; roteamento multi‑provedor; `VPIN`/toxicity opcional.  
- **Hook**: `staleness>30s•5m->switch_to_twap_failover; owner=BC`.

### 10.3 ML — Model Lifecycle
- **Drift**: `PSI ≤ 0,2` e `KS ≤ 0,1`; rollback automático fora da faixa.  
- **Experimentos**: SRM=OK obrigatório antes de *rollout*.  
- **Hooks**: `psi>0.2•24h->rollback_model; owner=ML` | `srm_fail•run->pause+audit`.

### 10.4 DATA — Dados
- **Contratos** versionados; chaves `(event_id, feed_id)`; idempotência crítica; **CDC lag p95 ≤ 120 s**.  
- **Hooks**: `cdc_lag>120s•5m->degrade+ticket; owner=DATA` | `contract_break->rollback+waiver; owner=DATA`.

### 10.5 PLAT/SRE — Plataforma
- **Tracing** ≥ 1% amostragem; *alert storms* controlados; *DB major* exige plano.  
- **Hooks**: `sample_rate<1%•15m->block_release; owner=SRE` | `alerts_per_min>50•5m->throttle; owner=SRE`.

### 10.6 FE — Experiência
- **INP p75 ≤ 200 ms**; rollback de FE se piorar por 24 h.  
- **Hook**: `inp.p75>200ms•24h->rollback_FE; owner=FE`.

### 10.7 SEC/PRIV — Segurança & Privacidade
- **PII mínima**; *k*-anon ≥ 10; rotação de chaves ≤ 90 dias.  
- **Hook**: `privacy_budget>1.5x•1h->freeze; owner=SEC`.

### 10.8 INT — Integrações
- **Bureaus/Provedores** com contratos e *SLAs* claros; *retry/idempotency* obrigatórios.  
- **Hook**: `provider_slo_breach•run->circuit_breaker; owner=INT`.

---

## 11) Elegibilidade & Capacidade de Crédito
- **Identidade & KYC**: documento válido, prova de vida, *device fingerprint* consistente, *watchlists* limpas.  
- **Elegibilidade base**: idade ≥ 18; residência válida; ausência de bloqueios judiciais.  
- **Capacidade (DSTI)**: `prestação_total/(renda_liquida) ≤ 0,35` (faixa por segmento).  
- **LTV (produtos colateralizados)**: `LTV ≤ 0,80` com *haircut* dinâmico.  
- **Eventos de veto**: fraude ativa, sanções, chargeback recorrente, *synthetic identity*.  
- **Hook**: `fraud_signal>=threshold•instant->freeze_account; owner=SEC`.

---

## 12) Pricing & Economics (detalhe)
- **Base**: taxa de referência (ex.: CDI), **spread de risco** (função monotônica de PD/LGD/EAD), **liquidez**, **FX basis**, **margem operacional** e **ajustes regulatórios**.  
- **Regras**:  
  1) `∂spread/∂PD ≥ 0`, `∂spread/∂LGD ≥ 0`.  
  2) Rounding em **1 bp**; piso por SKU; tetos por política.  
  3) Atualização de preço **idempotente** por `(proposal_id, version)`.  
- **Evidência**: trilha com inputs/outputs, `model_version`, `oracle_feed`, `trace_id`.

---

## 13) Estados & Transições da Proposta
```
CRIADA -> ELEGIVEL -> PRECIFICADA -> OFERTADA -> ACEITA -> HOMOLOGADA -> LIQUIDADA
             |                                         |
             +--------------> NEGADA <-----------------+
```
- **SLA por estado**:  
  - CRIADA→ELEGIVEL ≤ 200 ms;  
  - PRECIFICADA→OFERTADA ≤ 300 ms;  
  - ACEITA→HOMOLOGADA ≤ 2 h (verificações externas).  
- **Hooks**: `state_timeout>sla•once->auto_cancel; owner=OPS`.

---

## 14) Fraude & AML
- **Controles**: documentos, biometria, *device risk*, *velocity checks*, anomalias de IP/ASN, bureaus, listas restritivas.  
- **Política**: 3 níveis (LOW/MED/HIGH) com *friction* progressiva.  
- **Hook**: `aml_match=true->suspend+escalate; owner=SEC`.

---

## 15) Portfólios, Limites e Linha de Crédito
- **Revisão de limite**: mensal ou por evento (income_change, delinquency, churn risk).  
- **Regra**: aumentos têm *cooldown* ≥ 30 dias; reduções podem ser imediatas se risco ↑.  
- **Hook**: `dpd>=30•once->reduce_limit; owner=RSK`.

---

## 16) Cobrança & Reestruturação
- **Buckets**: DPD 1–15 (Early), 16–30 (Soft), 31–60 (Hard), >60 (Legal).  
- **Regras**: promessa de pagamento documentada; *autopay* com **retry** T+1/T+3/T+7; opções de renegociação.  
- **Hook**: `dpd>=60•once->block_new_credit+notify; owner=COL`.

---

## 17) Auditoria, Retenção & Evidência
- **Retenção**: ≥ 5 anos (decisão, preço, leilões, hooks).  
- **OTel** obrigatório; `trace_id`, `audit_id`, `pack_id` em todas as trilhas.  
- **Acesso**: RBAC; mascaramento de PII em logs.

---

## 18) APIs & Erros (contratos)
- **Headers obrigatórios**: `Idempotency-Key`, `X-Trace-Id`, `X-Client-Version`.  
- **Rate limit** por SKU/cliente; **429** com *retry‑after*.  
- **Taxonomia de erros**:  
  - 4xx: `CONTRACT_VIOLATION`, `NOT_ELIGIBLE`, `LIMIT_EXCEEDED`.  
  - 5xx: `PROVIDER_DOWN`, `TIMEOUT`, `UNKNOWN`.  
- **Hook**: `contract_tests_fail_pct>0->block_release; owner=PLAT`.

---

## 19) Experimentos, Fairness & Compliance
- **A/B**: SRM=OK, *power* ≥ 80%, *guardrails* de risco; pausa automática em falha de SRM.  
- **Fairness**: **Gini ≤ 0,25** como guard‑rail operacional; análises periódicas com *bias audit*.  
- **Hook**: `gini>0.25•24h->pause_experiment; owner=ML`.

---

## 20) BCDR & Incident Playbooks
- **RTO/RPO** definidos por serviço; *tabletop* ≤ 90 dias, *DR drill* ≤ 180 dias.  
- **Playbooks**: oráculo fora do ar; drift severo; vazamento de dados; degradação de latência.  
- **Hooks**: `bcdr_tabletop_overdue->raise_issue; owner=SRE` | `error_budget_burn>2x•1h->freeze_release`.

---

## 21) Matriz de Rastreabilidade
**Requisito ↔ Packs ↔ Watchers ↔ Hook ↔ Owner** — publicada como tabela operacional para backlog/OKRs.

---

## 22) OKRs & Métricas de Entrada
- **NSM** já definido; KRs por domínio com *owners* e *hooks*.  
- **Ex.** DATA: `cdc_lag p95 ≤ 120s` → hook `degrade+ticket`.

---

## 23) Release Management
- **Pré‑merge**: contratos/DBT OK; hooks definidos; evidência atualizada.  
- **Pré‑deploy**: canary/shadow; dashboards alinhados; runbooks à mão.  
- **Pós‑deploy (24 h)**: watchers verdes; *post‑deploy review*.

---

## 24) Glossário & Convenções
- **Bases**: ACT/360 (FX), ACT/365F (pools), 30E/360 (bonds).  
- **Unidades**: %, bps, p.p., moeda; **pips** (FX).  
- **Eventos**: `proposal.created`, `eligibility.passed`, `price.computed`, `offer.accepted`, `hook.triggered`.

---

## 25) ADRs Abertos (resumos)
- **ADR‑001**: Cap de Δpreço diário por SKU.  
- **ADR‑002**: Política de *cooldown* para aumento de limite.  
- **ADR‑003**: Critério de *haircut* para `fx_basis` ausente.

---

## 26) Golden Notebooks (catálogo)
- **GN‑CIP‑FX**: verificação CIP + *TWAP failover*.  
- **GN‑DRIFT‑ML**: cálculo de PSI/KS e rollback controlado.  
- **GN‑PRICING‑SPREAD**: sanity checks de monotonicidade e caps.



---

## 27) Tesouraria & Liquidez (A24–A33)
- **Objetivo**: garantir funding ao menor custo, com estabilidade sob stress.  
- **Políticas**:  
  1) **Ladder de liquidez** por tenores (D, W, M, Q); *duration matching* com passivos.  
  2) **Concentração**: HHI portfólio ≤ alvo; *headroom* por emissor/rota.  
  3) **Cap de exposição** por provedor/rota.  
- **Leilões**: rotina diária de *clearing* (P2), *fill ≥ 90%*; fallback para cotas internas.  
- **Hooks**: `fill<90%•24h->review_params; owner=PMO` | `hhi>alvo•once->throttle_volume; owner=TSR`.

## 28) Pools & Cupom (ACT/365F)
- **Cupom** como média ponderada por `capital×tempo`; bases **ACT/365F**; rounding em **bps**; trilha de cálculo por evento.  
- **Invariantes**: sem arbitragem entre janelas; *carry* explícito; monotonicidade da *exposure*.  
- **Hooks**: `pool_coupon_deviation>ε•run->pause_reprice; owner=TSR`.

## 29) Proveniência & Attestations
- **Merkle root** por *batch* (`pricing_events`, `oracle_ticks`) e **carimbo RFC‑3161** opcional.  
- **Traceability Bridge**: `trace_id ↔ audit_id ↔ contract.version ↔ GN`.  
- **Gate**: sucesso dos **Golden Notebooks** é pré‑requisito de Go/No‑Go.  
- **Hook**: `gn_fail•run->block_release; owner=SRE`.

## 30) Human‑in‑the‑Loop (HITL) & Exceções
- **Quando aciona**: fraude alta, sinal de dados conflitante, *model uncertainty*, risco jurídico.  
- **Cotas** por squad e **SLA** para resolver; decisões manuais registradas com **ACE** e `audit_id`.  
- **Hooks**: `sop_exception_storm•5m->spin_up_review; owner=OPS` | `decision_cycle_slip>target•3x->load_shed; owner=OPS`.

## 31) Adverse Action & Explicabilidade
- **Obrigatório**: lista de razões (policy/model) entregue ao solicitante; *counterfactuals* quando cabível.  
- **Retenção**: ≥ 5 anos; **RBAC** e mascaramento.  
- **Hook**: `explain_gap>0•run->block_promotion; owner=ML`.

## 32) Fairness & Bias
- **Guard‑rail** operacional: **Gini ≤ 0,25**; *bias audit* periódico; proibição de proxies sensíveis.  
- **Hook**: `gini>0.25•24h->pause_experiment; owner=ML`.

## 33) Portfolio & Concentration Risk
- **Limites** por indústria/segmento/produto; **HHI** monitorado; *headroom* dinâmico por risco/margem.  
- **Hook**: `concentration>limit•once->throttle+reprice; owner=RSK`.

## 34) Stress Testing & Overlays
- **Cenários**: curvas de inadimplência, choque de FX, queda de funding.  
- **Overlays**: *add‑ons* temporários no spread/limite quando cenário ativo.  
- **Hook**: `stress_mode=on->apply_overlay; owner=RSK`.

## 35) Integrações — SLAs & Penalidades
- **SLAs** por provedor (p95, uptime); **penalidades** por violação material; *circuit breaker* automático.  
- **Hook**: `provider_slo_breach•run->circuit_breaker; owner=INT`.

## 36) Sandbox, Dados Sintéticos & Migracões
- **Sandbox** obrigatório para novos SKUs/rotas; **dados sintéticos** com sementes determinísticas; **migrações** com *plan* versionado.  
- **Hooks**: `db_version_major->require_migration_plan; owner=DATA`.

## 37) Segurança Cripto & Chaves (A102)
- **Assinaturas**: ECDSA/EdDSA/BLS conforme caso; **rotação ≤ 90 dias**; *supply chain* sem regressões de CVE.  
- **Hooks**: `idp_keys_rotation>90d->raise_issue; owner=SEC` | `image_vuln_regression>0->block_merge; owner=SEC`.

## 38) Feature Flags & Release
- **Flags** por rota/SKU; *canary/shadow* com rollback automático; *freeze* por **error‑budget burn**.  
- **Hooks**: `error_budget_burn>2x•1h->freeze_release; owner=SRE`.

## 39) Oráculos — Heartbeats & Desvios
- **Heartbeats** e **TWAP**; *deviation threshold* por par.  
- **Hook**: `price_deviation>threshold•1m->switch_to_twap_failover; owner=BC`.

## 40) FX — Calendários & CLS
- **Calendários** sincronizados; *CLS pay‑in/out* monitorado; execução fora de janela bloqueia *route*.  
- **Hook**: `missed_payin_cutoffs>0•run->block_route; owner=BC`.

## 41) Cache & TTL
- **TTL mínimo** por recurso crítico; **429** com `Retry‑After`; *negative caching* só com *circuit breaker*.  
- **Hook**: `cache_ttl<10s•run->policy_violation; owner=PLAT`.

## 42) Runtime & Dependências
- **EOL** de runtime bloqueia release; **vulns** altas = **No‑Go**.  
- **Hooks**: `runtime_eol•once->block_release; owner=PLAT` | `dep_vuln_high>0->block_merge; owner=SEC`.

## 43) OKRs — Mapeamento Operacional
- **NSM** ligado a *KRs* por domínio (DEC, DATA, ML, PM, PLAT).  
- **Painel** mantém `KPI→Hook→Owner` e *estado* (OK/DEGRADED/ROLLED_BACK).

## 44) Quórum & Aprovações
- **Quórum mínimo** por mudança material: Produto + Engenharia + Dados + Risco; **waiver** só com prazo+rollback.  
- **Hook**: `missing_quorum•once->block_release; owner=PO`.

## 45) Disputas & Chargebacks
- **Regra**: canal de disputa com *SLA* definido; *evidence* automatizada; *chargeback* recorrente eleva *friction tier*.  
- **Hook**: `chargeback_ratio>target•W->raise_investigate; owner=COL`.

## 46) Repricing & Ofertas Ativas
- **Repricing** por eventos (risk, funding, FX) e janela mínima; **cooldown** entre ofertas para evitar *ping‑pong*.  
- **Hook**: `offer_churn>ε•D->cooldown+throttle; owner=PMO`.

## 47) Documentos & Identidade
- **KYC**: documento válido, *liveness*, *device fingerprint* coerente; **watchlists** (sanções) limpas.  
- **Hook**: `kyc_fail•once->deny; owner=SEC`.

## 48) Compliance & Privacidade
- **LGPD**: minimização, base legal, direitos do titular; **auditoria** periódica.  
- **Hook**: `dp_budget_breach•run->freeze; owner=SEC`.

## 49) Métricas de Saúde de Fila & Headroom
- **Headroom** mínimo CPU/Mem ≥ 30%; fila p95 ≤ 10 s; *back‑pressure* com shed.  
- **Hook**: `capacity_headroom<30%•5m->shed_load; owner=SRE`.

## 50) Tabelas Canônicas & Eventos
- `pricing_events`, `oracle_ticks`, `fx_quotes`, `cdc_offsets` — chaves, schemas e compatibilidade backward; **dbt** como teste de contrato.  
- **Hook**: `schema_incompatible_ratio>0->rollback; owner=DATA`.



---

## 51) Contratos de Dados (A106/A87/A89) — Especificação Operacional
**Princípios**: versionamento semântico; compatibilidade backward; `idempotency_key`; `schema_registry`; testes **dbt** obrigatórios.

### 51.1 Objetos Canônicos (JSON Schema — resumo)
**proposal.v1**
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "proposal.v1",
  "type": "object",
  "required": ["proposal_id","applicant_id","ts","inputs"],
  "properties": {
    "proposal_id": {"type":"string","pattern":"^prp#[a-zA-Z0-9_-]+$"},
    "applicant_id": {"type":"string"},
    "ts": {"type":"string","format":"date-time"},
    "inputs": {"type":"object","required":["income","dsti"],"properties":{
      "income": {"type":"number","minimum":0},
      "dsti": {"type":"number","minimum":0,"maximum":1}
    }},
    "channel": {"type":"string","enum":["web","mobile","api"]},
    "context": {"type":"object"}
  }
}
```
**pricing_event.v1**, **oracle_tick.v1**, **cdc_offsets.v1**, **audit_log.v1** seguem padrão similar (ids, `ts`, `trace_id`, `audit_id`, `contract.version`).

### 51.2 Testes Obrigatórios (dbt)
- `unique`/`not_null`/`accepted_values`/`relationships`/`freshness` em **todas** as tabelas canônicas.  
- **CI** bloqueia *merge* se `schema_registry_drift` ou `data_contract_break` > 0.

---

## 52) CDC & Linhagem (A105/A88)
- **Debezium** ou equivalente; *snapshot* inicial controlado; **lag p95 ≤ 120 s**.  
- **Idempotência** por `(event_id, feed_id)`; *replay* determinístico; *lineage* completo.

---

## 53) Observabilidade (A71–A72) — OTel Padrão
- **Spans**: `decision.core`, `pricing.compute`, `oracle.fetch`, `cdc.read`, `dbt.run`, `hook.trigger`.  
- **Atributos**: `trace_id`, `audit_id`, `pack_id`, `model_version`, `hook_id`, `latency_ms`, `status`.  
- **Eventos**: `slo.violation`, `rollback.apply`, `waiver.issue`.  
- **Regras**: amostragem ≥ 1%; cardinalidade controlada; logs correlacionados.

---

## 54) Model Serving (A81)
- **Artefato** (ex.: ONNX): versionado; *checksum*; *feature store* compatível.  
- **SLOs**: p95 ≤ alvo; *timeouts/retries* explícitos; *dynamic batching* quando suportado.  
- **Rollout**: `shadow → canary → full`, com *abort* por hook.

---

## 55) Experimentação (A83)
- **SRM obrigatório**; *power* ≥ 80%; *sequential tests* onde cabível; CUPED opcional.  
- **Guardrails**: perda de receita/risco; *auto‑pause* por falha de SRM.  
- **Evidência**: `experiment_id`, `allocation`, `p_value`, `srm_flag` nos logs.

---

## 56) Drift & Saúde de Modelo (A84)
- **PSI/KS** por **feature** e **score**; janela 24 h; *winsorize* opcional para outliers.  
- **Ação**: `psi>0.2` → `rollback_model`; `ks>0.1` → `degrade_policy`.

---

## 57) Formal Verification & Invariantes (A103)
- **Propriedades**: monotonicidade (∂spread/∂PD≥0), ausência de arbitragem no preço, paridade **C−P** quando aplicável.  
- **Gate**: `formal_verification_gate_watch=ok` antes de promover.

---

## 58) Oráculos & Mercado (A104)
- **Heartbeats** + **TWAP/EWMA**; `staleness<30s`; divergência cross-feed monitorada.  
- **Failover**: `switch_to_twap_failover` por hook; *jitter* e *time alignment* obrigatórios.

---

## 59) FX (A98–A100) — Regras
- **Conveções**: *spot/forward/premium*; base ACT/360; pips/bps; *CLS cutoffs*.  
- **Paridade**: `F = S * (1+r_d*T)/(1+r_f*T)`; **rounding** em pips; limites de desvio.  
- **Roteamento**: multi‑provedor com *toxicity filters* (ex.: VPIN) quando habilitado.

---

## 60) Segurança & Privacidade (A77/A108)
- **PII**: minimização e mascaramento; *data retention* por classe de dado; **DLP** em trânsito/repouso.  
- **Chaves/segredos**: rotação ≤ 90d; *supply chain* sem regressões de CVE.  
- **DP Budget**: `epsilon_burn_rate` monitorado; *freeze* automático em violação.

---

## 61) OKRs & Governança (A109)
- **NSM** ligado a *KRs* por domínio; **revisão mensal**; *error‑budget freeze*.

---

## 62) Experiência (A74–A80) — Regras de UX
- **3 telas** por jornada (Originação/Oferta/Confirmação); *skeletons* e *optimistic UI*.  
- **A11y** AA; textos humanizados; `trace_id` para suporte (mascarado).  
- **INP p75 ≤ 200ms** com *rollback* se piorar 24h.

---

## 63) Integrações (Bureaus/Provedores)
- **SLAs**: p95 e uptime; **penalidades** por violação; *retry/idempotency*; *circuit breaker* por provedor.  
- **Auditoria**: logs com `provider_id`, `latency`, `status`, `cost`.

---

## 64) Incidentes & Runbooks
- **Cenários**: oráculo fora, drift severo, schema drift, degradação de latência, vazamento.  
- **Passos mínimos**: detectar→isolar→mitigar→rollback→postmortem (ações sem atraso).  
- **SLO**: *tabletop* ≤ 90d, *DR drill* ≤ 180d.

---

## 65) Release & Flags
- **Pré‑merge**: contratos/DBT OK; hooks definidos; *security checks* pass.  
- **Pré‑deploy**: canary/shadow + dashboards;  
- **Pós‑deploy 24h**: watchers verdes; *freeze* se `error_budget_burn>2x`.

---

## 66) API v1 — Contratos
- **Headers**: `Idempotency-Key`, `X-Trace-Id`, `X-Client-Version`.  
- **Endpoints** (resumo):  
  - `POST /v1/proposals` — cria proposta.  
  - `POST /v1/pricing/:proposal_id` — calcula preço.  
  - `GET /v1/offers/:proposal_id` — consulta oferta.  
  - `POST /v1/offers/:id/accept` — aceita oferta.  
  - `GET /v1/audit/:audit_id` — auditoria.  
- **Status**: 200/201/202/4xx/5xx com taxonomia padronizada.  
- **Idempotency TTL**: ≥ 24h; *retry‑safe*.

---

## 67) Rate Limits & Quotas
- **Por parceiro/SKU**; *soft/hard limit*; **429** com `Retry‑After`; *dynamic throttling* por risco/custo.

---

## 68) Retenção & Direito do Titular
- **Retenção**: decisões/leilões ≥ 5 anos; *privacy request* com SLA; *erasure* onde legalmente aplicável; trilha de deleção.

---

## 69) Portais Internos & Acesso
- **SSO**; RBAC por domínio (DEC/DATA/ML/PM/PLAT/FE/SEC/INT); *break‑glass* auditado; *session hardening*.

---

## 70) Guardrails de Preço & Rollback
- **Caps**: Δpreço diário ≤ X bps; **freeze** por volatilidade anômala; auditoria automática em “saltos”.

---

## 71) Multi‑Tenancy & Isolamento
- **Isolamento** lógico por tenant; `encryption at rest` por tenant; quotas dedicadas; *blast radius* limitado.

---

## 72) Custos & Orçamento
- **Orçamentos** por domínio (cloud/bureaus/mercado); *watchers* de custo; *degrade* automático acima do teto.

---

## 73) Performance & Capacidade
- **Headroom** CPU/Mem ≥ 30%; fila p95 ≤ 10 s; *autoscaling* com *warm‑pool*; *load shedding* progressivo.

---

## 74) Localização & Calendários
- **FX/CLS** e feriados regionais; janelas de operação; *fallback* fora de janela.

---

## 75) Golden Notebooks — Catálogo Expandido
- **GN‑CIP‑FX**, **GN‑DRIFT‑ML**, **GN‑PRICING‑SPREAD**, **GN‑CDC‑REPLAY**, **GN‑FORMAL‑INVARIANTS** — todos com `hash`, dados sintéticos e *plots*.

---

## 76) ADRs — Índice & Status
- **ADR‑001** (cap Δpreço), **ADR‑002** (cooldown limite), **ADR‑003** (haircut fx_basis), **ADR‑004** (policy fairness), **ADR‑005** (CLS janela), **ADR‑006** (privacidade/logs).  
- Cada ADR com **ACE/DoR/DoD**, owners, rollback e packs citados.

---

## 77) Biblioteca de Hooks A110 (export — trecho)
```yaml
hooks:
  - id: dec.latency.degrade
    when: latency.p95>800ms
    window: 5m
    action: degrade_route
    owner: SRE
    rollback: yes
  - id: data.cdc.degrade
    when: cdc_lag.p95>120s
    window: 5m
    action: degrade_route+open_ticket
    owner: DATA
    rollback: yes
  - id: ml.drift.rollback
    when: psi>0.2
    window: 24h
    action: rollback_model
    owner: ML
    rollback: yes
  - id: ab.srm.pause
    when: srm_fail==true
    window: run
    action: pause_experiment+audit
    owner: ST
    rollback: n/a
  - id: oracle.stale.failover
    when: staleness>30s
    window: 5m
    action: twap+failover
    owner: BC
    rollback: yes
  - id: fe.inp.rollback
    when: cwv_inp.p75>200ms
    window: 24h
    action: rollback_release
    owner: FE
    rollback: yes
  - id: sec.dp.freeze
    when: privacy_budget_epsilon_burn_rate>1.5x
    window: 1h
    action: freeze
    owner: SEC
    rollback: yes
  - id: plat.trace.block
    when: tracing.sample_rate<1%
    window: 15m
    action: block_release
    owner: SRE
    rollback: yes
  - id: api.contract.block
    when: contract_tests_fail_pct>0
    window: run
    action: block_release
    owner: PLAT
    rollback: yes
  - id: treasury.hhi.throttle
    when: hhi>target
    window: once
    action: throttle_volume
    owner: TSR
    rollback: yes
```

---

## 78) Backlog PO‑Ready — Estrutura (amostra)
- **HIST‑DEC‑001**: “Como solicitante, quero receber uma decisão <0.8s p95…” — **ACE/DoR/DoD**, watchers, hook `dec.latency.degrade`.  
- **HIST‑DATA‑004**: “Como Eng. Dados, quero `schema_registry` com testes dbt…” — hook `api.contract.block`.  
- **HIST‑ML‑010**: “Como Cientista, quero rollback automático por PSI>0.2…” — hook `ml.drift.rollback`.

---

## 79) Matriz Completa Requisito↔Pack↔Watcher↔Hook↔Owner
- Publicada como **tabela operacional** acoplada ao backlog/OKRs (export CSV/JSON).  

---

## 80) Encerramento (Pearl × Jobs × Meadows)
- **Pearl**: causalidade viva (DAGs revisados; contrafactuais nos Goldens).  
- **Jobs**: simplicidade agressiva (menos telas/variantes; linguagem humana).  
- **Meadows**: alavancas de sistema (headroom, delays, loops) conectadas a hooks.



---

## 81) Políticas por Produto (Revolving / Parcelado / BNPL / Colateralizado)
- **Revolving (cartão/conta)**: avaliação contínua; **overlimit** apenas com política explícita e *cooldown*; juros compostos com teto/regra local.  
- **Parcelado**: Tabela Price/SAC; CET exibido; amortização mensal; **vencimento** adaptado ao calendário local.  
- **BNPL**: parcelas curtas (3–6); juros 0% com subsídio/custo; *merchant discount rate* explícito.  
- **Colateralizado**: **LTV** por ativo; *haircut* dinâmico; *margin call*; leilão de colateral com regras anti‑sniping.  
- **Hooks**: `overlimit>ε->block+notify (DEC)` • `ltv>limit->margin_call (RSK)` • `mdr_below_floor->block_offer (PMO)`.

## 82) Amortização, Juros & Alocação de Pagamento
- **Base**: ACT/365F; arredondamento em bps; juros **não** incidem sobre juros pausados por lei.  
- **Ordem de alocação**: encargos → juros → principal → fees residuais.  
- **Hook**: `accrual_policy_violation•run->block_settlement; owner=FIN`.

## 83) Taxas & Encargos (Fees)
- **Origination** com teto; **late fee** com *grace*; **overlimit fee** opcional; **refund** pró‑rata.  
- **Regra**: publicar CET/TAEG; usura/regulatórios por jurisdição.  
- **Hook**: `fee_cap_breach•run->block_release; owner=FIN`.

## 84) Carência, Feriados & Payment Holidays
- **Carência**: até N dias conforme SKU; accrual pausado quando exigido.  
- **Calendário**: feriados/CLS; mudança automática de vencimento fora de janela.  
- **Hook**: `due_date_out_of_window•run->shift_due; owner=OPS`.

## 85) Pré‑pagamento & Quitação
- **Sem multa** onde lei exigir; senão tabela de *prepayment* publicada.  
- **Hook**: `prepay_request•once->recompute_CET; owner=FIN`.

## 86) Charge‑off & Write‑off
- **DPD**: políticas por SKU (ex.: 120/180/360); *non‑accrual* a partir de S3.  
- **Hook**: `dpd>=policy•once->charge_off; owner=FIN`.

## 87) Provisão & ECL (IFRS 9/CECL)
- **Estágios**: S1 (12m ECL), S2 (lifetime ECL), S3 (impaired).  
- **Inputs**: PD/LGD/EAD por cenário; overlays de stress.  
- **Hook**: `ecl_spike>threshold•run->apply_overlay; owner=FIN`.

## 88) Reconhecimento de Receita & Non‑accrual
- **Regra**: parar accrual em S3/charge‑off; *interest reversal* conforme política.  
- **Hook**: `non_accrual_breach•run->reverse_interest; owner=FIN`.

## 89) Cobrança — Estratégias & Tratamentos
- **Buckets** por DPD; cadência omni‑canal; *hardship* e renegociação.  
- **Segmentação**: risco, propensão a pagar, custo de contato.  
- **Hook**: `dpd>=60•once->block_new_credit; owner=COL`.

## 90) Renegociação & Hardship
- **Opções**: alongamento, desconto, pausa temporária; trilha legal.  
- **Hook**: `hardship_flag=true->offer_plan; owner=COL`.

## 91) Seguros & Garantias
- **CP/Seguro**: opt‑in explícito; sinistro com fluxo auditável; *claim ratio* monitorado.  
- **Hook**: `claim_ratio>cap•M->repricing; owner=FIN`.

## 92) Parceiros & Revenue Share
- **Floor** de margem por SKU; MSA/SLAs; contra‑gaming de campanha.  
- **Hook**: `revenue_share_mismatch•run->block_payout; owner=FIN`.

## 93) Campanhas & Promoções
- **Elegibilidade**: segmentos, cooldown; **anti‑churn ping‑pong**.  
- **Hook**: `offer_churn>ε•D->cooldown; owner=PMO`.

## 94) Lifecycle & CRM (Upsell/Retenção)
- **Triggers**: aumento de renda, *green flags*, *declining risk*; cross‑sell ético (fairness).  
- **Hook**: `churn_risk>τ•W->retention_play; owner=GTM`.

## 95) Risco de Terceiros & Due Diligence
- **Vendors**: SOC2/ISO; DPA; *pen tests*; relatórios periódicos.  
- **Hook**: `vendor_audit_overdue•run->suspend_access; owner=SEC`.

## 96) Compliance por Geografia
- **Matriz**: usura, CET/TAEG, direito à portabilidade, disclosure.  
- **Hook**: `reg_update•once->policy_review; owner=LEGAL`.

## 97) Model Risk Management (MRM)
- **Independência**: validação externa de modelos/material; periodicidade; *model cards*.  
- **Hook**: `model_risk_doc_gap>0->block_release; owner=MRM`.

## 98) Overrides Manuais & 4‑Eyes
- **Override**: permitido sob regras; **dupla aprovação**; ACE + trilha.  
- **Hook**: `override_without_dual•run->revoke; owner=OPS`.

## 99) Orçamento de Dados & Custos de Terceiros
- **Budget** por parceiro/consulta; *throttling* em excesso; *kill‑switch*.  
- **Hook**: `data_cost_burn>cap•D->throttle; owner=FIN`.

## 100) Qualidade de Dados — SLAs por Campo
- **Null%** e **freshness** por campo crítico; `accepted_values` e *relationships*.  
- **Hook**: `null_rate>threshold•run->block_promotion; owner=DATA`.

## 101) Streaming — Exactly‑Once & Dedup
- **Chaves**: `(event_id, feed_id)`; *idempotent sinks*; *replay* determinístico.  
- **Hook**: `dup_events>ε•5m->isolate_stream; owner=DATA`.

## 102) Backtesting & Champion‑Challenger
- **Backtests** com janelas *out‑of‑time*; roll‑down; *champion/challenger*.  
- **Hook**: `challenger_worse•run->halt_promotion; owner=ML`.

## 103) Simulação & Shadow Traffic
- **Shadow** antes de *full*; **simulações** com dados sintéticos; GNs cobrindo caminhos críticos.  
- **Hook**: `gn_fail•run->block_release; owner=SRE`.

## 104) Securitização & Loan Sales
- **Eligibility**: trilha, tape padrão, *reps & warranties*; exclusões (fraude, charge‑off recentes).  
- **Hook**: `tape_quality_breach•run->hold_sale; owner=TSR`.

## 105) ALM/FTP & Funding Cost
- **FTP** por tenor/risco; piso de taxa; *pass‑through* transparente.  
- **Hook**: `ftp_gap>bps•W->reprice; owner=FIN`.

## 106) Impostos & Relato Fiscal
- **Tributos** por produto; IOF/VAT onde aplicável; conciliação diária.  
- **Hook**: `tax_mismatch•run->block_settlement; owner=FIN`.

## 107) Comunicação Legal & Consentimentos
- **Templates** versionados; consentimentos auditáveis; *opt‑out* claros.  
- **Hook**: `missing_disclosure•run->block_offer; owner=LEGAL`.

## 108) Inclusão & Fair Lending
- **Proibições** de proxies sensíveis; **bias audits**; linguagem acessível.  
- **Hook**: `bias_metric>cap•24h->pause; owner=ML`.

## 109) On‑Call, Severidades & MTTR
- **Sev** 1–4, *paging* 24×7; MTTA/MTTR objetivos; *blameless* PM.  
- **Hook**: `slo_budget_burn>2x•1h->freeze_release; owner=SRE`.

## 110) Política de SLO/SLI & Burn Rate
- **Orçamento** por serviço; *burn*>2× congela *release*; *error budgets* visíveis.  
- **Hook**: `error_budget_burn>2x•1h->freeze; owner=SRE`.

## 111) Segredos & HSM
- **KMS/HSM**; *rotation* ≤ 90d; escopo mínimo.  
- **Hook**: `idp_keys_rotation>90d->raise_issue; owner=SEC`.

## 112) PenTests & Bug Bounty
- **Janela**: semestral; *triage* e SLA por severidade; CVE feed automação.  
- **Hook**: `sev_high_regressions>0->block_merge; owner=SEC`.

## 113) DR & Geo‑Redundância
- **RTO/RPO** por serviço; *tabletop* ≤ 90d; *DR drill* ≤ 180d; *runbooks*.  
- **Hook**: `bcdr_test_overdue->raise_issue; owner=SRE`.

## 114) Performance & Load Tests
- **Orçamentos** de CPU/mem/IO; testes de carga por rota; *warm‑pool*.  
- **Hook**: `capacity_headroom<30%•5m->shed_load; owner=SRE`.

## 115) FinOps & Unit Economics
- **KPIs** por SKU (CAC/LTV/COGS) e *cloud cost per decision*; *alerts* por desvio.  
- **Hook**: `unit_cost>cap•W->degrade; owner=FIN`.

## 116) Retenção & Arquivamento
- **Classes** de dados e prazos; *legal hold*; *WORM* onde exigido.  
- **Hook**: `retention_policy_violation•run->block_delete; owner=LEGAL`.

## 117) E‑Discovery & Busca
- **Índices** por `audit_id/trace_id`; *chain‑of‑custody*.  
- **Hook**: `audit_search_gap•run->reindex; owner=OPS`.

## 118) Relacionamento com Reguladores
- **Cadência** de reporte; *early warning* para mudanças materiais; visitas técnicas.  
- **Hook**: `reg_request•once->prepare_dossier; owner=LEGAL`.

## 119) Ética & Conduta
- **Código** público; revisão de políticas; *kill switch* para práticas indevidas.  
- **Hook**: `ethics_violation•run->freeze_feature; owner=PO`.

## 120) Decomissionamento & Sunset
- **Planos** de migração, *data export*, *customer notice*; remoção segura de chaves/dados.  
- **Hook**: `sunset_without_export•run->block; owner=PLAT`.



---

## 121) Princípio‑guia: **Intermediação 100%** (core)
- **Regra**: CE **não** define taxa, **não** faz *market making*, **não** toma risco de balanço. Orquestra **RFQ/leilões/roteamento/liquidação** com **evidence** assinada e auditável.
- **Consequências**: todo preço deve referenciar **fonte externa** (ordens, cotações, leilões) ou **regras de best‑ex**. Sem fonte → **no‑go**.
- **Hooks**: `intermediacao_deviation•once->freeze_flow; owner=PO` | `best_ex_breach•run->halt_route; owner=PMO`.

## 122) Defaults Operacionais — Best‑Ex, SLOs & Eventos
- **Best‑Ex**: ≥ 3 cotações válidas; **single‑price** com alocação *pro‑rata*; **book price‑time**; eventos **EIP‑712** em toda trilha.  
- **SLOs de referência**: Decisão p95 ≤ 500ms; **Time‑to‑Fund** ≤ 2h (permissionado) / ≤ 1d (TradFi); **Settlement accuracy** ≥ 99,98%; **Fill‑rate** por família ≥ 85–95%.  
- **Hooks**: `fill_rate<85%•D->leilao_param_review; owner=PMO` | `settlement_miss>0.02%•D->reconcile+halt; owner=OPS`.

## 123) Watchers Baseline v13 & Linter (CI‑gates)
- **Obrigatório** em **todas** as features: `decision.latency`, `cdc.lag`, `oracle.staleness`, `model.psi|ks`, `ab.srm`, `web.inp`.  
- **CI**: regra `watcher_baseline_ok` bloqueia PR sem baseline.  
- **Hooks**: `baseline_missing•run->block_merge; owner=PO` | `evidence_min3_missing•run->block_merge; owner=PO`.

## 124) Doc‑Ops — Evidence mínima & Pipeline
- **Evidence mínima por feature (3)**: `trace_id`, `audit_id`, `adr_id` (+ `feature_id`, `hook_id`, `occurred_at`, `result`).  
- **Pipeline (CI)**: pré‑merge → lints (OpenAPI, contratos, hooks, evidence); pré‑deploy → *canary/shadow*; pós‑deploy → publicação **rastreabilidade 360°**.  
- **Hooks**: `doc_tests_fail•run->block_release; owner=PO`.

---

## 125) Superfície de Produto — PF (herda defaults)
- **Pessoal/consignado/overdraft/cartão/BNPL/veículos/imobiliário/salário/microcrédito/estudantil/leasing/SBL/margin/HEA/embedded PF**.  
- **Regras comuns**: elegibilidade/KYC; **CET** exposto; DSTI/LTV conforme SKU; **anti‑churn ping‑pong**; *chargeback* monitorado; **Time‑to‑Fund** por linha.  
- **Hooks**: `ltv>limite•once->margin_call; owner=RSK` | `chargeback_ratio>alvo•M->investigate; owner=COL`.

## 126) Superfície de Produto — PJ/SME/Corporate
- **Giro/limites/AR discount/confirming/RCF/term/unitranche/mezanino/bridge/project/ABL/warehouse/forfaiting/floorplan/commodities/fund finance/B2B BNPL**.  
- **Regras**: covenants explícitos; *eligibility tape* por título; **headroom** por âncora/fornecedor; testes OC/IC onde couber.  
- **Hooks**: `covenant_breach•once->freeze_draw; owner=OPS` | `supplier_concentration>limite•D->throttle; owner=RSK`.

## 127) Trade Finance
- **LC/SBLC/aval/cobrança doc./ACC/ACE/warehouse receipts/tolling/off‑taker/dynamic discounting**.  
- **Regras**: *docs & discrepancies*; *expiry windows*; *country risk*; *off‑take* obrigatório quando aplicável.  
- **Hooks**: `lc_discrepancy>ε•run->review; owner=OPS` | `expiry_breach•run->halt; owner=OPS`.

## 128) Mercado de Capitais — Dívida
- **Bonds/debêntures/CP/MTN/CRI/CRA/FIDC/LIG/AT1/municipal/SLL/SLB**.  
- **Regras**: *bookbuilding* ou RFQ com trilhas; *ratchets ESG* onde aplicável; **waterfall**/eventos pós‑negócio.  
- **Hooks**: `book_health<alvo•run->adjust_allocation; owner=PMO` | `oc_ic_fail•run->halt_cashflow; owner=TRUST`.

## 129) Securitização & Estruturados
- **ABS/RMBS/CMBS/CLO/CDO/Marketplace ABS/NPL/Whole business/Re‑REMIC/CLN/COE/structured deposits/certificates**.  
- **Regras**: **pool tests** (OC/IC), tape padrão, **servicing** e reconciliação; *tranches* e eventos.  
- **Hooks**: `pool_test_fail•run->block_distribution; owner=TRUST`.

## 130) Money Market & Funding
- **CDB/LC/LCI/LCA/CDs/CP/ECP/repos/securities lending/collateral upgrades/tri‑party/CCS funding/janelas BC**.  
- **Regras**: *best‑ex* e *no‑arb* com curvas; vínculo a pipeline de loans quando financiado via captação.  
- **Hooks**: `best_ex_violation•run->reroute; owner=TSR`.

## 131) Derivativos de Crédito
- **CDS single‑name/índice/tranches/LCDS/TRS/opções/CSO/OTRS/quanto**.  
- **Regras**: ISDA/CSA; eventos de crédito; *marks* e *rolls*.  
- **Hooks**: `credit_event_detected->hedge_execute; owner=RSK`.

## 132) Derivativos de Juros & FX (hedge)
- **Swaps DI/fixo, CCS, FX fwd/swap, futuros, opções**.  
- **Regras**: *duration gap* e *basis* monitorados; **best‑ex** e latência por rota.  
- **Hooks**: `basis_out_of_band•1h->rebalance; owner=TSR`.

## 133) Web3 — Lending & Borrowing
- **Pools sobrecolateralizados/permissionados/LRT‑LP/NFT/RWA on‑chain/intents RFQ**.  
- **Regras**: **whitelist/KYC**; *proofs* e **PoR**; **haircuts** dinâmicos; segregação 1:1 quando exigida.  
- **Hooks**: `depeg•run->halt_routes; owner=BC` | `proof_stale•run->freeze; owner=SEC`.

## 134) Derivativos cripto/tokenizados
- **Perp/Futuros/Opções/Swaps funding/TRS/power‑perps/vol tokens**.  
- **Regras**: *greeks* e barreiras; funding/index *watchers*; **RWA** como hedge quando aplicável.  
- **Hooks**: `funding_spike•5m->reduce_leverage; owner=TSR`.

## 135) RWA — Tokenização de Dívida/Recebíveis
- **T‑bills tokenizados/invoices/FIDC quotas/NPL tokens/Home equity tokens**.  
- **Regras**: lastro validado; **NAV/waterfall**; cessão e eventos; **LGPD/KYC**.  
- **Hooks**: `nav_divergence>ε•run->halt_issuance; owner=TRUST`.

## 136) Stablecoins & Colateral Digital
- **Fiat‑backed/cripto‑colateralizadas/algorítmicas/commodity/RWA‑backed/yield‑bearing/CBDC como *rail***.  
- **Regras**: **PoR**, *whitelist*, limites e *tracking*; uso restrito por política onde aplicável.  
- **Hooks**: `peg_break•5m->halt_route; owner=TSR` | `por_gap•run->freeze; owner=SEC`.

## 137) Infra de Garantias Colateralizadas
- **Registries/cartórios; tri‑party; CCPs; rehypothecation; otimização de colateral; vaults on‑chain; oráculos PoR; seguro de colateral; cross‑margin; oráculos de recovery**.  
- **Regras**: *allocations/substitutions*; segregação; *access control*; **SLA ingest** e provas.  
- **Hooks**: `margin_breach•run->margin_call; owner=RSK` | `por_fail•run->freeze; owner=SEC`.

## 138) Checklists de Completude (v4→v13)
- **Sem watcher** → **não libera**; **rollback** para qualquer quebra de schema; **SRM** falhou → pausar; **drift** alto → holdout.  
- **Checklist**: Bonds/Capitais ✓; Securitização ✓; Money Market ✓; Derivativos crédito/IR/FX ✓; Web3/DeFi ✓; Stablecoins ✓; Infra de Garantias ✓.

## 139) Rastreabilidade 360° — Mapeamento
- **Tabela operacional** (export CSV): _Feature → APIs/Contratos → Métricas (SLI/SLO) → Hooks (A110) → Evidence (≥3) → ADR → Runbooks → Statusboards_.  
- **Publicação** automática pós‑deploy; linter impede divergências.

## 140) Estados de Conformidade & Owners
- **Estado** por domínio (OK/DEGRADED/ROLLED_BACK); *owners* explícitos; **waivers** sempre com prazo e rollback.  
- **Hook**: `missing_owner•run->block_release; owner=PO`.

## 141) Anti‑Stacking Guard (PF/PJ)
- **Problema**: múltiplas originações simultâneas elevando risco de concentração.  
- **Regras**: sessão/identidade correlacionadas; *cooldown* por CPF/CNPJ; *credit stacking score*; bloqueio por *velocity*.  
- **Hooks**: `stacking_score>τ•1h->freeze_new_credit; owner=RSK` | `velocity_breach•15m->quarantine_session; owner=SEC`.

## 142) CLS Cutoff Guard (FX/liquidação)
- **Regras**: usar `planilhas/cls_calendar.csv`; impedir ordens fora de janela; reprogramar *pay-in/out*.  
- **Hook**: `cls_cutoff_violation•run->halt_route+notify; owner=OPS`.

## 143) Evidence JSON Linter (Doc‑Ops)
- **Regra**: validar com `schemas/evidence.v1.json` + **mínimo 3 evidências**/feature (`trace_id`, `audit_id`, `adr_id`).  
- **Hook**: `evidence_min3_missing•run->block_merge; owner=PO`.

## 144) Privacy Ledger & DPIA (LGPD)
- **Regras**: ledger de consentimentos; DPIA/ROPA por feature; *data mapping* por contrato (A106).  
- **Hook**: `dp_budget_breach•run->freeze; owner=SEC`.

## 145) Fees Policy (hash) & Timelock
- **Regras**: política de taxas versionada com **hash**; mudanças por **timelock 72h** e *changelog* EIP‑712.  
- **Hook**: `fee_change_without_timelock•run->block_release; owner=FIN`.

## 146) Legal Doc Diff (hash)
- **Regras**: *diff* assinado (hash) por versão; vincular a proposal/offer; export auditável.  
- **Hook**: `legal_diff_missing•run->block_offer; owner=LEGAL`.

## 147) Statement API & Reconciliação/Payment Bus
- **APIs**: `/statements/*`, `/payments/*`, *webhooks idempotentes*; eventos `Payment.Event`.  
- **Regras**: reconciliação D+0 com **golden files**; *escrow* conciliado.  
- **Hook**: `recon_miss>0•D->halt_settlement; owner=OPS`.

## 148) Counterparty Due Diligence
- **Regras**: due diligence de parceiros (SOC2/ISO, DPA, sanções, seguro, SLA/penalidades).  
- **Hook**: `vendor_audit_overdue•run->suspend_access; owner=SEC`.

## 149) Split Optimizer (Fees)
- **Objetivo**: reduzir *fee‑drag* em rotas multi‑provedor; simular *splits* com restraints de contrato.  
- **Hook**: `fee_drag>cap•W->reroute_split; owner=PMO`.

## 150) Status Page + SLA
- **Regras**: publicar *statusboards* (NSM, CDC, Oráculos, CIP, Budgets, SRM, CWV, Settlement, Liquidity, Privacy).  
- **Hook**: `status_publish_fail•run->raise_issue; owner=SRE`.

## 151) Golden Files (APR/Auction/Waterfall/Idempotency)
- **Regras**: *goldens* versionados e reprodutíveis; gates de promoção dependem da execução dos *goldens*.  
- **Hook**: `golden_fail•run->block_release; owner=SRE`.

## 152) Default Orchestrator & NPL/Open Auction
- **Regras**: fluxo de *default* com *open auction* transparente; *rounds* justos; *waterfall* pós‑default.  
- **Hook**: `default_event•once->open_auction; owner=TRUST`.

## 153) Audit On‑Demand Exports
- **Regras**: export sob demanda (D+0) de trilhas completas (`audit_id`, `trace_id`, contratos, hooks, ADRs).  
- **Hook**: `audit_export_fail•run->raise_issue; owner=OPS`.

## 154) Concentration Heatmap & Anti‑Stacking Scenarios
- **Regras**: mapa de concentração por sacado/fornecedor/ativo; cenários de *stacking*.  
- **Hook**: `concentration>limit•once->throttle+reprice; owner=RSK`.

## 155) Onboarding & Consent — Fast‑Track
- **Regras**: KYC multi‑provedor; consent ledger; *fallback* de provedor; DSRs em D+0 via `/privacy/*`.  
- **Hook**: `kyc_fail•once->deny; owner=SEC`.

## 156) RFQ — Idempotency/Batch/Cancel/Amend/Sandbox
- **APIs**: `POST /rfq` com `Idempotency‑Key`; `/rfq/batch`; `/rfq/{id}/cancel|amend`; `/rfq/sandbox/*`.  
- **Hook**: `rfq_dup•5m->isolate_key; owner=PLAT`.

## 157) Eligibility Explain & Risk Explain
- **APIs**: `/eligibility/explain`, `/risk/explain` com razões e contrafactuais.  
- **Hook**: `explain_gap>0•run->block_promotion; owner=ML`.

## 158) Consent Revocation & Data Residency Guard
- **Regras**: revogação imediata; *data residency* por jurisdição.  
- **Hook**: `data_residency_breach•run->freeze; owner=SEC`.

## 159) Device Binding & Session Quarantine
- **Regras**: vínculo dispositivo; quarentena sob alerta de segurança/IDS.  
- **Hook**: `alert_storm•15m->quarantine_session; owner=SEC`.

## 160) ADR/CI Gates — Enforcement
- **Regras**: PR bloqueado sem ADR/esquemas/contratos; *pre‑deploy* e *post‑deploy* obrigatórios (Makefile/CI).  
- **Hook**: `ci_gate_fail•run->block_release; owner=PO`.



---

## 161) Data Clean Rooms (DCR) & Underwriting com Dados Sensíveis
- **Regra**: uso de **DCRs** para atributos sensíveis; contratos A106/ROPA/DPIA vinculados; *join* apenas por chaves *privacy‑preserving*; logs sem PII.  
- **SLO**: jobs ≤ janela acordada; *egress* zero.  
- **Hook**: `dcr_violation•run->halt_job+alert; owner=DATA`.

## 162) Proof‑of‑Reserve/Solvency (PoR)
- **Regra**: ingest de **PoR proofs** de custodians; frequência mínima; atestações assinadas; divergência → **freeze** das rotas afetadas.  
- **SLO**: `SLA proofs` dentro da janela; **evidence** anexada.  
- **Hook**: `por_gap•run->freeze; owner=SEC`.

## 163) Verifiable Events (EIP‑712)
- **Regra**: todos os eventos RFQ/clearing/settlement assinados (`LoanEvent{…}`) e encadeados por `prevHash`.  
- **Hook**: `signature_invalid•run->halt_flow; owner=PLAT`.

## 164) Pós‑negócio — Servicing, Trustees & SPV/SPE
- **Regra**: reconciliação D+0/D+1; relatórios a trustees com SLA; governança de **SPV/SPE** e segregação; *servicing waterfall*.  
- **Hook**: `servicing_report_sla_breach•run->raise_issue; owner=TRUST`.

## 165) Ratings & Pareceres Externos
- **Regra**: ingest de ratings/pareceres; divergência versus PD internos gera *flag*; periodicidade de atualização.  
- **Hook**: `rating_divergence>τ•run->review_model; owner=RSK`.

## 166) Crowdlending/P2P
- **Regra**: integração com plataformas; *best‑ex* mantido; *disclosures* e governança de suitability; intermediação 100% (CE não capta).  
- **Hook**: `p2p_suitability_gap•run->halt_route; owner=LEGAL`.

## 167) Ativos Sintéticos (TRS/CFD/Delta‑One)
- **Regra**: RFQ com marks consistentes; *CSA/margem*; VaR/mark‑out monitorados; sem mesa própria.  
- **Hook**: `var_spike•5m->reduce_exposure; owner=TSR`.

## 168) Structured Notes/Deposits/Certificates
- **Regra**: apenas **roteamento** (sem fabricação); *greeks* e barreiras auditadas; *best‑ex*; *tracking error* monitorado.  
- **Hook**: `barrier_event•run->hedge_rebalance; owner=TSR`.

## 169) Paying Agent, Escrow & Reconciliação
- **Regra**: APIs `/payments/*` e `/statements/*` com *webhooks* idempotentes; **golden files** D+0; *escrow* conciliado.  
- **Hook**: `recon_miss>0•D->halt_settlement; owner=OPS`.

## 170) Seguros & ECA
- **Regra**: anexar apólices (crédito, garantia, prestamista, mortgage/title, risco político) e **ECA cover** quando cabível; eventos de sinistro alimentam LGD.  
- **Hook**: `claim_ratio>cap•M->repricing; owner=FIN` | `eca_event•run->update_limits; owner=TRUST`.

## 171) Country Risk & Sanctions
- **Regra**: *exposure caps* por país/Âncora; *sanctions screening* contínuo e antes de cada liquidação.  
- **Hook**: `country_risk_level>cap•run->throttle; owner=RSK` | `sanction_hit•once->suspend; owner=SEC`.

## 172) ESG Ratchets (SLL/SLB)
- **Regra**: KPIs de sustentabilidade versionados; *ratchets* precificáveis (bps) com fórmula clara e janelas de medição; auditoria terceira parte.  
- **Hook**: `esg_kpi_miss•Q->ratchet_up; owner=FIN`.

## 173) Open Finance & Bureaus (PF/PJ)
- **Regra**: coleta *consented*; quotas e *retry‑after*; minimização (LGPD); *fallback* multi‑provedor.  
- **Hook**: `provider_fail•5m->fallback_route; owner=INT`.

## 174) Tributos — Pre‑Check & TaxCalc
- **Regra**: `/tax/indicative` para “surpresa zero”; conciliação de tributos no *settlement*; export fiscal.  
- **Hook**: `tax_mismatch•run->block_settlement; owner=FIN`.

## 175) Casos Extremos & Fallbacks
- **Regra**: taxas negativas; oráculo *stale*/gaps; *front‑running* mitigado com *commit‑reveal/batch*; *broken‑date* FX; injunções legais.  
- **Hook**: `extreme_case_trigger•run->activate_playbook; owner=SRE`.

## 176) Simulação & Monte Carlo (Pools/Tranches)
- **Regra**: simular trajetórias de PD/LGD, choques de σ, stress de FIFO e falhas de oráculo; outputs NAV/EL/UL/VaR por tranche; usar como **overlay** de política.  
- **Hook**: `simulation_var>cap•run->apply_overlay; owner=RSK`.



---

## 177) CIP & Rails de Pagamento (PIX/Boletos/STR)
- **Regras**: integração com **CIP** e rails regulados (PIX, boletos, STR/TED) com *cutoffs* e janelas de compensação; *idempotency* forte em `/payments/*`; reconciliação D+0 via **golden files**.  
- **SLO**: `settlement.miss_pct ≤ 0,02%` por dia; *retry with backoff* conforme rail.  
- **Hook**: `rail_cutoff_breach•run->halt_route+resched; owner=OPS` | `settlement_miss>0.02%•D->reconcile+halt; owner=OPS`.

## 178) SCA/3DS2 & Autenticação de Pagamentos
- **Regras**: **SCA** (quando aplicável) e **3DS2** para fluxos de cartão; *step‑up* por risco; fallback *frictionless* com justificativa.  
- **Hook**: `sca_required_missing•run->deny_tx; owner=SEC`.

## 179) PCI DSS & Escopo de Cartão
- **Regras**: segmentação de escopo, **tokenização/pan‑vault** externo, *vault isolado* e sem replicação; **mTLS**/JOSE para payloads sensíveis.  
- **Hook**: `pci_scope_violation•run->freeze_feature; owner=SEC`.

## 180) Disclosures & KIDs (PRIIPs/MiFID II) + TILA/Reg Z
- **Regras**: **CET/TAEG/APR** claros; **KID/PRIIPs** quando aplicável; suitability MiFID II; TILA/Reg Z (EUA).  
- **Hook**: `missing_kid_or_apr•run->block_offer; owner=LEGAL`.

## 181) Direitos do Consumidor & Ouvidoria
- **Regras**: canal de reclamações (SLA resposta ≤ 10 dias úteis); logs vinculados (`audit_id`); *chargeback/contestação* com trilha.  
- **Hook**: `complaint_sla_breach•run->escalate_ombudsman; owner=OPS`.

## 182) Ledger Contábil & *Double‑Entry*
- **Regras**: **double‑entry** por evento (DR/CR) com **chart‑of‑accounts** mapeado; *posting* por `LoanEvent`; reconciliação diária.  
- **Hook**: `posting_imbalance•run->halt_settlement; owner=FIN`.

## 183) Reconhecimento de Receita — *Agent‑Only*
- **Regras**: CE é **intermediário** (sem balanço); receita de **fee** (agent) com *contra‑partidas*; sem **principal**.  
- **Hook**: `principal_like_activity•run->freeze_flow; owner=FIN`.

## 184) *Risk Appetite* & RAROC
- **Regras**: **RAROC** e *risk appetite* por portfólio/linha; *headroom* dinâmico; overrides por comitê.  
- **Hook**: `raroc<floor•W->throttle+reprice; owner=RSK`.

## 185) AML — Transaction Monitoring & STR/ROS
- **Regras**: cenários (smurfing, *velocity*, *mule*, PEP, sanções); **STR/ROS** (reporte de operações suspeitas) com SLA; *watchlists* contínuas.  
- **Hook**: `tm_alert_high•run->suspend+investigate; owner=SEC`.

## 186) Dados Alternativos & Consentimento
- **Regras**: fontes alternativas (Open Finance/bureaus) somente com consentimento e **minimização**; rotas *fallback* multi‑provedor.  
- **Hook**: `provider_fail•5m->fallback_route; owner=INT`.

## 187) Transferência Internacional & Residência de Dados
- **Regras**: *data residency* por jurisdição; **SCCs**/DPA quando cabível; logs sem PII.  
- **Hook**: `data_residency_breach•run->freeze; owner=SEC`.

## 188) SDKs/Clients — Versionamento & Deprecação
- **Regras**: *semver*, *deprecation window* ≥ 90d, *changelog*; *contract tests* com SDKs oficiais.  
- **Hook**: `sdk_break_change•run->block_release; owner=PLAT`.

## 189) API GW & Segurança de Canal
- **Regras**: **OAuth2/mTLS**; **JWS/JWK** com rotação ≤ 90d; *OPA/ABAC* por rota.  
- **Hook**: `jwk_rotation_overdue•run->raise_issue; owner=SEC`.

## 190) Audit Pack — *Bundles* Reprodutíveis
- **Regras**: export **D+0** com contratos, eventos EIP‑712, *golden files*, hooks, ADRs, runbooks e **statusboards**; `hash`/`sig`.  
- **Hook**: `audit_export_fail•run->raise_issue; owner=OPS`.

## 191) Chaos Engineering & *Game Days*
- **Regras**: *chaos inject* controlado (oráculo off, CDC lag, drift spike, rail down); *game days* trimestrais.  
- **Hook**: `chaos_guard_fail•run->abort_experiment; owner=SRE`.

## 192) Comunicação de Incidentes
- **Regras**: **status page** + *RCAs* públicos (quando permitido); cadência de updates; *embargo* quando regulatório.  
- **Hook**: `status_publish_fail•run->raise_issue; owner=SRE`.

## 193) Edge Latency & CDN
- **Regras**: **CDN** e *edge compute* para FE; *budgets* por camada; cache coerente; `trace_id` ponta‑a‑ponta.  
- **Hook**: `edge_budget_breach•24h->rollback_FE; owner=FE`.

## 194) Multi‑moeda & Rounding
- **Regras**: **rounding** por moeda (pips/bps), casas decimais, *broken‑date* FX; *no‑arb* em cross‑rates.  
- **Hook**: `fx_rounding_error•run->halt_price; owner=PM`.

## 195) Soft‑Launch & Pilotos
- **Regras**: *allowlist* por parceiro, *feature flags* e *canary*; *success criteria* e **waiver time‑boxed**.  
- **Hook**: `pilot_fail•run->rollback; owner=PO`.

## 196) Fairness por Sub‑segmentos
- **Regras**: auditoria de **fairness** por sub‑segmento/região; *bias audit* programada; *mitigations* documentadas.  
- **Hook**: `bias_metric>cap•24h->pause; owner=ML`.

## 197) I18N/L10N — Locales & Formatos
- **Regras**: moedas/números/datas por locale; pluralização; *right‑to‑left* quando aplicável; *content testing*.  
- **Hook**: `i18n_missing•run->block_release; owner=FE`.

## 198) Retenção de Voz/Chat & E‑Discovery
- **Regras**: retenção segura de **voz/chat** (SLA legal), transcrição e associação a `audit_id`; anonimização quando exigido.  
- **Hook**: `edisco_gap•run->reindex; owner=OPS`.

## 199) Acessibilidade Estendida
- **Regras**: **WCAG 2.2 AA** com foco em acessibilidade cognitiva (leitura fácil, erros claros, navegação consistente).  
- **Hook**: `a11y_audit_fail•run->rollback_FE; owner=FE`.

## 200) Qualidade & Cobertura de Testes
- **Regras**: cobertura mínima por domínio (BE 85%/DATA 80%/ML 75%/FE 80%); **property‑based** para preços/oráculos; *chaos tests* para resilientes.  
- **Hook**: `coverage_drop•run->block_merge; owner=PLAT`.

## 200) Qualidade & Cobertura de Testes
- **Regras**: cobertura mínima por domínio (BE 85%/DATA 80%/ML 75%/FE 80%); **property‑based** para preços/oráculos; *chaos tests* para resilientes.  
- **Hook**: `coverage_drop•run->block_merge; owner=PLAT`.

## 201) SCA/3DS2 & PCI DSS (Pagamentos → Cartões)
- **Regras**: Strong Customer Authentication (quando aplicável); 3DS2; fallback *frictionless* documentado; PCI DSS escopo segmentado; PAN tokenizado em *vault* externo; payloads com mTLS + JWS.
- **Hooks**:
  - `sca_required_missing•run->deny_tx; owner=SEC`.
  - `pci_scope_violation•run->freeze_feature; owner=SEC`.

## 202) Disclosures Globais (KIDs/PRIIPs, MiFID II, TILA/Reg Z)
- **Regras**: CET/TAEG/APR sempre expostos; **KIDs/PRIIPs** quando aplicável; suitability MiFID II para capitais europeus; **TILA/Reg Z** para crédito EUA.
- **Hook**:
  - `missing_kid_or_apr•run->block_offer; owner=LEGAL`.

## 203) Data Residency & DSRs (Portal do Titular)
- **APIs**: `/privacy/erasure`, `/privacy/access`, `/privacy/export`.
- **SLA**: todas as DSRs respondidas em D+0; logs vinculados a `audit_id`.
- **Regras**: data residency enforced por jurisdição; SCCs/DPA onde cabível; masking em logs.
- **Hooks**:
  - `data_residency_breach•run->freeze; owner=SEC`.
  - `dsr_sla_breach•run->raise_issue; owner=SEC`.

## 204) SDKs/Clients — Semver & Deprecação
- **Regras**: versionamento semântico obrigatório; janela de deprecação ≥ 90 dias; changelog publicado; SDKs oficiais testados contra contratos de API.
- **Hook**:
  - `sdk_break_change•run->block_release; owner=PLAT`.

## 205) NPL Default Orchestrator (Commit‑Reveal)
- **Mecanismo**: commit‑reveal english auction; até 5 rounds; reserve_price definido por cenário; KPIs: decisão p75 ≤ 10d, clearing auction p75 ≤ 20d.
- **Hooks**:
  - `default_event•once->open_commit_reveal_auction; owner=TRUST`.
  - `auction_kpi_breach•run->raise_issue; owner=TRUST`.

---

## 206) Evidence JSON Linter + Golden Files (Catálogo)
- **Schema**: `schemas/evidence.v1.json` validado em CI; evidence mínima ≥3 (trace_id, audit_id, adr_id).
- **Golden Catalog**: APR, Auction, Waterfall, Idempotency.
- **Hooks**:
  - `evidence_lint_fail•run->block_release; owner=PO`.
  - `golden_fail•run->block_release; owner=SRE`.

## 207) Error‑Budget Freeze (SRE)
- **Regra**: se burn‑rate > 2× por 1h → `freeze_release + rollback`.
- **Hook**:
  - `error_budget_spike•1h->freeze_release; owner=SRE`.

## 208) Settlement Rails (PIX/Boletos/STR)
- **Regras**: cutoffs explícitos por rail; reconciliação D+0 via golden; `settlement.miss_pct ≤ 0,02%`/dia.
- **Hooks**:
  - `rail_cutoff_breach•run->halt_route+reschedule; owner=OPS`.
  - `settlement_miss>0.02%•D->reconcile+halt; owner=OPS`.

## 209) Anti‑Stacking Guard (PF/PJ)
- **Regras**: cooldown por CPF/CNPJ; velocity score; quarentena de sessão sob alerta.
- **Hooks**:
  - `stacking_score>τ•1h->freeze_new_credit; owner=RSK`.
  - `velocity_breach•15m->quarantine_session; owner=SEC`.

## 210) Rastreabilidade 360° — Publicação Pós‑Deploy
- **Regra**: export CSV/JSON (Feature → APIs/Contratos → Métricas/SLI/SLO → Hooks A110 → Evidence → ADR → Runbooks → Statusboards).
- **Hook**:
  - `trace360_publish_fail•run->block_release; owner=PO`.