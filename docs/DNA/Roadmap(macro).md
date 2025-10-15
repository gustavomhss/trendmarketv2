# CreditEngine — Master Plan v1.1 (MBP‑first, 12M) • **sem backlog**
> Versão ajustada conforme sua solicitação: **sem backlog**, com todos os **apertos nível master** — PR/FAQ, hooks A110 com **limiares numéricos**, ADRs críticos, painel **Hook Coverage**, DPIA/privacidade, runbooks vinculados a watchers, mapeamento **SKU→Roadmap (H0–H3)**, e governança A110.

---

## 0) Delta Executivo (v1.0 → v1.1)
- **Incluído PR/FAQ (1 pág + 6 perguntas)**
- **Hooks A110** sem placeholders (`X`, `Y`, `σ·N`) → **limiares iniciais calibrados**
- **3 ADRs críticos** (Oráculos, AMM vs. Orderbook, Roteamento FX)
- **Measurement Plan** com **painel Hook Coverage** e queries de referência
- **DPIA/PIA** enxuta + **política de logs sem PII**
- **Runbooks** amarrados 1:1 com watchers
- **Mapa SKU→Roadmap (Readiness H0–H3)**
- **Fórmula de Prioridade** adicional para desempate (além do WSJF)

---

## 1) PR/FAQ (Bezos‑style, one‑pager)
**Press Release (interno)** — *Hoje lançamos o Mercado de Previsões (MBP) interno do CreditEngine.* Ele dá às nossas squads um preço/implied‑probabilidade em tempo real para decisões estratégicas. O MBP eleva a barra de governança (hooks A110), acelera aprendizado (telemetria/experimentos) e cria base para as ondas CE$ (consignado, recebíveis, etc.). O GA interno ocorre após 30 dias verdes, com **resolução ≤ 24h**, **invariant error = 0**, **TTPV p95 ≤ 0,8s** e **INP p75 ≤ 200ms**. Sem payout financeiro externo nesta fase; privacidade e compliance by‑design.

**FAQ (6)**
1) *Por que MBP primeiro?* — Para construir reputação de preço, telemetria e governança reusáveis em CE$.
2) *Como medimos sucesso?* — NSM TTPV; DoA MBP (resolução≤24h, invariant=0, depth@2%≥limiar, CWV ok); error‑budget<1x.
3) *Riscos principais?* — Divergência/oráculos, CDC lag, drift de modelo, abuso; mitigados por watchers A110 e runbooks.
4) *Quando abrimos para fora?* — Só após GA interno + revisão legal (gate externo: AML/KYC, termos, publicidade).
5) *Como evitamos “Big Bang”?* — Slices: Skeleton→MVP→Escala, com canary e feature flags.
6) *Como isso acelera CE$?* — Oráculos/TWAP, UI, observabilidade e governança do MBP são blocos‑mãe das ondas CE$.

---

## 2) Portfolio Roadmap (12M) — visão
**Q1:** MBP GA interno + Fundações CE$ (A106/A87/A89, A71–A72, A110, DEC p95≤0,8s)  
**Q2:** Consignado (PF) + Recebíveis (PJ)  
**Q3:** CDC Veículo (PF) + Pessoal OF (PF)  
**Q4:** Home Equity + Microcrédito  
**Gates por marco:** Pre‑merge → Pre‑deploy → Canary → GA (30d verdes). Falha crítica → rollback/waiver (A106).

---

## 3) Roadmap 0–90d (MBP‑first)
- **S0–S2 (Slice 0 — Skeleton):** CPMM x·y=k; criação manual; liquidez simulada; UI mínima; resolução manual; pontos de reputação. **Exit:** invariant=0; p95≤0,8s; goldens ok.
- **S3–S4 (Slice 1 — MVP):** templates; resolução regrada; TWAP; painel completo; auditoria; anti‑abuso. **Exit:** 5–10 mercados; depth@2%≥**500 unid.**; resolução≤24h.
- **S5 (Slice 2 — Escala):** auto‑resolução por oráculo; fees dinâmicos; simulação/backtesting; moderação avançada; flags. **Exit:** 25+ mercados; 30d verdes; 0 P1.
- **S6:** GA interno confirmado; handoff para CE$ Fundações.

> **Nota:** “unid.” = unidade de negociação interna (sem valor financeiro). Limiar inicial = 500; recalibrável.

---

## 4) Measurement Plan (com Hook Coverage)
```csv
KPI,Fonte,Janela,SLO,Watcher,Hook,Owner
TTPV p95,APM/Traces,5m,<=0.8s,slo_budget_breach,rollback,SRE
INP p75,RUM,24h,<=200ms,web_cwv_regression,rollback_fe,FE
Invariant error,Engine,1m,==0,amm_invariant_breach,block_release,DEC/PM
Resolution SLA,Events,24h,<=24h,mbp_resolution_sla,freeze,PM/BC
Depth@2%,Engine,15m,>=500 units,mbp_liquidity_depth,degrade,PM
TWAP divergence,Engine/Oracle,5m,<=1.0%,mbp_price_spike_divergence,freeze,PM/SRE
CDC lag p95,CDC/APM,5m,<=120s,cdc_lag,degrade+rollback,DATA
Oracle staleness,Oracles/APM,5m,<=30s,oracle_staleness,twap_failover,PM/BC
Hook Coverage (%),Repo/CI,24h,>=98%,metrics_decision_hook_gap,open_incident,PLAT
Audit coverage,Logs,24h,>=99%,metrics_decision_hook_gap,open_incident,PLAT
```

**Queries de referência:** `apm.query.ttpv_p95`, `rum.query.inp_p75`, `engine.metric.invariant_error`, `events.query.resolution_hours`, `engine.metric.depth_2pct`, `engine.metric.twap_gap`, `cdc.query.lag_p95`, `oracle.query.staleness`, `ci.query.hook_coverage`, `logs.query.audit_coverage`.

---

## 5) Watchers & Hooks A110 — **limiares v1.1**
```yaml
version: 1
owners:
  accountables: { all: "PO" }
  responsibles: { DEC: "ST", DATA: "PY/DC", ML: "ML", FE: "FE", SRE: "SRE", SEC: "SEC/RSK", PM: "PM/BC", INT: "INT", PLAT: "PLAT" }
hooks:
  mbp.amm_invariant_breach: { rule: "abs(x*y-k)/k>1e-9•1m", action: "block_release", owner: "DEC/PM" }
  mbp.resolution_sla:       { rule: "resolution_hours>24h",     action: "freeze+notify", owner: "PM/BC" }
  mbp.liquidity_depth_2pct: { rule: "depth_at_2pct<500•15m",     action: "degrade_route", owner: "PM" }
  mbp.price_spike_divergence:{ rule: "abs(price-twap)/twap>0.010•5m", action: "freeze", owner: "PM/SRE" }
  mbp.abuse_anomaly:        { rule: "abuse_flags>5•1h",          action: "alert+moderation", owner: "SEC/PM" }
  dec.latency_p95:          { rule: "latency.p95>800ms•5m",      action: "degrade_route", owner: "SRE", rollback: "yes" }
  data.cdc_lag_p95:         { rule: "cdc_lag.p95>120s•5m",       action: "degrade+open_ticket", owner: "DATA", rollback: "yes" }
  data.schema_drift:        { rule: "schema_registry_drift>0",    action: "block_deploy", owner: "DATA" }
  data.contract_break:      { rule: "data_contract_break==true",  action: "rollback+waiver_timebox", owner: "DATA" }
  data.dbt_test_failure:    { rule: "dbt_tests.failed>0",         action: "block_merge", owner: "DATA" }
  ml.model_drift:           { rule: "psi>0.20|ks>0.10•60m",       action: "rollback_model", owner: "ML" }
  ml.srm_guard:             { rule: "srm_pvalue<0.01",            action: "stop_experiment", owner: "ML" }
  pm.oracle_staleness:      { rule: "staleness_ms>30000•5m",      action: "switch_to_twap_failover", owner: "PM/BC" }
  pm.oracle_divergence:     { rule: "abs(oracle_a-oracle_b)/twap>0.010•5m", action: "freeze_oracle", owner: "PM/BC" }
  pm.fx_benchmark_delta:    { rule: "abs(quote-benchmark)/benchmark>0.015•10m", action: "alert+degrade_route", owner: "RSK/Treasury" }
  fe.web_cwv_regression:    { rule: "cwv.regressed==true•30m",    action: "rollback_fe", owner: "FE" }
  fe.inp_p75:               { rule: "inp.p75>200ms•24h",          action: "rollback_fe", owner: "FE" }
  sre.slo_budget_breach:    { rule: "error_budget_burn>2x•1h",    action: "rollback", owner: "SRE" }
  sec.dp_budget_breach:     { rule: "privacy_budget>1.5x•1h",     action: "freeze+audit", owner: "SEC" }
  sec.dep_vuln_open:        { rule: "critical_vuln_open>0•24h",   action: "block_release", owner: "SEC" }
  sec.formal_verification_gate:{ rule: "formal_proof_status!=pass",action: "block_release", owner: "RSK/SEC" }
  plat.runtime_eol:         { rule: "runtime.eol<90d and not(plan)", action: "raise_blocker", owner: "PLAT" }
  int.api_breaking_change:  { rule: "api_breaking_change_detected==true", action: "block_merge", owner: "INT" }
  int.api_contract_break:   { rule: "api_contract_break==true",    action: "rollback", owner: "INT" }
```

---

## 6) ADRs (decisões arquiteturais)
**ADR‑001 — Oráculos (quórum vs. TWAP puro)**  
- **Decisão:** Quórum 2/3 com **fallback TWAP 5m**; heartbeat 30s; desvio máximo 1.0%.  
- **Drivers:** Robustez vs. latência; resiliência a outliers; clareza de governança.  
- **Consequências:** Maior custo de integração; menor risco de manipulação.

**ADR‑002 — Engine MBP (AMM CPMM vs. Orderbook sintético)**  
- **Decisão:** **CPMM** para v1 (simplicidade, slippage previsível); avaliar orderbook sintético na v2 (Slice Escala).  
- **Drivers:** Tempo‑de‑mercado, explainability, telemetria.  
- **Consequências:** Menor granularidade de preço; compensado por TWAP/benchmarks.

**ADR‑003 — Roteamento FX (benchmarks / VPIN)**  
- **Decisão:** Roteamento por **benchmark+spread** com alarme em **1,5%**; explorar VPIN como KRI.  
- **Drivers:** Transparência, auditabilidade, custo.  
- **Consequências:** Exige manutenção de benchmarks; menor risco de preço fora do mercado.

---

## 7) Privacidade & Segurança (DPIA)
- **Âmbito:** uso interno do MBP; sem payout financeiro externo; minimização de dados; retenção curta; anonimização de eventos de UI.
- **Política de logs:** **sem PII** em logs; mascaramento/ hashing quando inevitável; segregação por ambiente; acesso por necessidade.
- **Controles:** rate‑limit; validação/quórum de fonte; cooldown de criação; moderação auditável; *least privilege* em integrações.

---

## 8) Runbooks vinculados a watchers
- `amm_invariant_breach` → **Runbook Invariante**: HALT pool → calcular Δk → reprocessar swaps → publicar post‑mortem (≤24h).
- `mbp_resolution_sla` → **Runbook Resolução**: Escalar owner → aplicar resolve‑by‑oracle → registrar waiver A106 → comunicar.
- `mbp_liquidity_depth` → **Runbook Liquidez**: Habilitar market‑maker programático → elevar D_min → revisar fees/tick.
- `mbp_price_spike_divergence` → **Runbook Preço**: Ativar TWAP → auditar fontes → congelar criação de novos mercados.
- `cdc_lag` → **Runbook CDC**: Repriorizar ingest → abrir incident → ativar downgrade/rollback.
- `model_drift` → **Runbook Modelos**: Retornar para champion → recalibrar monitor → abrir experimento controlado.

---

## 9) Mapa **SKU→Roadmap** (Readiness H0–H3)
- **H0 (foundation):** A106/A87/A89, A71–A72, A110, DEC p95≤0,8s, consent OF.  
- **H1:** Consignado (CET, margem, tetos, integrações) • Recebíveis (registradoras, portabilidade, reconcil D+1).  
- **H2:** CDC Veículo (gravame/DETRAN, LTV, portais) • Pessoal OF (modelos PF, antifraude).  
- **H3:** Home Equity (garantias, LTV/LTI/DTI, desembolso) • Microcrédito (jornada orientada, relatórios).  
> Cada SKU herda os **must‑have** + hooks específicos da trilha.

---

## 10) Prioridade (além do WSJF)
**Fórmula complementar:** Priority = \( \frac{Impacto\times(1−Risco)}{Esforço\times CoD} \).  
**Uso:** aplicar quando WSJF empatar; documentar rationale no ADR do épico.

---

## 11) RACI & Capacidade
**RACI:** PO = **A** em tudo; **R** por domínio (DEC, DATA, ML, FE, SRE, SEC/RSK, PM/BC, INT, PLAT).  
**Capacidade base/sprint:** {PO:0,5 | ST:1,0 | PY:1,0 | DC:0,5 | ML:1,0 | SRE:0,5 | FE:0,5}.  
**Ritos:** Replanejamento trimestral; limites de WIP; buffers para incidentes.

---

## 12) Governança: Gates & Kill Criteria
**Gates:** Pre‑merge (cobertura≥80%; formal_gate=pass; 0 dep crítico) → Pre‑deploy (goldens; p95≤0,8s; N RPS; watchers verdes) → Canary (budget<1x/4h; invariant=0; failover TWAP ok) → GA (30d verdes + DoA).  
**Kill Criteria:** invariant breach persistente (7d); ≥2 violações SLA resolução/14d; abuso>limiar 3×/sem; bloqueio legal; PSI/KS fora do envelope 7d.

---

## 13) Traceabilidade (template canônico)
**Matriz CSV (sem backlog nesta v1.1):** `Requisito,Feature,Watcher,Hook,KPI,Evidência,AC (Given/When/Then),Owner`.  
**Política:** nenhuma feature sem watcher/hook + métrica/AC → **No‑Go**.

---

> **Pronto.** Este documento é o seu **guarda‑chuva de execução** para 12 meses — com PR/FAQ, métricas, hooks, ADRs, privacidade, runbooks e governança **sem fila de backlog**. Quando quiser, gero o backlog a partir daqui, já com ACE/DoR/DoD e *hook coverage* embutidos.

