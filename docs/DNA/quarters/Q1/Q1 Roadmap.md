# Q1 Roadmap — MBP GA interno + CE$ Fundações • v1.1 FINAL (triple‑reviewed)
> **Status:** versão revisada em 3 camadas (estratégica → operacional → técnica) para garantir **execução impecável** do trimestre. **PO = Accountable.** Sem backlog detalhado (a ser gerado depois).

---

## 0) Delta v1.0 → v1.1 (o que foi elevado)
- Critérios de saída por sprint ficaram **quantitativos e auditáveis**.
- **Gates/Kill** por sprint, com **watchers/hooks** específicos.
- **ORR checklist** objetivo por marco (Pre‑deploy, Canary, GA).
- **Measurement Plan** do Q1 com queries/ids de referência.
- **Runbooks** vinculados 1:1 a cada risco do trimestre.
- **Planejamento de capacidade** e **RACI** granular por sprint.
- Tabela de **calendarização** pronta para ancorar datas (sem fixar o calendário financeiro).

---

## 1) Objetivo & KRs do Q1
**Objetivo:** Levar o **MBP** ao **GA interno (30 dias verdes)** e deixar **Fundações CE$** em **scorecard verde**.

**KRs (Q1):**
1) **TTPV p95 ≤ 0,8s** (painel MBP + DEC) por ≥ 30 dias.
2) **Invariant error = 0** (Δk/k ≤ 1e−9 por 30 dias); **TWAP divergence ≤ 1,0%**.
3) **Resolução ≤ 24h** em 100% dos mercados ativos no Q1.
4) **Hook Coverage ≥ 98%** e **Audit Coverage ≥ 99%** (rolling 7d).
5) **CDC lag p95 ≤ 120s** nas tabelas quentes de CE$ Fundações.

---

## 2) Sprints, Entregas e Critérios de Saída
**S1 (Semanas 1–2) — Slice 0 / Walking Skeleton**
- **Entregas:** AMM CPMM (x·y=k), criação manual, liquidez simulada, UI preço⇄prob, resolução manual, pontos de reputação.
- **Saída (Pre‑deploy):** `invariant_error=0`; **lat p95 ≤ 0,8s**; *goldens* AMM ok; **watchers must‑have** verdes.
- **Kill (S1):** 1× `invariant_breach` pós‑fix não resolvida em 24h → halt + correção antes de seguir.

**S2 (Semanas 3–4) — Hardening + Observabilidade**
- **Entregas:** tracing A71–A72, métricas/eventos MBP, logs auditáveis, **hooks A110 dry‑run**, ADRs rascunho.
- **Saída (Canary M1):** APM+RUM no ar; `hooks_test=pass`; `error_budget_burn<1x/4h`; **mbp_* verdes**.
- **Kill (S2):** `error_budget_burn≥1x/4h` por 2 janelas → rollback e correções obrigatórias.

**S3 (Semanas 5–6) — Slice 1 / MVP interno**
- **Entregas:** templates de mercado; regras de resolução (Truth Source); TWAP/benchmarks; painel completo; anti‑abuso básico.
- **Saída (Release):** 5–10 mercados ativos; **depth@2% ≥ 500**; `mbp_resolution_sla OK`.
- **Kill (S3):** depth < 500 por 24h → ativar market‑maker programático antes de novos mercados.

**S4 (Semanas 7–8) — MVP hardening + CE$ Fundações**
- **Entregas:** contratos A106/A87/A89 (pacotes críticos), dbt tests, schema registry; DEC p95≤0,8s; donos de watchers; ADRs 001–003 aprovados.
- **Saída (Pre‑GA M2):** **Scorecard CE$ Fundações ≥ 90% verde**; `cdc_lag p95≤120s`; `schema_drift=0`.
- **Kill (S4):** `schema_registry_drift>0` ou `data_contract_break` → bloqueio de deploy.

**S5 (Semanas 9–10) — Slice 2 / Escala**
- **Entregas:** auto‑resolução por oráculo (quórum 2/3 + TWAP 5m), fees dinâmicos, backtesting/simulação, moderação avançada, feature flags.
- **Saída (GA interno):** 25+ mercados; `oracle_staleness<30s`; `twap_gap≤1%`; **0 P1** no período.
- **Kill (S5):** qualquer P1 em produção → freeze até causa raiz + ação corretiva aplicada.

**S6 (Semanas 11–12) — Operação + Handoff**
- **Entregas:** operação assistida; drills dos runbooks; relatórios de DoA/OKRs; handoff para trilhas CE$.
- **Saída (M3):** **GA interno confirmado** + 30 dias verdes contínuos + scorecard CE$ verde.
- **Kill (S6):** 2 violações de `mbp_resolution_sla` na janela de 14 dias → reverter auto‑resolução para resolve‑by‑oracle até fix.

---

## 3) Lanes & Pacotes (Q1)
- **MBP (Produto/Engine):** AMM, criação/mercados, resolução, painel, moderação.
- **DATA/CDC:** A106/A87/A89 + dbt + DQ + schema registry.
- **DEC (Perf):** pipeline p95≤0,8s; roteamento; rollback por SLO.
- **ORÁCULOS/FX:** quórum 2/3; TWAP 5m; divergência≤1%.
- **FE (UI/RUM):** INP p75≤200ms; RUM/CWV; Creator/Board/Admin.
- **SEC/PRIV/RSK:** DPIA; logs sem PII; abuso/moderação; ADRs.
- **SRE/PLAT:** APM/metrics/logs/traces; CI/CD; canary; incident.

---

## 4) Measurement Plan (Q1)
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner
TTPV p95,APM/Traces,5m,<=0.8s,slo_budget_breach,rollback,SRE
Invariant error,Engine,1m,==0,amm_invariant_breach,block_release,DEC/PM
Resolution SLA,Events,24h,<=24h,mbp_resolution_sla,freeze,PM/BC
Depth@2%,Engine,15m,>=500 units,mbp_liquidity_depth,degrade,PM
TWAP divergence,Engine/Oracle,5m,<=1.0%,mbp_price_spike_divergence,freeze,PM/SRE
Oracle staleness,Oracles/APM,5m,<=30s,oracle_staleness,twap_failover,PM/BC
CDC lag p95,CDC/APM,5m,<=120s,cdc_lag,degrade+rollback,DATA
INP p75,RUM,24h,<=200ms,web_cwv_regression,rollback_fe,FE
Hook Coverage,Repo/CI,24h,>=98%,metrics_decision_hook_gap,open_incident,PLAT
Audit Coverage,Logs,24h,>=99%,metrics_decision_hook_gap,open_incident,PLAT
```
**Queries de referência:** `apm.query.ttpv_p95`, `rum.query.inp_p75`, `engine.metric.invariant_error`, `events.query.resolution_hours`, `engine.metric.depth_2pct`, `engine.metric.twap_gap`, `cdc.query.lag_p95`, `oracle.query.staleness`, `ci.query.hook_coverage`, `logs.query.audit_coverage`.

---

## 5) Gates, Kill Criteria & ORR
**Gates por sprint:**
- **Pre‑merge (S1→S6):** cobertura≥80%; `formal_gate=pass`; `dep_vuln=0` crítico.
- **Pre‑deploy (S1, S3, S5):** goldens passam; **p95≤0,8s**; `N RPS` alvo estável; watchers verdes.
- **Canary (S2, S5):** `error_budget_burn<1x/4h`; `invariant_breach=0`; failover TWAP testado.
- **GA (S6):** 30d verdes + DoA cumprida.

**ORR (por marco):** DRIs; oncall; SLOs; feature flags; rollback testado; comunicação interna (PR/FAQ); scorecards publicados.

**Kill Criteria (geral do Q1):** invariant breach persistente (7d); ≥2 violações SLA resolução em 14d; abuso>limiar 3×/sem; bloqueio legal; PSI/KS fora do envelope 7d.

---

## 6) Riscos & Runbooks (vinculados)
1) **Oráculo divergente/estagnado** → `oracle_divergence`/`oracle_staleness` → **Runbook Oráculos:** ativar TWAP; revisar fontes; congelar criação (se necessário).
2) **CDC lag alto** → `cdc_lag` → **Runbook CDC:** repriorizar ingest; abrir incidente; degradar/rollback.
3) **CWV/INP regressão** → `web_cwv_regression` → **Runbook FE:** rollback; mitigar causa; re‑medir RUM.
4) **Abuso/manipulação** → `mbp_abuse_anomaly` → **Runbook Moderação:** pausar contas; coletar evidências; moderação.
5) **Erro budget burn** → `slo_budget_breach` → **Runbook Confiabilidade:** rollback; reduzir carga; correção.

---

## 7) Dependências (Q1)
**Externas:** adaptadores de oráculo/benchmark; identidades (internas).  
**Internas:** schema registry; APM/Observabilidade; CI/CD; RUM; authn/authz; logging/auditoria; feature‑flags.

---

## 8) RACI & Capacidade (Q1)
**RACI:** PO=A; R por domínio (DEC, DATA, ML, FE, SRE, SEC/RSK, PM/BC, INT, PLAT).  
**Capacidade base/sprint:** {PO:0,5 | ST:1,0 | PY:1,0 | DC:0,5 | ML:1,0 | SRE:0,5 | FE:0,5}.
**Alocação indicativa:** S1–S2 (MBP 70% / Obs 30%) • S3–S4 (MBP 50% / CE$ 50%) • S5–S6 (MBP 60% / CE$ 40%).

---

## 9) Calendarização (preencha o âncora e rode)
> Defina o **Monday‑anchor** do Q1 (conforme calendário fiscal) e marque as semanas.

| Sprint | Datas (seg–sex) | Gate | Principal entrega |
|---|---|---|---|
| S1 | __/__/____ – __/__/____ | Pre‑deploy | Skeleton (engine/UI/resolução manual) |
| S2 | __/__/____ – __/__/____ | Canary (M1) | Hardening + Telemetria + Hooks |
| S3 | __/__/____ – __/__/____ | Release | MVP: templates/TWAP/painel |
| S4 | __/__/____ – __/__/____ | Pre‑GA (M2) | CE$ Fundações (DEC p95≤0,8s; DQ; Schema) |
| S5 | __/__/____ – __/__/____ | GA Interno | Escala: auto‑res/fees/simulação |
| S6 | __/__/____ – __/__/____ | GA Confirmado (M3) | Operação 30d verdes + Scorecard CE$ |

---

## 10) Entregáveis do Q1 (sem backlog)
- **MBP GA interno** com auto‑resolução, moderação, painel e telemetria completa.
- **Fundações CE$**: contratos A106/A87/A89, A71–A72, A110, DEC p95≤0,8s.
- **ADRs 001–003** aprovados e arquivados.
- **Measurement Plan + painel Hook Coverage** publicados.
- **Runbooks validados** (drills) e **audit pack** por mudança (trace_id/commit/sha).

---

### Apêndice A — Watchers/Hook do Q1 (recorte operacional)
- `mbp.amm_invariant_breach: abs(x*y-k)/k>1e-9•1m → block_release` (DEC/PM)
- `mbp.resolution_sla: T_resolucao>24h → freeze+notify` (PM/BC)
- `mbp.liquidity_depth_2pct: depth@2pct<500•15m → degrade_route` (PM)
- `mbp.price_spike_divergence: |price-twap|/twap>1.0%•5m → freeze` (PM/SRE)
- `mbp.abuse_anomaly: abuse_flags>5•1h → alert+moderation` (SEC/PM)
- `dec.latency_p95: p95>800ms•5m → degrade_route` (SRE)
- `cdc_lag_p95: p95>120s•5m → degrade+open_ticket` (DATA)
- `schema_registry_drift>0 → block_deploy` (DATA)
- `data_contract_break==true → rollback+waiver` (DATA)
- `web_cwv_regression (INP p75>200ms•24h) → rollback_fe` (FE)
- `slo_budget_breach>2x•1h → rollback` (SRE)

---

**FIM — Q1 pronto pra rodar.** Quando quiser, gero a versão com **datas preenchidas** e **quadros de apresentação** (slides/board visual).

