# Q1 • Sprint 6 — MBP GA interno (30d verdes) + Readout & Handoff • v1.1 FINAL (deepdive 100×)
> **Alinhado a**: *Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)*, *S1–S5 v1.1*, e *Roadmap — Kickoff Intake (CE$) • V0.2 (Jeff Patton)*.  
> **Objetivo (2 semanas):** **confirmar GA interno** do **MBP** com **30 dias verdes contínuos**, consolidar **scorecards**, executar **readout** com lições e **handoff** para a próxima fase do **CreditEngine** (Q2), mantendo **governança A110** e **compliance A108** impecáveis.

---

## 0) Delta S5 → S6 (elevações)
- **Operação 30d**: todos os **watchers must‑have** verdes; **P1=0**; **error‑budget burn < 1×/30d**; **invariant=0**.
- **Preço & Oráculos**: **staleness p95 ≤ 30s**, **divergência ≤ 1,0%**, **failover TWAP < 60s** comprovado em drills.
- **Auto‑resolução & SLA**: **p95 ≤ 2h** (mediana ≤ 60m) com trilha/auditoria; fallback manual ensaiado.
- **Dados/DQ/CDC**: **CDC lag p95 ≤ 120s** e **dbt tests=pass** (rolling); documentação ≥ **95%** dos pacotes MBP.
- **Segurança/Privacidade**: **SBOM/SAST/Secrets** sem críticos; amostragem de logs 100% **sem PII**; *pentest light* interno.
- **Scorecards**: publicação diária/semanal (DEC/Preço/CDC/FE/A110) + **painel executivo**.
- **Readout**: pacote de evidências + **CAPAs** (ações corretivas) priorizadas para Q2/Q3.

---

## 1) Sprint Goal & DoA (S6)
**Goal:** Encerrar Q1 com **GA interno confirmado** (30d verdes), **readout** formal e **handoff** para as ondas CE$ seguintes.

**Definition of Awesome (S6):**  
- **Confiabilidade**: **0 P1**; **error‑budget burn < 1×/30d**; uptime prod ≥ **99,9%**.  
- **Integridade de Preço**: **Invariant error = 0**; **TWAP divergence ≤ 1,0%** (5m).  
- **Oráculos**: **staleness p95 ≤ 30s**; **failover < 60s** (drill).  
- **Resolução**: **p95 ≤ 2h**; mediana ≤ 60m; 100% audit trail.  
- **Dados**: **CDC p95 ≤ 120s**; **dbt tests=pass**; **schema_drift=0**.  
- **Experiência**: **TTPV p95 ≤ 0,8s**; **INP p75 ≤ 200ms**; regressões CWV=**No‑Go**.  
- **Governança**: **Hook Coverage ≥ 98%**; **Audit Coverage ≥ 99%** (rolling 24h).  
- **Readout**: Lições, **CAPAs** e **decisões ADR** registradas; **OK** de **PO/Eng/Data/SRE/SEC/PM**.

---

## 2) Definition of Ready (DoR)
- **Ambientes** `stage/prod` estáveis com canary‑off; *feature flags* congeladas (mudanças via Change Control).  
- **Painéis** SLO/Preço/CDC/FE/A110 publicados e acessíveis a todos os DRIs.  
- **Owners** de watchers/hook confirmados; rota de alerta verificada.  
- **Planos & Runbooks** (Oráculos, Resolução, Perf, CDC, Moderação) revisados e disponíveis.  
- **Lista de critérios GA (S6)** distribuída com queries/ids das evidências.

---

## 3) Escopo S6 (alto nível — sem backlog CSV)
- **Operação 30d verdes**  
  - On‑call 24×7; *error budget* e *slo burn* monitorados; incidentes P2/P3 tratados sob SOP.  
  - **Drills semanais**: **TWAP failover**, **Abort Canary** (simulado), **CDC delay**, **Fee guard**, **Moderação burst**.
- **Preço & Oráculos**  
  - Saúde contínua dos adaptadores; verificação de **quórum**; divergência e staleness sob limiares.  
  - *Failover playbook* pronto e auditado; relatórios de divergência por janela.
- **Auto‑Resolução & Fees**  
  - Observação contínua de **p95/mediana**; *cooldown* e *bounds* sob guarda; auditoria de alterações de fee.  
- **Moderação & Abuso**  
  - **MTTD ≤ 5m / MTTM ≤ 15m**; evidence pack por caso; revisão semanal de decisões.  
- **Dados/CDC & DQ**  
  - *dbt tests* (unique/not null/FKs/expectations) rodando nos pacotes MBP; *CDC lag p95 ≤ 120s*; alarmes ativos.  
- **Observabilidade/Scorecards**  
  - Scorecards diários (DEC/Preço/CDC/FE/A110); **painel executivo** (NSM/TTPV, P1, burn, TWAP, staleness, CDC, INP, Hook/Audit Coverage).  
- **Segurança/Privacidade/Compliance**  
  - Amostragem de logs (≥95%) **sem PII**; **SAST/Secrets/SBOM** verdes; política de retenção; checklist **LGPD A108**.  
- **Readout & Handoff**  
  - **Readout** com métricas 30d; lições; **CAPAs**; atualização de **DoA** e **catálogo**; **handoff** para Q2 (Consignado/Recebíveis) com *dependencies* e *open items* claros.

**Fora do escopo S6**: novas features de MBP; expansão externa; mudanças em modelos além do baseline.

---

## 4) Plano de 10 dias (quem faz o quê)
**D1** — Kick S6: congelar flags; revisar checklists; publicar **scorecards v1**.  
**D2** — Drill 1: **TWAP failover < 60s**; validar relatórios.  
**D3** — Drill 2: **CDC delay** (degrade/rollback); verificar DQ/dbt.  
**D4** — Drill 3: **Fee guard** (Δfee); auditoria de alterações.  
**D5** — Drill 4: **Moderação burst** (pause/unpause + evidências).  
**D6** — Auditoria **A110** (Hook/Audit Coverage); ajustar gaps.  
**D7** — Auditoria **A108** (privacidade/retention/logs); *pentest light*.  
**D8** — Fechar **evidence pack** 30d e **painel executivo**.  
**D9** — **Readout**: lições + **CAPAs** priorizadas; documentação ADRs.  
**D10** — **GA Confirm** (board): assinaturas; **handoff Q2**; comunicado interno.

> **Capacidade**: {PO:0,5 • ST:1,0 • PY:1,0 • DC:0,5 • ML:1,0 • SRE:0,5 • FE:0,5 • SEC/RSK:0,5}.  
> **WIP máx**: 2 por trilha (Ops/Preço/Dados/FE/Obs/Seg/Comp).

---

## 5) Test Plan & Aceites (S6)
**Operação**: 30d sem P1; **error‑budget burn < 1×/30d**; evidência de on‑call e *postmortems zero‑P1*.  
**Preço**: **Invariant=0**; **TWAP divergence ≤ 1,0%**; relatórios semanais.  
**Oráculos**: **staleness p95 ≤ 30s**; **failover < 60s** (drill).  
**Resolução**: **p95 ≤ 2h**; mediana ≤ 60m; 100% trilha.  
**Dados/CDC**: **dbt tests=pass**; **CDC p95 ≤ 120s**; **schema_drift=0**.  
**Experiência**: **TTPV p95 ≤ 0,8s**; **INP p75 ≤ 200ms**; sem regressão CWV.  
**Governança**: **Hook ≥ 98%**; **Audit ≥ 99%**; **evidence pack** completo.  
**Readout/Handoff**: documento aprovado com **CAPAs** e **decisões ADR**.

---

## 6) Measurement Sheet — S6 (rolling 30d)
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
Incidentes P1 (#),Incident DB,30d,==0,slo_budget_breach,rollback,SRE,inc.p1_count
Error budget burn,XLA,30d,<1x,slo_budget_breach,rollback,SRE,apm.error_budget_burn
Invariant error,Engine,1m,==0,amm_invariant_breach,block_release,DEC/PM,engine.amm_invariant
TWAP divergence %,Engine,5m,<=1.0,mbp_price_spike_divergence,freeze,PM/SRE,engine.twap_gap
Oracle staleness (ms),APM/Oracles,5m,<=30000,pm.oracle_staleness,twap_failover,PM/BC,orcl.staleness_ms
Failover TWAP (s),Drill,run,<60,pm.oracle_staleness,twap_failover,PM/BC,drill.twap_failover
Auto‑resolução p95 (h),Events,24h,<=2,mbp_resolution_sla,freeze,PM/BC,events.auto_resolve_p95
TTPV p95 (ms),APM/Traces,5m,<=800,slo_budget_breach,rollback,SRE,apm.ttp_dec_p95
INP p75 (ms),RUM,24h,<=200,web_cwv_regression,rollback_fe,FE,rum.inp_p75
CDC lag p95 (s),CDC/APM,5m,<=120,cdc_lag,degrade+rollback,DATA,cdc.lag_p95
DBT tests status,CI/dbt,run,pass,dbt_test_failure,block_merge,DATA,dbt.test_status
Hook Coverage %,CI/Repo,24h,>=98,metrics_decision_hook_gap,open_incident,PLAT,ci.hook_coverage
Audit Coverage %,Logs,24h,>=99,metrics_decision_hook_gap,open_incident,PLAT,logs.audit_coverage
MTTD moderação (min),Logs,1h,<=5,mbp_abuse_anomaly,alert+moderation,SEC/PM,logs.mttd_abuse
MTTM moderação (min),Logs,1h,<=15,mbp_abuse_anomaly,alert+moderation,SEC/PM,logs.mttm_moderation
```

---

## 7) Hooks A110 — exercícios (drills S6)
```yaml
exercises:
  twap_failover:
    inject: orcl.delay(staleness_ms=45000, duration='5m')
    expect: action=='switch_to_twap_failover' && failover_time<60s
  cdc_delay:
    inject: cdc.delay(p95='+180s', window='10m')
    expect: action=='degrade+rollback' && ticket.owner=='DATA'
  fee_guard:
    inject: fee.controller(alpha='x2', duration='10m')
    expect: hook=='fee_guard' && action in ['freeze','degrade_route']
  moderation_burst:
    inject: engine.burst_trades(rate='x3', duration='5m')
    expect: action=='alert+moderation' && market.status in ['paused','limited']
  slo_burn:
    inject: apm.loadtest(rps=N*1.2, duration='10m')
    expect: action=='rollback' && error_budget_burn<1
  web_cwv_regression:
    inject: fe.inp_regress(p75='+80ms', window='24h')
    expect: action=='rollback_fe'
```

---

## 8) ORR — **GA Confirm (30d verdes)** (checklist)
- **Confiabilidade**: 30d sem P1; **error budget** dentro; uptime ≥ 99,9%.  
- **Preço/Oráculos**: invariant=0; TWAP divergence ≤ 1,0%; staleness p95 ≤ 30s; failover < 60s (drill).  
- **Resolução**: p95 ≤ 2h; mediana ≤ 60m; trilha 100%.  
- **Dados/CDC**: dbt tests=pass; CDC p95 ≤ 120s; schema_drift=0.  
- **Experiência**: TTPV p95 ≤ 0,8s; INP p75 ≤ 200ms; sem regressões CWV.  
- **Governança**: Hook ≥ 98%; Audit ≥ 99%.  
- **Readout/Handoff**: artefatos publicados; CAPAs priorizadas; próximos marcos definidos (Q2 S7→S12).  
- **Assinaturas**: **PO, ST, PY, DC, ML, SRE, FE, SEC/RSK, PM/BC, INT**.

---

## 9) Riscos & Mitigações (watcher/hook)
1) **Burn de SLO** → `slo_budget_breach` → **rollback** + throttle.  
2) **CDC lag** → `cdc_lag` → **degrade/rollback**; priorizar ingest.  
3) **Staleness/divergência** → `pm.oracle_staleness`/`pm.oracle_divergence` → **TWAP/freeze**.  
4) **Resolução lenta** → `mbp_resolution_sla` → **freeze** + fallback manual.  
5) **INP/CWV** → `web_cwv_regression` → **rollback_fe**.  
6) **Privacidade/Segurança** → `dp_budget_breach`/`dep_vuln_open` → **freeze/block_release**.

---

## 10) Evidence Pack & Assinaturas
- **Evidências**: scorecards 30d; prints de dashboards; *trace_ids*; relatórios dbt/CDC; drills (TWAP/CDC/fee/moderação/SLO/FE); *commit sha*; **ADRs** atualizados; **CAPAs**.  
- **Assinaturas**: PO • ST • PY • DC • ML • SRE • FE • SEC/RSK • PM/BC • INT.

---

## 11) Demo (Review) & Comunicação
- **Roteiro**: painel executivo (NSM/TTPV/p95/P1=0/burn) → preço (invariant/TWAP) → oráculos (staleness/failover drill) → resolução (SLA/trace/audit) → dados (CDC/dbt) → FE (INP/CWV) → A110 (Hook/Audit Coverage) → **lições & CAPAs** → **decisão GA Confirm**.  
- **Comms**: post interno (sumário + KPIs + CAPAs), changelog e atualização de *statuspage*.

---

## 12) Pós‑Readout → Prep Q2
- Entregar **handbook de operação** (SOPs, DRIs, SLAs, scorecards).  
- Endereçar CAPAs *must‑do* como **pré‑work S7**.  
- Atualizar **catálogo MBP** e roadmap CE$ (baseline estabilizado).  
- Agendar **revisão de riscos** e **planejamento S7→S12**.

---

## 13) Políticas & No‑Go (reafirmação)
- **Sem GA Confirm** se qualquer **watcher crítico** vermelho; **sem logs com PII**; **waivers** somente com *timebox* + rollback e aprovação **PO+Eng+Data+SRE**.

---

> **Resultado esperado da S6**: **GA interno confirmado** com **30 dias verdes**, **evidence pack** robusto, **readout** executado e **handoff** concluído para Q2 (Consignado/Recebíveis), preservando **integridade de preço**, **confiabilidade**, **dados** e **governança** no padrão de excelência.

