# Q1 • Sprint 2 — MBP Slice 0 Hardening + Observabilidade + Hooks A110 (Dry‑run) • v1.1 FINAL (deepdive 10×)
> **Alinhado a**: *Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)*, *Q1 • Sprint 1 v1.1*, e *Roadmap — Kickoff Intake (CE$) • V1 (2025‑09‑10)*.  
> **Objetivo (2 semanas):** **endurecer o Slice 0 do MBP**, fechar observabilidade **A71–A72**, **exercitar Hooks A110 (dry‑run/fault‑injection)** e atingir **Gate Canary (M1)** com **error‑budget burn < 1×/4h**, **watchers verdes** e **telemetria completa** em `stage` e `prod‑shadow`.

---

## 0) Delta S1 → S2 (elevações)
- **Perf**: tuning DEC/Engine (p95≤0,8s sob carga‑alvo definida no ORR) e *profiling* com evidências.  
- **Observabilidade**: métricas/eventos/traces **completos** (DEC/MBP/FE/DATA/INT/SEC), **dashboards + alarmes** publicados.  
- **A110**: **dry‑run** e **fault‑injection** para `invariant`, `resolution_sla`, `liquidity_depth`, `price_spike`, `cdc_lag`, `schema_drift`, `api_*`, `web_cwv`, `slo_budget`, `model_drift`, `dp_budget`.  
- **Segurança/Privacidade**: SBOM/SAST/Secrets limpos; logs **sem PII** (A108) validados em amostra.  
- **Runbooks**: v1→**v1.1** com *RTO/RPO* e *who‑calls‑who*; **drills** agendados/executados.  
- **Canary readiness**: playbook de **abort**, *shadow traffic* e *feature flags* categorizadas.

---

## 1) Sprint Goal & DoA (S2)
**Sprint Goal:** habilitar **Canary (M1)** do MBP com telemetria 360°, hooks A110 exercitados e performance sob carga‑alvo.  
**Definition of Awesome (S2):**  
- **Perf**: DEC **p95 ≤ 0,8s** por ≥ 1h com **N rps** (definir no ORR) e **0** 5xx; **invariant=0**.  
- **Telemetria**: 100% spans chave (`amm.quote|swap`, `resolution.rule`, `audit.write`) + **eventos MBP** (create/liquidity/trade/resolve) e **RUM** ativo (INP p75≤200ms).  
- **Hooks**: **100% must‑have** carregados com **owners**; **dry‑run=pass** em todos; **falhas simuladas** disparam **ações corretas**.  
- **SLO**: **error‑budget burn < 1×/4h** (canary), **P1=0**.  
- **Segurança/Privacidade**: SBOM/SAST/Secrets **sem críticos**; **logs sem PII** (amostra ≥ 95%).

---

## 2) Definition of Ready (DoR)
- `dev`/`stage` estáveis; *prod‑shadow* liberado; **feature flags** revisadas (`mbp.create_market`, `mbp.resolve.manual`).  
- Acesso a **APM/Logs/Traces/RUM**, **schema registry**, **CI/CD**.  
- **Contratos de eventos** `mbp.events.v1` registrados (A106/A87).  
- **Goldens** de engine v1 aprovados na S1.  
- **Owners** por watcher/hook confirmados.

---

## 3) Escopo S2 (alto nível — sem backlog CSV)
- **Observabilidade A71–A72 (fechamento)**  
  - Métricas DEC: `lat.p50|p95`, `rps`, `5xx`, `error_budget_burn`.  
  - Métricas MBP: `amm.invariant_error`, `price.twap_gap`, `liquidity.depth@2pct`, `res.sla_hours`.  
  - Eventos MBP: `market_created`, `liquidity_added`, `trade_executed`, `resolution_started/finished`, `flagged_abuse`.  
  - Traces: spans end‑to‑end (DEC/MBP/INT/DATA/FE) com **trace_id** correlacionado a audit.
- **Hooks A110 — Dry‑run + Fault‑Injection**  
  - Exercitar: `amm_invariant_breach`, `mbp_resolution_sla`, `mbp_liquidity_depth`, `mbp_price_spike_divergence`, `cdc_lag`, `schema_registry_drift`, `data_contract_break`, `slo_budget_breach`, `web_cwv_regression`, `api_breaking_change`, `api_contract_break`, `model_drift`, `dp_budget_breach`.  
  - Validar **ação** (rollback/freeze/degrade/alert) e **notificação** (on‑call/Slack/Email) + **owner**.
- **DEC/Engine — Hardening**  
  - Cache quente/controlado; *profiling*; *noisy neighbors*; golden v2 (sequências longas).  
- **FE (UI/RUM)**  
  - Micro‑otimizações: *hydration defer*, *preload*, limites de *reflow*; INP p75≤200ms; regressão CWV bloqueia deploy.  
- **DATA/CDC & Contratos**  
  - dbt smoke tests; `cdc_lag` alarmes; `schema_drift` simulado; documentação ≥95% do pacote MBP.  
- **Segurança/Privacidade (A108)**  
  - Amostragem de logs (≥95%) sem PII; *secrets scan*; *dep vulns* zeradas; *least‑privilege* verificado.
- **Runbooks v1.1 + Drills**  
  - Invariante, CWV/INP, CDC lag, Oráculos staleness/divergência, *Abort Canary*.

**Fora do escopo S2**: TWAP/oráculos reais (entra **S3**), auto‑resolução, fees dinâmicos, moderação avançada.

---

## 4) Plano de 10 dias (quem faz o quê)
**D1** — Observabilidade: completar métricas/eventos/traces; publicar painéis iniciais.  
**D2** — Hooks: carregar cenários de **dry‑run**; validar owners/rotas de alerta.  
**D3** — Fault‑injection 1: `invariant`, `lat_p95`, `resolution_sla`.  
**D4** — Fault‑injection 2: `cdc_lag`, `schema_drift`, `api_*`.  
**D5** — FE: *perf pass* INP p75; auditoria RUM; regressão CWV=**No‑Go**.  
**D6** — DEC: *profiling*/cache; hardening; golden v2.  
**D7** — DATA: dbt smoke; documentação; alarmes cdc.  
**D8** — Drill Runbooks: Invariante + Abort Canary; evidências.  
**D9** — **prod‑shadow** + checklist Canary; *bug‑bash* multi‑papel.  
**D10** — Review/Demo; Retro; **Gate Canary (M1)**.

> **Capacidade**: {PO:0,5 • ST:1,0 • PY:1,0 • DC:0,5 • ML:1,0 • SRE:0,5 • FE:0,5}.  
> **WIP máx**: 2 por trilha (Engine, FE, Observabilidade, DATA/INT, Segurança).

---

## 5) Test Plan & Perf Budget (S2)
**Cobertura mínima**: unit (engine) ≥80%; integração (API) ≥60%; E2E (feliz + 3 infelizes).  
**Carga** (stage/prod‑shadow): **N rps** (ORR) por 60 min, **p95≤0,8s**, **5xx=0**, **invariant=0**.  
**Fault‑injection**: atraso CDC; drift schema; regressão CWV; *spike* de preço; *rate‑limit* API; *staleness* oráculo (simulado).  
**Aprovação**: todos os **hooks** disparam **ação correta**; **error‑budget burn <1×/4h**; **P1=0**.

---

## 6) Measurement Sheet — S2 (referência)
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
Latency p95 (ms),APM/Traces,5m,<=800,slo_budget_breach,rollback,SRE,apm.ttp_dec_p95
Invariant error,Engine,1m,==0,amm_invariant_breach,block_release,DEC/PM,engine.amm_invariant
INP p75 (ms),RUM,24h,<=200,web_cwv_regression,rollback_fe,FE,rum.inp_p75
Resolution SLA (h),Events,24h,<=24,mbp_resolution_sla,freeze,PM/BC,events.resolution_sla
Liquidity depth @2%,Engine,15m,>=500,mbp_liquidity_depth,degrade,PM,engine.depth_2pct
TWAP gap %,Engine (sim),5m,<=1.0,mbp_price_spike_divergence,freeze,PM/SRE,engine.twap_gap
CDC lag p95 (s),CDC/APM,5m,<=120,cdc_lag,degrade+rollback,DATA,cdc.lag_p95
Schema drift,Registry,run,==0,schema_registry_drift,block_deploy,DATA,registry.schema_drift
API contract,INT Tests,run,OK,int.api_contract_break,rollback,INT,int.contract_status
Error budget burn,XLA,4h,<1x,slo_budget_breach,rollback,SRE,apm.error_budget_burn
Hook coverage %,CI,24h,>=98,metrics_decision_hook_gap,open_incident,PLAT,ci.hook_coverage
Audit coverage %,Logs,24h,>=99,metrics_decision_hook_gap,open_incident,PLAT,logs.audit_coverage
```

---

## 7) Hooks A110 — exercícios (validação)
```yaml
exercises:
  invariant_breach:
    inject: engine.swap_sequence(delta_k_ratio=1.5e-9, duration='2m')
    expect: action=='block_release' && alert.to=='DEC/PM'
  latency_budget:
    inject: apm.loadtest(rps=N*1.2, duration='10m')
    expect: action=='rollback' && error_budget_burn<1
  resolution_sla:
    inject: events.delay('resolution_finished', hours=25)
    expect: action=='freeze' && notify=='PM/BC'
  cdc_lag:
    inject: cdc.delay(p95='+180s', window='10m')
    expect: action=='degrade+rollback' && ticket.owner=='DATA'
  schema_drift:
    inject: registry.bump_version(incompatible=true)
    expect: action=='block_deploy' && pipeline.status=='halted'
  api_contract:
    inject: int.break_contract('mbp.v1')
    expect: action=='rollback' && release.status=='reverted'
  web_cwv_regression:
    inject: fe.inp_regress(p75='+80ms', window='24h')
    expect: action=='rollback_fe' && cwv.score>=baseline
```

---

## 8) ORR — **Gate Canary (M1)** (checklist)
- **Perf**: p95≤0,8s por 1h com **N rps**; 5xx=0; invariant=0.  
- **SLO**: error‑budget burn <1×/4h; P1=0.  
- **Observabilidade**: painéis publicados (DEC/MBP/FE/DATA/INT/SEC); acesso validado; alertas ativos.  
- **Hooks**: 100% carregados; dry‑run **pass**; fault‑injection **pass**; owners/rotas OK.  
- **Segurança/Privacidade**: SAST/Secrets/SBOM **sem críticos**; amostragem de logs **sem PII**.  
- **Change**: *Canary Plan* publicado (escopo, público, % tráfego, abort, comunicação).  
- **Assinaturas**: **PO, Eng (ST), Data (DC), SRE, FE, SEC/RSK**.

---

## 9) Plano de Canary (prod‑shadow → canary)
- **Fase 1 (Shadow)**: duplicar tráfego de 3 jornadas internas; sem efeito colateral.  
- **Fase 2 (1–5%)**: liberar para *beta users* internos; **abort** se: `error_budget_burn≥1x/4h` OU `invariant_breach>0` OU `5xx>0,1%` OU `INP p75>200ms`.  
- **Fase 3 (10–20%)**: após 24h verdes; manter **abort** preparado; report por hora ao PO.  
- **Comunicação**: statusboard, canal #mbp‑canary, *runbook abort* à mão.

---

## 10) Riscos & Mitigações (watcher/hook)
1) **Perf instável sob carga** → `slo_budget_breach` → **rollback** + *profiling*; throttle.  
2) **Telemetria incompleta** → `metrics_decision_hook_gap` → bloquear merge + completar eventos.  
3) **CDC lag** → `cdc_lag` → **degrade/rollback**; repriorizar ingest.  
4) **Regressão CWV/INP** → `web_cwv_regression` → **rollback_fe**.  
5) **Contrato/API** quebrado → `api_*` → **block_merge/rollback**.  
6) **Privacidade** → `dp_budget_breach` → freeze + auditoria.

---

## 11) Evidence Pack & Assinaturas
- **Evidências**: prints de dashboards, *trace_ids*, resultados de fault‑injection, relatórios SAST/Secrets/SBOM, *commit sha*.  
- **Assinaturas**: PO • ST • PY • DC • ML • SRE • FE • SEC/RSK.

---

## 12) Demo (Review) & Comunicação
- **Roteiro**: mostrar painéis (DEC/MBP/FE/DATA), simular um *spike* (ver freeze), demonstrar rollback por SLO burn, abrir/fechar *canary plan*.  
- **Materiais**: 1 slide executivo (OKRs, SLO, hooks exercitados), link para evidence pack, *post* interno de anúncio.

---

## 13) Pós‑Review → Prep **S3**
- Consolidar *gaps/waivers* (A106) com timebox e dono.  
- Planejar **S3**: **MVP** (templates, **resolução regrada**, **TWAP**/benchmarks, painel completo, anti‑abuso básico).  
- Pré‑work S3: selecionar *truth sources*, desenhar templates, definir parametrizações de TWAP (5m) e benchmarks.

---

## 14) Políticas & No‑Go (reafirmação)
- **Sem GA** sem 30d verdes e DoA cumprida; **sem deploy** com watcher crítico vermelho; **sem logs com PII**; **waivers** só com *timebox* + rollback.

---

> **Resultado esperado da S2**: **Gate Canary (M1) aprovado** com **telemetria 360°**, **hooks A110 exercitados**, **perf sob carga**, **segurança/privacidade** no verde e **plano de canary** publicado e assinado.

