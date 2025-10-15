# Q1 • Sprint 4 — MVP Hardening + CE$ Fundações (DEC≤0,8s • A106/A87/A89 • dbt • Schema Registry • ADRs) • v1.1 FINAL (deepdive 10×)
> **Alinhado a**: *Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)*, *S1 v1.1*, *S2 v1.1*, *S3 v1.1*, e *Roadmap — Kickoff Intake (CE$) • V1/v0.2 (Jeff Patton)*.  
> **Objetivo (2 semanas)**: **endurecer o MVP do MBP** e **fechar CE$ Fundações** com **DEC p95 ≤ 0,8s**, **CDC lag p95 ≤ 120s**, **Schema Registry sem drift**, **contratos A106/A87/A89** com **dbt tests** e **ADRs 001–003 aprovados**, atingindo **Gate Pre‑GA (M2)**.

---

## 0) Delta S3 → S4 (elevações)
- **DEC/Perf**: tuning do pipeline (roteamento, cache, GC, conexões), com **p95 ≤ 0,8s** estável em carga‑alvo.  
- **Dados/CDC**: contratos **A106/A87/A89** concluídos para domínios MBP; **dbt tests** (unique/not null/FKs/expectations) + monitor DQ; documentação ≥ **95%**.  
- **Schema Registry**: versões **semver**, *compat rules* ativas; **schema_drift=0**.  
- **Governança**: **Hook Coverage ≥ 98%**; **Audit Coverage ≥ 99%**; owners de watchers confirmados.  
- **ADRs 001–003**: DEC; Resolução Regrada; TWAP/Benchmarks — **aprovados**.  
- **Segurança/Privacidade (A108)**: amostragem de logs 100% **sem PII**; SBOM/SAST/Secrets **sem críticos**.

---

## 1) Sprint Goal & DoA (S4)
**Sprint Goal:** deixar **CE$ Fundações “verde”** e o **MVP MBP endurecido**, prontos para **Pre‑GA (M2)**.  
**Definition of Awesome (S4):**  
- **DEC p95 ≤ 0,8s** por ≥ 1h na carga‑alvo (**N rps**, ORR).  
- **CDC lag p95 ≤ 120s** nas tabelas quentes MBP (`mbp_markets`, `mbp_quotes`, `mbp_resolutions`, `mbp_abuse_events`).  
- **Schema drift = 0**; **data_contract_break = false**; **dbt tests=pass**.  
- **Hook Coverage ≥ 98%**; **Audit Coverage ≥ 99%** (rolling 24h).  
- **ADRs 001–003 aprovados** e arquivados.  
- **P1=0**; **error‑budget burn < 1×/4h** (janela S4).  
- **INP p75 ≤ 200ms** (painel MBP) — sem regressão CWV.

---

## 2) Definition of Ready (DoR)
- **Ambientes**: `dev`/`stage` estáveis; `prod‑shadow` liberado.  
- **Acessos**: APM/Logs/Traces/RUM; **schema registry**; **CI/CD**; notebooks de goldens.  
- **Contratos**: rascunhos A106/A87/A89 criados (S3) e campos críticos definidos.  
- **Observabilidade**: painéis S3 publicados; alarmes base ativos.  
- **Governança**: matriz de owners (watchers) revisada; queries do Measurement Plan disponíveis.

---

## 3) Escopo S4 (alto nível — sem backlog CSV)
- **DEC (Performance/Confiabilidade)**  
  - *Profiling* + ajustes (pool de conexões, GC, cache de preço, roteamento rápido).  
  - Testes de estresse (picos/caudas); *graceful degrade* por SLO.  
- **Dados/CDC & Contratos (A106/A87/A89)**  
  - Finalizar contratos para `mbp_markets|quotes|resolutions|abuse_events`.  
  - **dbt tests**: unique/not null/FKs + regras de consistência (ex.: market fechado ⇒ sem novos trades).  
  - **DQ**: monitoração e alertas; documentação ≥95% pacote MBP.  
  - **CDC**: garantir `lag p95 ≤ 120s` + alarmes e *runbook*.  
- **Schema Registry**  
  - Políticas de compatibilidade; *lint* de schema; automação de *breaking checks* no CI; **drift=0**.  
- **Governança/Observabilidade**  
  - **Hook Coverage ≥ 98%**; **Audit Coverage ≥ 99%**; owners/rotas de alerta confirmados.  
  - Painéis consolidados (DEC/MBP/DATA/FE) + alertas de **error budget**, **cdc lag**, **schema drift**, **decision gap**.  
- **Segurança/Privacidade (A108)**  
  - Amostragem de logs **sem PII**; SBOM/SAST/Secrets **verdes**; *least‑privilege* revisado.  
- **ADRs 001–003**  
  - Fechamento e publicação (DEC; Rule Engine; TWAP).  
- **FE (RUM/CWV)**  
  - Verificações INP p75; *no‑regression*; *preload/hydration* mínimo se necessário.

**Fora do escopo S4**: auto‑resolução por oráculo (→ **S5**); fees dinâmicos; backtesting/simulação avançada; moderação avançada.

---

## 4) Plano de 10 dias (quem faz o quê)
**D1** — DEC: *profiling* e plano de remediação; DATA: priorizar A106/A87/A89; SRE: baseline de carga.  
**D2** — DEC: cache/roteamento; DATA: *dbt tests* (unique/not null/FKs); SRE: alarmes de **error budget**.  
**D3** — DEC: *stress* com picos; DATA: regras de consistência; FE: revisão INP p75.  
**D4** — Registry: compat rules; CI com *breaking checks*; DATA: documentação (≥95%).  
**D5** — CDC: otimização ingest; alarmes; drill *Runbook CDC*.  
**D6** — Observabilidade: painéis consolidados; *decision gap* watcher; *web CWV* verificado.  
**D7** — Segurança: SBOM/SAST/Secrets; *least‑privilege*; auditoria de logs.  
**D8** — **Fault‑injection**: `schema_drift`, `contract_break`, `cdc_delay`, `lat_p95`.  
**D9** — *Bug‑bash*; *perf pass* (p95≤0,8s); *dbt tests=pass*; documentação verificada.  
**D10** — Review/Demo; Retro; **Gate Pre‑GA (M2)**.

> **Capacidade**: {PO:0,5 • ST:1,0 • PY:1,0 • DC:0,5 • ML:1,0 • SRE:0,5 • FE:0,5}.  
> **WIP máx**: 2 por trilha (DEC/DATA/Registry/Obs/FE/SEC).

---

## 5) Test Plan & Perf Budget (S4)
**Perf**: carga‑alvo **N rps** em `stage` por 60 min; **p95 ≤ 0,8s**; 5xx=0; *graceful degrade* acionando rollback quando necessário.  
**Dados**: *dbt tests* verdes; **schema_drift=0**; **contract_break=false**; documentação ≥95%.  
**CDC**: **lag p95 ≤ 120s**; *alert* e *runbook* verificados.  
**Gov/Obs**: **Hook Coverage ≥ 98%**; **Audit Coverage ≥ 99%**; alarmes testados.  
**FE**: **INP p75 ≤ 200ms** (sem regressão).  
**Aprovação**: P1=0; **error‑budget burn < 1×/4h**.

---

## 6) Measurement Sheet — S4
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
DEC p95 (ms),APM/Traces,5m,<=800,slo_budget_breach,rollback,SRE,apm.ttp_dec_p95
CDC lag p95 (s),CDC/APM,5m,<=120,cdc_lag,degrade+rollback,DATA,cdc.lag_p95
Schema drift,Registry,run,==0,schema_registry_drift,block_deploy,DATA,registry.schema_drift
Data contract break,CI/Tests,run,false,data_contract_break,rollback+waiver,DATA,ci.data_contract_status
DBT tests status,CI/dbt,run,pass,dbt_test_failure,block_merge,DATA,dbt.test_status
Hook Coverage %,CI/Repo,24h,>=98,metrics_decision_hook_gap,open_incident,PLAT,ci.hook_coverage
Audit Coverage %,Logs,24h,>=99,metrics_decision_hook_gap,open_incident,PLAT,logs.audit_coverage
INP p75 (ms),RUM,24h,<=200,web_cwv_regression,rollback_fe,FE,rum.inp_p75
Error budget burn,XLA,4h,<1x,slo_budget_breach,rollback,SRE,apm.error_budget_burn
TWAP divergence %,Engine,5m,<=1.0,mbp_price_spike_divergence,freeze,PM/SRE,engine.twap_gap
```

---

## 7) Hooks A110 — exercícios (validação)
```yaml
exercises:
  schema_drift:
    inject: registry.bump_version(incompatible=true)
    expect: action=='block_deploy' && pipeline.status=='halted'
  data_contract_break:
    inject: ci.break_data_contract('mbp.quotes.v1')
    expect: action=='rollback+waiver_timebox' && owner=='DATA'
  dbt_failure:
    inject: dbt.fail_test('mbp_resolutions_fk')
    expect: action=='block_merge' && pr.status=='blocked'
  cdc_delay:
    inject: cdc.delay(p95='+180s', window='10m')
    expect: action=='degrade+rollback' && ticket.owner=='DATA'
  dec_latency:
    inject: apm.loadtest(rps=N*1.2, duration='10m')
    expect: action=='rollback' && error_budget_burn<1
  web_inp_regression:
    inject: fe.inp_regress(p75='+80ms', window='24h')
    expect: action=='rollback_fe'
```

---

## 8) ORR — **Gate Pre‑GA (M2)** (checklist)
- **Perf (DEC)**: p95≤0,8s por 1h com N rps; 5xx=0; degrade/rollback testado.  
- **Dados/CDC**: *dbt tests* **pass**; **schema_drift=0**; **contract_break=false**; **CDC lag p95≤120s**.  
- **Governança**: **Hook Coverage≥98%**; **Audit Coverage≥99%**; owners/rotas de alerta **OK**.  
- **ADRs 001–003**: publicados; *decision log* anexado.  
- **Segurança/Privacidade**: SBOM/SAST/Secrets sem críticos; amostragem de logs **sem PII**.  
- **Change**: *Pre‑GA Plan* (escopo/flags/rollback/comunicação).  
- **Assinaturas**: **PO, Eng (ST), Data (DC), SRE, FE, SEC/RSK, INT**.

---

## 9) Riscos & Mitigações (watcher/hook)
1) **DEC p95>800ms** → `slo_budget_breach` → **rollback/degrade** + *profiling*; ajuste de cache/GC.  
2) **CDC lag** → `cdc_lag` → **degrade/rollback**; priorizar ingest.  
3) **Schema drift/contract break** → `schema_registry_drift`/`data_contract_break` → **block_deploy/rollback**.  
4) **dbt failures** → `dbt_test_failure` → **block_merge** até correção.  
5) **CWV regressão** → `web_cwv_regression` → **rollback_fe**.

---

## 10) Evidence Pack & Assinaturas
- **Evidências**: prints de dashboards (DEC/CDC/Hook/Audit), *trace_ids*, relatórios **dbt/CI**, *commit sha*, ADRs 001–003, resultados de exercícios A110.  
- **Assinaturas**: PO • ST • PY • DC • ML • SRE • FE • SEC/RSK • INT.

---

## 11) Demo (Review)
- **Roteiro**: mostrar painéis consolidados; provar p95≤0,8s; exibir **schema registry** (sem drift) e **dbt tests** *pass*; simular **cdc delay** (ver *degrade/rollback*); destacar **ADRs** e **evidence pack**.  
- **AC (Given/When/Then)**:  
  - *Given* janelas de 5m; *When* medir DEC; *Then* `p95≤800ms` e **error budget OK**.  
  - *Given* contratos publicados; *When* rodar CI/dbt; *Then* `tests=pass` e `schema_drift=0`.

---

## 12) Pós‑Review → Prep **S5**
- Consolidar *gaps/waivers* (A106) com dono/timebox.  
- Planejar **S5**: **Slice 2 / Escala** (auto‑resolução por oráculo; fees dinâmicos; simulação/backtesting; moderação avançada; feature flags).  
- Pré‑work: rascunhos de auto‑resolução; parametrização de fees; selecionar cenários de simulação; reforçar *benchmarks*.

---

## 13) Políticas & No‑Go (reafirmação)
- **Sem Pre‑GA** com watcher crítico vermelho; **sem logs com PII**; **waivers** só com *timebox* + rollback e aprovação **PO+Eng+Data+SRE**.

---

> **Resultado esperado da S4**: **Gate Pre‑GA (M2) aprovado** com **CE$ Fundações verde**, **DEC ≤ 0,8s**, **CDC ≤ 120s**, **schema drift=0**, **contratos/documentação/dbt** ok, **ADRs 001–003** publicados, **governança A110** e **observabilidade consolidada**.

