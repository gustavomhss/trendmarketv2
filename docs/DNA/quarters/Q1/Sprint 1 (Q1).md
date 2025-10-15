# Q1 • Sprint 1 — MBP Slice 0 (Walking Skeleton) • v1.1 FINAL (deepdive 5×)
> **Alinhado a**: *Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)* e *Roadmap — Kickoff Intake (CE$) • V1 (2025‑09‑10)*.  
> **Objetivo (2 semanas):** erguer o **esqueleto funcional do MBP** (CPMM x·y=k + UI mínima + resolução manual + auditoria básica) e **atingir Gate Pre‑deploy** em `stage` com **evidências fechadas**.

---

## 0) Delta v1.0 → v1.1 (o que foi elevado)
- **Exits 100% quantitativos** com *queries/ids* de evidência e **assinaturas** (PO/Eng/Data/SRE).  
- **DoR/DoD reforçados** (SBOM, SAST/Secrets, cobertura de testes, LGPD A108, A11x hooks).  
- **Teste de performance** com carga‑alvo e *perf budget* (p95≤0,8s; throughput alvo).  
- **Plano de Telemetria** granular (eventos/métricas/traces), **dashboards** e **alarmes** prontos.  
- **Runbooks v1** (Invariante; Resolução; CWV/INP; Staleness/Quórum) com **drill** agendado.  
- **Riscos→Hooks** com *playbooks* e **Kill** intra‑sprint documentados.  
- **Qualidade de engenharia**: trunk‑based + code review 2‑olhos; *coverage* ≥ 80% em engine; *lint*/format no CI; *feature flags* catalogadas.

---

## 1) Sprint Goal + DoA (S1)
**Sprint Goal:** MBP “andando” em `stage` com governança base ativa.  
**DoA da S1:**  
- **Engine** CPMM com **Δk/k ≤ 1e−9 (60 min)**; **goldens=pass**; **lat p95 ≤ 0,8s**.  
- **UI** preço⇄prob + criador básico (atrás de **flag**) com **INP p75 ≤ 200ms** e RUM ligado.  
- **Resolução** manual fim‑a‑fim (eventos + SLA medido).  
- **Audit**: ≥ **95%** de ações críticas com `trace_id` + `commit_sha`.  
- **A110**: watchers **carregados, verdes**, donos definidos e *health‑check* passando.

---

## 2) Definition of Ready (DoR)
- **Ambientes**: `dev` e `stage` ativos; *feature flags* criadas (`mbp.create_market`, `mbp.resolve.manual`).  
- **Acessos**: CI/CD, APM/Logs/Traces, *schema registry*, repositórios (app/infra/dados).  
- **Contratos**: `mbp.events.v1` registrado (A106/A87); políticas de log **sem PII** (A108).  
- **Qualidade**: *linters* e *pre‑commit* habilitados; *test harness* para engine; **golden dataset v0** pronto.  
- **Segurança**: SAST, *secret scan* e **SBOM** no pipeline; deps críticas=0.

---

## 3) Escopo S1 (alto nível — sem backlog CSV)
- **Engine/DEC**: CPMM (`x·y=k`) com *quote/swap* (sem dinheiro real); *goldens* + `amm.invariant_error`.  
- **UI/FE**: painel preço⇄prob; criador mínimo (flagged); RUM (INP).  
- **Resolução**: fluxo manual `resolution_started`→`resolution_finished`; SLA em horas.  
- **Audit/Logs**: `trace_id`, `commit_sha`, `market_id`, `user_id_hash` (tokenizado); filtros.  
- **Observabilidade**: spans `amm.quote`, `amm.swap`, `resolution.rule`, `audit.write`; métricas definidas no *Measurement Sheet*.  
- **Hooks/Watchers**: carregar e validar must‑have (`amm_invariant_breach`, `resolution_sla`, `liquidity_depth`, `price_spike_divergence`, `abuse_anomaly`, `dec.latency_p95`, `web_cwv_regression`, `cdc_lag`, `schema_drift`, `data_contract_break`, `slo_budget_breach`).  
- **Segurança/Privacidade**: logs sem PII; *least privilege*; deps sem CVE crítico.  
- **Artefatos**: **ADR‑001** (Engine MBP), **Measurement Sheet (S1)**, **Runbook Invariante v1**.

**Fora do escopo S1**: TWAP/benchmarks/oráculos (entrarão em S3); auto‑resolução; anti‑abuso avançado; fees dinâmicos; backtesting.

---

## 4) Plano de 10 dias (quem faz o quê)
**D1** — *kick*: planning técnico; flags; bootstrap repo; ADR‑001 rascunho; checagem de acessos.  
**D2** — engine *quote/swap*; **goldens v0**; métrica `invariant_error`; scaffold UI + RUM.  
**D3** — *perf pass* inicial (profiling); criador de mercado (flag); *schema registry* dos eventos.  
**D4** — resolução manual + eventos; audit trail (`trace_id`/`commit_sha`); dashboards p95/erro budget.  
**D5** — carregar **hooks A110** com limiares; owners; *health-check* `green`.  
**D6** — hardening CPMM (precisão); **goldens v1**; tuning p95; *secrets scan*; SBOM.  
**D7** — **drill Runbook Invariante** (simulado); revisão *Measurement Sheet*; ajuste janelas/limiares hooks.  
**D8** — *stage dry run* (E2E): criar→negociar→resolver; validar telemetria.  
**D9** — *bug‑bash* multi‑papel; p95≤0,8s; audit≥95%; PR/Review 2‑olhos.  
**D10** — Review/Demo; Retro; **Gate Pre‑deploy**.

> **Capacidade**: {PO:0,5 • ST:1,0 • PY:1,0 • DC:0,5 • ML:1,0 • SRE:0,5 • FE:0,5}. **WIP máx**: 2 por trilha.

---

## 5) Test Plan & Perf Budget (S1)
**Testes**: unit (engine) ≥ **80%**; integração (API) ≥ **60%**; E2E feliz e 2 infelizes.  
**Carga/Throughput alvo** (stage): **N rps** (configurar no ORR) por 15 min, p95≤0,8s, `invariant=0`.  
**Condições de aprovação**: zero *invariant breach*; p95 dentro; 0 erros 5xx.

---

## 6) Measurement Sheet — S1
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
Latency p95 (ms),APM/Traces,5m,<=800,slo_budget_breach,rollback,SRE,apm.ttp_dec_p95
Invariant error,Engine,1m,==0,amm_invariant_breach,block_release,DEC/PM,engine.amm_invariant
INP p75 (ms),RUM,24h,<=200,web_cwv_regression,rollback_fe,FE,rum.inp_p75
Resolution SLA (h),Events,24h,<=24,mbp_resolution_sla,freeze,PM/BC,events.resolution_sla
Audit coverage %,Logs,24h,>=95,metrics_decision_hook_gap,open_incident,PLAT,logs.audit_coverage
Hook coverage %,Repo/CI,24h,>=98,metrics_decision_hook_gap,open_incident,PLAT,ci.hook_coverage
```

---

## 7) Watchers & Hooks — validação (S1)
```yaml
checks:
  hooks_loaded:    ci.query('hook_registry_loaded == true')
  owners_present:  ci.query('hook_owner_missing == 0')
  health_green:    apm.query('mbp_watchers_green >= 95')
exercises:
  invariant:       engine.test('swap_sequence', assert='abs(x*y-k)/k < 1e-9')
  p95_latency:     apm.loadtest('N_rps', target_p95_ms=800)
  resolution_sla:  events.simulate('resolution_delay_h=23')
```

---

## 8) Riscos & Runbooks (vinculados)
1) **Invariante quebra** → `amm_invariant_breach` → **Runbook Invariante v1**: HALT pool → Δk → reprocesso → post‑mortem (≤24h).  
2) **p95 acima** → `slo_budget_breach` → **Runbook Perf**: rollback/degrade; *profiling*; cache; GC.  
3) **INP regressão** → `web_cwv_regression` → **Runbook FE**: rollback; mitigar; re‑medir RUM.  
4) **Telemetria faltante** → `metrics_decision_hook_gap` → **Runbook Telemetry**: abrir incidente; bloquear merge; completar eventos.  
5) **Logs com PII** → `dp_budget_breach` → **Runbook Privacidade**: freeze; mascarar; auditoria.

---

## 9) ORR — Gate Pre‑deploy (checklist)
- **DRIs/oncall** definidos; *feature flags* catalogadas e testadas.  
- **Rollback** testado em `stage`; *kill‑switch* catalogado.  
- **Dashboards** (p95, invariant, audit, hook coverage) publicados e acessíveis.  
- **SAST/Secrets/SBOM**: sem críticos; CVEs mitigadas.  
- **Evidence pack**: *screens* + trace_ids + *commit sha* anexados.  
- **Assinaturas**: **PO, Eng (ST), Data (DC), SRE**.

---

## 10) Demo (roteiro e AC Given/When/Then)
**Roteiro**: criar mercado (template) → adicionar liquidez simulada → executar swaps → monitorar painel preço/prob → iniciar & concluir resolução manual → inspecionar audit trail & métricas (p95/invariant).  
**AC principais**:  
- *Given* sequência de swaps; *When* executar; *Then* `abs(x*y-k)/k ≤ 1e−9` e p95≤0,8s.  
- *Given* mercado resolvido; *When* finalizar; *Then* `resolution_hours ≤ 24` e evento `resolution_finished` com `trace_id`.

---

## 11) Kill intra‑sprint & Waivers
- **Kill**: 1× *invariant breach* pós‑fix não resolvido em 24h; `error_budget_burn≥1x/4h` por 2 janelas; falha de segurança crítica.  
- **Waivers**: só com **timebox** + plano de rollback (A106) e aprovação **PO+Eng+Data+SRE**.

---

## 12) Comunicação & Change
- *Release notes* curtas (scope, métricas, hooks).  
- *Standup notes* com riscos/impedimentos; *incident channel* definido.  
- *Stakeholder ping* no **M‑checkpoint (D5)** e **pre‑Gate (D9)**.

---

> **Resultado esperado**: **Gate Pre‑deploy aprovado** com MBP esquelético funcional, **telemetria mínima** e **governança base** ativada, evidências publicadas e *sign‑off* concluído.

