# Q1 • Sprint 3 — MBP Slice 1 (MVP interno) • v1.1 FINAL (deepdive 10×)
> **Alinhado a**: *Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)*, *S1 v1.1*, *S2 v1.1*, e *Roadmap — Kickoff Intake (CE$) • V1 (2025‑09‑10)*.  
> **Objetivo (2 semanas)**: entregar o **MVP interno do MBP** com **templates de mercado**, **resolução regrada (Truth Source)**, **TWAP/benchmarks (5m)**, **painel completo** e **anti‑abuso básico**, atingindo **Gate Release**.

---

## 0) Delta S2 → S3 (elevações)
- **Resolução regrada**: implementação do **Rule Engine** (Truth Source) e manual fallback.  
- **TWAP/Benchmarks (5m)**: cálculo on‑line + janelas configuráveis; divergência ≤ **1,0%**.  
- **Templates de Mercado**: catálogo versionado (+ validações) e criador por template.  
- **Painel completo**: preço, prob, TWAP, profundidade, eventos e trilha.  
- **Anti‑abuso básico**: flags/anomalias (volume anômalo, burst trades, manipulação), com *rate limits* e pausas.  
- **Observabilidade**: eventos e spans adicionais (rule.eval, twap.compute, abuse.detect).  
- **Dados/CDC**: contratos e *dbt tests* para `mbp_markets`, `mbp_quotes`, `mbp_resolutions`, `mbp_abuse_events`.  
- **Segurança/Privacidade (A108)**: auditoria de exibição de regra; logs sem PII; *least privilege*.  
- **Runbooks**: Resolução Regrada, TWAP Divergência, Abuso/Moderação.

---

## 1) Sprint Goal & DoA (S3)
**Sprint Goal:** colocar o **MVP interno** em *prod* com **Gate Release** aprovado.  
**Definition of Awesome (S3):**  
- **Mercados ativos**: **5–10** internos.  
- **Liquidez**: **depth@2% ≥ 500** unidades.  
- **Resolução**: ≤ **24h** em 100% dos casos S3.  
- **Preço**: **TWAP divergence ≤ 1,0%** (5m).  
- **Perf**: **TTPV p95 ≤ 0,8s**; **INP p75 ≤ 200ms**; **invariant=0**.  
- **Confiabilidade**: **P1=0**; **error‑budget burn < 1×/4h** (janela Release).  
- **Governança**: **audit trail** 99%+ ações; **watchers must‑have** verdes.

---

## 2) Definition of Ready (DoR)
- **ADRs** aprovados: Resolução Regrada (Truth Source), TWAP/Benchmarks, Anti‑Abuso.  
- **Templates** definidos (tipos, constraints, validações); *feature flags* (`mbp.create.by_template`).  
- **Contratos de dados** registrados (A106/A87) e *dbt tests* esqueleto criados.  
- **Ambientes & acessos**: APM/Logs/Traces/RUM; schema registry; CI/CD; *prod‑shadow*.  
- **Watchers/Hooks**: *owners* confirmados e limiares validados (A110).

---

## 3) Escopo S3 (alto nível — sem backlog CSV)
- **Templates de Mercado**  
  - Catálogo versionado (id, categoria, truth_source, parâmetros).  
  - Validações: *name*, *resolution_window*, *min_liquidity*, *truth_source*.  
  - Criador por template (atrás de flag) + pré‑visualização.  
- **Resolução Regrada (Truth Source)**  
  - **Rule Engine**: fontes de verdade (tabela/manual/endpoint interno).  
  - Workflow: `resolution_started` → `rule_eval` → `resolution_finished`.  
  - Fallback: **manual** (com evidência e aprovação).  
- **TWAP/Benchmarks (5m)**  
  - TWAP 5m com janelas 1/5/15m; *benchmarks* opcionais; *alert* de divergência.  
  - Exposição no painel e eventos de recalculo.  
- **Painel completo**  
  - Preço, prob, TWAP, profundidade, ordens recentes, eventos, trilha de auditoria.  
- **Anti‑Abuso básico**  
  - *Rate limit* por usuário/mercado, *cooldown* pós‑spike, detecção de burst trades.  
  - Fluxo de **pausa de mercado** + moderação (evidências).  
- **Observabilidade A71–A72**  
  - Spans: `rule.eval`, `twap.compute`, `abuse.detect`; correlação com audit.  
  - Eventos: `market_created_template`, `twap_recomputed`, `abuse_flagged`.  
- **Dados & CDC**  
  - Tabelas: `mbp_markets`, `mbp_quotes`, `mbp_resolutions`, `mbp_abuse_events`.  
  - **dbt tests** (unique/not null/FKs) e expectativas; *CDC lag p95 ≤ 120s*.  
- **Segurança/Privacidade (A108)**  
  - Logs sem PII; guarda de decisões/regras; *redaction* e *least‑privilege*.  
- **Documentação/Runbooks**  
  - ADRs 002–004; Runbooks: Resolução, TWAP, Anti‑Abuso; Measurement Sheet S3.

**Fora do escopo S3**: oráculos externos/auto‑resolução (→ **S5**); fees dinâmicos e simulações profundas; moderação avançada.

---

## 4) Plano de 10 dias (quem faz o quê)
**D1** — Templates: schema/validações; flag on em *stage*; painel: seções TWAP/depth.  
**D2** — Rule Engine (Truth Source): contrato; eventos `rule_eval`.  
**D3** — TWAP compute (1/5/15m); eventos `twap_recomputed`.  
**D4** — Anti‑abuso: rate limits + burst detector; `abuse_flagged`.  
**D5** — Dados/CDC: modelos `mbp_*`; *dbt tests*; dashboards.  
**D6** — Observabilidade: spans `rule.eval|twap.compute|abuse.detect`; correlação audit.  
**D7** — Perf: *load* com mercados 5–10; p95≤0,8s; invariant=0; depth@2%≥500.  
**D8** — Drill Runbooks: Resolução, TWAP, Abuso (simulados).  
**D9** — *Bug‑bash* e *dry‑run* de Release (checklist, owners, aborts).  
**D10** — Review/Demo; Retro; **Gate Release**.

> **Capacidade**: {PO:0,5 • ST:1,0 • PY:1,0 • DC:0,5 • ML:1,0 • SRE:0,5 • FE:0,5}.  
> **WIP máx**: 2 por trilha (Templates/Resolução/TWAP/Obs/FE/Dados).

---

## 5) Test Plan & Perf Budget (S3)
**Funcional**: criação por template; resolução via regra; fallback manual com evidência.  
**Perf**: 5–10 mercados ativos; **N rps** (ORR); **p95 ≤ 0,8s**; **invariant=0**.  
**Preço**: validar **TWAP divergence ≤ 1,0%** com *spike tests*.  
**Liquidez**: medir **depth@2% ≥ 500** com ordens programáticas.  
**Abuso**: simular *bursts* e *rate‑limit*; pausar/retomar mercado.  
**Dados**: *dbt tests* e *CDC lag p95 ≤ 120s*.  
**UX**: INP p75≤200ms; RUM ativo; regressão CWV bloqueia deploy.  
**Aprovação**: todos **watchers** verdes; **P1=0**; *evidence pack* completo.

---

## 6) Measurement Sheet — S3
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
Mercados ativos (#),Engine,24h,>=5 e <=10,metrics_decision_hook_gap,open_incident,PM,engine.markets_active
Depth@2% (unid),Engine,15m,>=500,mbp_liquidity_depth,degrade,PM,engine.depth_2pct
TWAP divergence %,Engine,5m,<=1.0,mbp_price_spike_divergence,freeze,PM/SRE,engine.twap_gap
Resolution SLA (h),Events,24h,<=24,mbp_resolution_sla,freeze,PM/BC,events.resolution_sla
TTPV p95 (ms),APM/Traces,5m,<=800,slo_budget_breach,rollback,SRE,apm.ttp_dec_p95
Invariant error,Engine,1m,==0,amm_invariant_breach,block_release,DEC/PM,engine.amm_invariant
INP p75 (ms),RUM,24h,<=200,web_cwv_regression,rollback_fe,FE,rum.inp_p75
Abuse flags (#/h),Logs,1h,<=limiar,mbp_abuse_anomaly,alert+moderation,SEC/PM,logs.abuse_flags
CDC lag p95 (s),CDC/APM,5m,<=120,cdc_lag,degrade+rollback,DATA,cdc.lag_p95
Audit coverage %,Logs,24h,>=99,metrics_decision_hook_gap,open_incident,PLAT,logs.audit_coverage
Hook coverage %,CI/Repo,24h,>=98,metrics_decision_hook_gap,open_incident,PLAT,ci.hook_coverage
```

---

## 7) Hooks A110 — exercícios S3 (validação/fault‑injection)
```yaml
exercises:
  price_spike_divergence:
    inject: engine.price_spike(delta_pct=1.5, window='2m')
    expect: action=='freeze' && notify.contains('PM/SRE')
  liquidity_depth_gap:
    inject: engine.remove_liquidity(to_depth_2pct=400)
    expect: action=='degrade_route' && route=='liquidity_program'
  resolution_sla_breach:
    inject: events.delay('resolution_finished', hours=25)
    expect: action=='freeze' && owner=='PM/BC'
  abuse_burst:
    inject: engine.burst_trades(rate='x3', duration='5m')
    expect: action=='alert+moderation' && market.status in ['paused','limited']
  cdc_lag:
    inject: cdc.delay(p95='+180s', window='10m')
    expect: action=='degrade+rollback' && ticket=='DATA'
```

---

## 8) ORR — **Gate Release (S3)** (checklist)
- **Mercados ativos 5–10**; **depth@2% ≥ 500**; **TWAP divergence ≤ 1,0%**.  
- **Perf**: **TTPV p95 ≤ 0,8s**; **invariant=0**; **P1=0**.  
- **Watchers**: 100% must‑have **verdes**; exercícios de hooks **pass**.  
- **Dados/CDC**: *dbt tests* ok; **CDC lag p95 ≤ 120s**.  
- **Segurança/Privacidade**: logs sem PII; dep/SAST/**SBOM** sem críticos.  
- **Change**: *Release Plan* publicado (escopo, rollback, comunicação).  
- **Assinaturas**: **PO, Eng (ST), Data (DC), SRE, FE, SEC/RSK**.

---

## 9) Riscos & Mitigações (watcher/hook)
1) **Liquidez insuficiente** → `mbp_liquidity_depth` → **degrade** para programa/roteamento.  
2) **TWAP > 1%** → `mbp_price_spike_divergence` → **freeze** + investigação; ajuste de janelas.  
3) **Resolução atrasada** → `mbp_resolution_sla` → **freeze** + fallback manual.  
4) **Abuso/manipulação** → `mbp_abuse_anomaly` → **pause/limit** mercado; moderação.  
5) **CDC lag** → `cdc_lag` → **degrade/rollback**; priorizar ingest.

---

## 10) Evidence Pack & Assinaturas
- **Evidências**: dashboards (depth/TWAP/p95), *trace_ids*, relatórios *dbt/CDC*, prints do painel e *rule eval*, resultados de exercícios A110, *commit sha*.  
- **Assinaturas**: PO • ST • PY • DC • ML • SRE • FE • SEC/RSK.

---

## 11) Demo (Review)
- **Roteiro**: criar por template → prover liquidez programática → negociar → observar painel (TWAP/profundidade) → acionar resolução regrada (e ver *rule eval* + audit) → simular *spike* para congelamento → reabrir após normalização.  
- **AC (Given/When/Then)**:  
  - *Given* janela de 5m; *When* computar TWAP; *Then* `|price−twap|/twap ≤ 1,0%`.  
  - *Given* mercado resolvido; *When* aplicar regra; *Then* `resolution_hours ≤ 24` e trilha OK.  
  - *Given* trades programáticos; *When* medir profundidade; *Then* `depth@2% ≥ 500`.

---

## 12) Pós‑Review → Prep **S4**
- Mapear *gaps/waivers* (A106) com dono + timebox.  
- Planejar **S4**: **hardening MVP** + **CE$ Fundações** (DEC p95≤0,8s; contratos/dbt; schema registry; ADRs 001–003 aprovados).  
- Pré‑work: ajustar limiares TWAP, parametrizar templates; reforço de *dbt tests*.

---

## 13) Políticas & No‑Go (reafirmação)
- **Sem Release** com watchers críticos vermelhos; **sem logs com PII**; **waivers** só com *timebox* + rollback e aprovação **PO+Eng+Data+SRE**.

---

> **Resultado esperado da S3**: **Gate Release aprovado** com **MVP interno** no ar, **templates**, **resolução regrada**, **TWAP/benchmarks (5m)**, **painel completo**, **anti‑abuso básico**, **telemetria 360°**, **dados/CDC** e **governança A110** ativas.

