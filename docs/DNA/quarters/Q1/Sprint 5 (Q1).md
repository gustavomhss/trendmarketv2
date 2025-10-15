# Q1 • Sprint 5 — MBP Slice 2 (Escala) • v1.1 FINAL (deepdive 100×)
> **Alinhado a**: *Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)*, *S1 v1.1*, *S2 v1.1*, *S3 v1.1*, *S4 v1.1*, e *Roadmap — Kickoff Intake (CE$) • V0.2 (Jeff Patton)*.  
> **Objetivo (2 semanas)**: escalar o **MBP** com **Oráculos v1 (quórum+TWAP/failover)**, **Auto‑Resolução regrada**, **Fees Dinâmicos** e **Simulação/Backtesting** + **Moderação Avançada**, atingindo **Gate GA‑Ready (M3)** e deixando o sistema pronto para iniciar os **30 dias verdes** na **S6**.

---

## 0) Delta S4 → S5 (elevações)
- **Oráculos v1 (Brasil)**: adaptadores + **quórum 2/3** (configurável), **TWAP 5m** com **failover** automático e **staleness ≤ 30s** / **divergência ≤ 1,0%**.  
- **Auto‑Resolução**: pipeline governado por regra (**Truth Source**) + quórum; *fallback* manual com evidência.  
- **Fees Dinâmicos**: `fee(t) = base + α·vol(t) + β·(1/depth(t))`, *bounds* [**bmin,bmax**], *cooldown* e **anti‑thrash** (Δfee≤20%/5m).  
- **Simulação & Backtesting**: *harness* reprodutível com cenários (picos, gaps, bursts) e replay de eventos.  
- **Moderação Avançada**: pause/limit por heurística + evidências e fluxos de apelação.  
- **Observabilidade A71–A72**: spans novos (`oracle.fetch`, `auto_resolve.eval`, `fee.update`, `sim.run`, `moderation.apply`) e painéis.  
- **Dados/CDC**: contratos A106/A87 para `oracle_quotes`, `twap_series`, `fees_config`, `simulation_runs`, `moderation_events` + **dbt tests**.

---

## 1) Sprint Goal & DoA (S5)
**Sprint Goal:** habilitar **GA‑Ready (M3)** para o MBP com oráculos/auto‑resolução/fees dinâmicos/moderação avançada/telemetria completa.

**Definition of Awesome (S5):**  
- **Oráculos**: `staleness ≤ 30s` (p95), `divergência ≤ 1,0%` (5m), **quórum≥2/3** ativo, **failover TWAP < 60s**.  
- **Auto‑Resolução**: **p95 ≤ 2h** (mediana ≤ 60m) pós‑evento; 100% trilha/auditoria; *fallback* manual testado.  
- **Preço/Integridade**: **TWAP divergence ≤ 1,0%**; **Invariant error = 0**.  
- **Fees**: Δfee/5m ≤ **20%**; `fee ∈ [bmin,bmax]`; **spread** estável; sem regressão de **TTPV p95 ≤ 0,8s**.  
- **Moderação**: **MTTD ≤ 5m** e **MTTM ≤ 15m** para abuso; pausa/reabertura com evidências.  
- **Confiabilidade**: **P1=0**; **error‑budget burn < 1×/4h**; **watchers must‑have 100% verdes**.  
- **Governança**: **Hook Coverage ≥ 98%**; **Audit Coverage ≥ 99%**; **ADRs 004–006** (Oráculos, Fees, Moderação) aprovadas.

---

## 2) Definition of Ready (DoR)
- **Ambientes**: `dev`/`stage`/`prod‑shadow` estáveis; *feature flags* (`mbp.auto_resolve`, `mbp.fee.dynamic`, `mbp.moderation.advanced`).  
- **Contratos**: rascunhos A106/A87 criados para novas tabelas; *schema registry* com **semver**.  
- **Acessos**: APM/Logs/Traces/RUM; CI/CD; dashboards base; notebooks de goldens.  
- **Governança**: owners/limiares de `oracle_staleness`, `oracle_divergence`, `fx_benchmark_delta`, `mbp_abuse_anomaly` confirmados.

---

## 3) Escopo S5 (alto nível — sem backlog CSV)
- **Oráculos v1 (Brasil)**  
  - Adaptadores (fontes internas/benchmarks); **quórum 2/3**; **TWAP 5m**; *failover*; *healthcheck*.  
  - Métricas: `staleness_ms`, `diverg_pct`, `quorum_ok`, `failover_time`.  
- **Auto‑Resolução**  
  - Serviço `auto_resolve.eval` disparado por evento; janela de confirmação; *fallback* manual; evidências.  
  - Exposição no painel (estado/regra/fonte).  
- **Fees Dinâmicos**  
  - *Controller* com `α,β,bmin,bmax,cooldown`; guarda anti‑thrash; auditar mudanças.  
  - Exibir fee vigente/histórico no painel.  
- **Simulação/Backtesting**  
  - *Harness* determinístico; cenários (spike, gap, burst); *replay*; relatórios.  
- **Moderação Avançada**  
  - Regras: burst pattern, *wash‑trading* simples, *cooldown*; fluxo de **pause/limit/unpause** + apelação.  
  - Eventos `moderation.applied`, `moderation.reviewed`.
- **Observabilidade**  
  - Spans: `oracle.fetch`, `auto_resolve.eval`, `fee.update`, `sim.run`, `moderation.apply`.  
  - Dashboards dedicados (oráculos/auto‑resolução/fees/moderação).  
- **Dados/CDC & DQ**  
  - Tabelas: `oracle_quotes`, `twap_series`, `fees_config`, `simulation_runs`, `moderation_events`.  
  - **dbt tests** (unique/not null/FKs) e regras (fee bounds; quórum; staleness).  
- **Segurança/Privacidade (A108)**  
  - Logs sem PII; *least‑privilege*; SBOM/SAST/Secrets **sem críticos**.  
- **Documentos**  
  - **ADRs 004–006** (Oráculos, Fees, Moderação); **Measurement Sheet S5**; *Runbooks* (Oráculos/Auto‑Resolução/Fees/Moderação).

**Fora do escopo S5**: abertura externa; modelos/antifraude avançados; integrações on‑chain.

---

## 4) Plano de 10 dias (quem faz o quê)
**D1** — Oráculos: quórum + TWAP; métricas; painel inicial.  
**D2** — Auto‑Resolução: serviço `auto_resolve.eval` + eventos.  
**D3** — Fees: controlador dinâmico (bounds/αβ/cooldown); auditoria de fee.  
**D4** — Simulação: *harness* + cenários; *replay*.  
**D5** — Moderação: regras/fluxos; eventos; UI de pausa/retomada.  
**D6** — Dados/CDC: contratos tabelas novas; **dbt tests**; documentação.  
**D7** — Observabilidade: spans/dashboards/alertas; correlação audit.  
**D8** — Fault‑injection: staleness/divergência/quórum/fee‑thrash/burst.  
**D9** — *Bug‑bash* + **GA‑Ready checklist**; evidências.  
**D10** — Review/Demo; Retro; **Gate GA‑Ready (M3)**.

> **Capacidade**: {PO:0,5 • ST:1,0 • PY:1,0 • DC:0,5 • ML:1,0 • SRE:0,5 • FE:0,5}.  
> **WIP máx**: 2 por trilha (Oráculos/Auto‑Resolução/Fees/Simulação/Moderação/Dados/Obs).

---

## 5) Test Plan & Perf Budget (S5)
**Oráculos**: injetar *staleness* e *divergência*; verificar failover TWAP < 60s; quórum 2/3.  
**Auto‑Resolução**: casos felizes/infelizes; *fallback* manual; **p95 ≤ 2h** e mediana ≤ 60m.  
**Fees**: validar Δfee≤20%/5m; bounds; sem regressão **TTPV p95 ≤ 0,8s**.  
**Simulação**: 3 cenários mínimos (spike/gap/burst) com relatórios; reprodutibilidade.  
**Moderação**: detecção e **MTTD ≤ 5m** / **MTTM ≤ 15m**.  
**Dados/DQ**: dbt tests verdes; *CDC lag p95 ≤ 120s* nas novas tabelas.  
**Governança**: 100% watchers verdes; **Hook ≥98%**; **Audit ≥99%**.

---

## 6) Measurement Sheet — S5
```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
Oracle staleness (ms),APM/Oracles,5m,<=30000,pm.oracle_staleness,twap_failover,PM/BC,orcl.staleness_ms
Oracle divergence (%),Engine/Oracles,5m,<=1.0,pm.oracle_divergence,freeze_oracle,PM/BC,orcl.diverg_pct
Quórum ok (% janelas),Oracles,5m,>=99,pm.oracle_divergence,freeze_oracle,PM/BC,orcl.quorum_ok
Auto‑Resolução p95 (h),Events,24h,<=2,mbp_resolution_sla,freeze,PM/BC,events.auto_resolve_p95
TWAP gap (%),Engine,5m,<=1.0,mbp_price_spike_divergence,freeze,PM/SRE,engine.twap_gap
Δfee/5m (%),Logs,5m,<=20,mbp_fee_change_rate,fee_guard,PM/SRE,logs.fee_delta_5m
Fee bounds (viol.),Logs,5m,==0,mbp_fee_bounds_breach,fee_guard,PM/SRE,logs.fee_bounds_breach
TTPV p95 (ms),APM/Traces,5m,<=800,slo_budget_breach,rollback,SRE,apm.ttp_dec_p95
MTTD abuso (min),Logs,1h,<=5,mbp_abuse_anomaly,alert+moderation,SEC/PM,logs.mttd_abuse
MTTM moderação (min),Logs,1h,<=15,mbp_abuse_anomaly,alert+moderation,SEC/PM,logs.mttm_moderation
CDC lag p95 (s),CDC/APM,5m,<=120,cdc_lag,degrade+rollback,DATA,cdc.lag_p95
Hook Coverage %,CI/Repo,24h,>=98,metrics_decision_hook_gap,open_incident,PLAT,ci.hook_coverage
Audit Coverage %,Logs,24h,>=99,metrics_decision_hook_gap,open_incident,PLAT,logs.audit_coverage
```

> **Notas**: `mbp_fee_change_rate`/`mbp_fee_bounds_breach` são **guards** específicos desta sprint no A110; mantêm ação **fee_guard (freeze/degrade)**.

---

## 7) Hooks A110 — exercícios (validação/fault‑injection)
```yaml
exercises:
  oracle_staleness:
    inject: orcl.delay(staleness_ms=45000, duration='5m')
    expect: action=='switch_to_twap_failover' && failover_time<60s
  oracle_divergence:
    inject: orcl.bias(delta_pct=0.015, window='5m')
    expect: action=='freeze_oracle' && notify.contains('PM/BC')
  quorum_failure:
    inject: orcl.drop_sources(n=2)
    expect: action=='freeze_oracle' && auto_resolve=='halted'
  auto_resolve_sla:
    inject: events.delay('auto_resolve', hours=2.5)
    expect: action=='freeze' && owner=='PM/BC'
  fee_thrash:
    inject: fee.controller(alpha='x2', duration='10m')
    expect: hook=='fee_guard' && action in ['freeze','degrade_route']
  abuse_burst:
    inject: engine.burst_trades(rate='x3', duration='5m')
    expect: action=='alert+moderation' && market.status in ['paused','limited']
```

---

## 8) ORR — **Gate GA‑Ready (M3)** (checklist)
- **Oráculos**: `staleness≤30s` p95; `divergência≤1%` (5m); **quórum 2/3**; **failover<60s**.  
- **Auto‑Resolução**: p95≤2h; mediana≤60m; fallback manual **testado**; trilha/auditoria ok.  
- **Fees**: Δfee≤20% (5m); bounds respeitados; sem regressão TTPV p95≤800ms.  
- **Moderação**: **MTTD≤5m** / **MTTM≤15m**; fluxos de pausa/reabertura operacionais.  
- **Dados/DQ**: tabelas novas **contratadas**; **dbt tests** verdes; **CDC lag p95≤120s**.  
- **Governança**: **Hook≥98%**, **Audit≥99%**, watchers verdes; **P1=0**; **error‑budget burn<1×/4h**.  
- **Change**: **GA Plan (S6)** publicado (start D0, escopo, comunicação, *abort*, scorecards).  
- **Assinaturas**: **PO, ST, PY, DC, ML, SRE, FE, SEC/RSK, PM/BC**.

---

## 9) Riscos & Mitigações (watcher/hook)
1) **Staleness/divergência** → `pm.oracle_staleness`/`pm.oracle_divergence` → **TWAP/freeze**.  
2) **Auto‑resolução lenta** → `mbp_resolution_sla` → **freeze + fallback manual**.  
3) **Fee thrash** → `mbp_fee_change_rate`/`mbp_fee_bounds_breach` → **fee_guard** (freeze/degrade).  
4) **Perf (TTPV)** → `slo_budget_breach` → **rollback/degrade**.  
5) **Abuso** → `mbp_abuse_anomaly` → **alert+moderation**.  
6) **CDC lag / schema drift** → `cdc_lag`/`schema_registry_drift` → **degrade/rollback**/**block_deploy**.  
7) **Privacidade/Segurança** → `dp_budget_breach`/`dep_vuln_open` → **freeze**/**block_release**.

---

## 10) Evidence Pack & Assinaturas
- **Evidências**: dashboards (oráculos/auto‑resolução/fees/moderação), *trace_ids*, relatórios de simulação, logs de auditoria, testes dbt/CDC, resultados de exercícios A110, *commit sha*.  
- **Assinaturas**: PO • ST • PY • DC • ML • SRE • FE • SEC/RSK • PM/BC.

---

## 11) Demo (Review)
- **Roteiro**: simular fonte fora do ar (ver **failover TWAP<60s**) → disparar **auto‑resolução** e checar trilha/regra → variar **volatilidade** e observar **fees** sob *bounds/cooldown* → acionar **moderação** em burst → exibir relatórios de **simulação** e painéis.  
- **AC (Given/When/Then)**:  
  - *Given* janelas de 5m; *When* medir oráculos; *Then* `staleness≤30s`, `diverg≤1%`, `failover<60s`.  
  - *Given* evento verdade; *When* auto‑resolução; *Then* `p95≤2h` e trilha OK.  
  - *Given* variação de vol/depth; *When* atualizar fee; *Then* `Δfee≤20%` e `fee∈[bmin,bmax]`.

---

## 12) Pós‑Review → Prep **S6** (GA interno — 30d verdes)
- Iniciar **GA Plan** (D0 na S6); configurar scorecards; congelar escopo; *on‑call* definido.  
- Checklist **S6**: 30d verdes, *readout*, lições, ajustes finais do catálogo MBP.

---

## 13) Políticas & No‑Go (reafirmação)
- **Sem GA‑Ready** com watcher crítico vermelho; **sem logs com PII**; **waivers** apenas com *timebox* + rollback e aprovação **PO+Eng+Data+SRE**.

---

> **Resultado esperado da S5**: **Gate GA‑Ready (M3) aprovado** com **Oráculos v1 + Auto‑Resolução + Fees Dinâmicos + Simulação/Backtesting + Moderação Avançada** em operação, telemetria e governança **A110** ativas, prontos para iniciar os **30 dias verdes** na **S6**.