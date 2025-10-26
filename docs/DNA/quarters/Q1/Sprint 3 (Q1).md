# Sprint 3 — Especificação FINAL (v1.3)

## MBP (Q1) • "Slice 1 — MVP Interno (Templates, Truth Source, TWAP 5m, Painel, Anti‑abuso)"

Alinhado a: **Q1 Roadmap — MBP GA interno + CE$ Fundações (v1.1 FINAL)**, **S1 v1.1**, **S2 v1.2 (aprovada)**, **Roadmap — Kickoff Intake (CE$) • 2025‑09‑10**.

> **Janela:** 2 semanas
> **Objetivo:** colocar no ar o **MVP interno do MBP** com **templates de mercado**, **resolução regrada (Truth Source)**, **TWAP/benchmarks (5m)**, **painel completo** e **anti‑abuso básico**, atingindo **Gate Release** com watchers verdes, trilha de auditoria e rollback claro.

---

## 0) Delta S2 → S3 (elevações)

* **Resolução regrada:** **Rule Engine** (Truth Source) + **fallback manual** auditado.
* **TWAP/Benchmarks (5m):** cálculo on‑line 1/5/15m; **divergência ≤ 1,0%**; *alert* e **freeze** com critérios formais.
* **Templates de Mercado:** catálogo versionado + validações + criador por template (atrás de flag).
* **Painel completo:** preço, prob, TWAP, profundidade, ordens, eventos, trilha de auditoria.
* **Anti‑abuso básico:** rate‑limit, burst‑detector, **risk‑caps** opcionais; pausa/limitação.
* **Observabilidade:** spans/eventos (`rule.eval`, `twap.compute`, `abuse.detect`) **correlacionados com audit**.
* **Dados/CDC:** contratos + **dbt tests** (`mbp_markets`, `mbp_quotes`, `mbp_resolutions`, `mbp_abuse_events`).
* **Segurança/Privacidade (A108):** logs sem PII; *least‑privilege*; auditoria de regra.
* **Runbooks:** Resolução Regrada, TWAP Divergência, Abuso/Moderação.

---

## 1) Sprint Goal & Definition of Awesome (DoA)

**Sprint Goal:** colocar o **MVP interno** em *prod* com **Gate Release** aprovado.

**Definition of Awesome (S3):**

* **Mercados ativos:** 5–10 internos.
* **Liquidez:** `depth@2% ≥ 500`.
* **Resolução:** `≤ 24h` em 100% dos casos S3.
* **Preço:** `TWAP divergence ≤ 1,0%` (janela 5m).
* **Perf:** `TTPV p95 ≤ 0,8s`; `INP p75 ≤ 200ms`; `invariant=0`.
* **Confiabilidade:** `P1=0`; `error‑budget burn < 1×/4h` (janela Release).
* **Governança:** audit trail ≥ 99% das ações; watchers must‑have verdes.

---

## 2) Definition of Ready (DoR)

* **ADRs** aprovados: Resolução Regrada (Truth Source), TWAP/Benchmarks, Anti‑Abuso.
* **Templates** definidos (tipos, constraints, validações); feature flag `mbp.create.by_template`.
* **Contratos de dados** registrados (A106/A87) + *dbt tests* esqueleto.
* **Ambientes & acessos**: APM/Logs/Traces/RUM; schema registry; CI/CD; prod‑shadow.
* **Watchers/Hooks:** owners confirmados e limiares revisados (A110).

---

## 3) Escopo S3 (alto nível — verb‑driven)

### 3.1 **Modelar Templates de Mercado**

* Catálogo versionado (`id`, `category`, `truth_source`, parâmetros).
* Validações: `name`, `resolution_window`, `min_liquidity`, `truth_source`.
* Criador por template (atrás de flag) + pré‑visualização.

### 3.2 **Avaliar Regras (Truth Source)**

* **Rule Engine** com fontes: tabela interna / manual / endpoint interno.
* Workflow: `resolution_started` → `rule.eval` → `resolution_finished`.
* Fallback: manual com evidência + aprovação + audit.
* **Evolução — policy‑as‑data:** regras YAML/JSON versionadas + hash de política.

  * **Rollout como *data migrations***: `ruleset vMAJOR.MINOR.PATCH` → PR com *schema check* + *golden tests* → pre‑prod dry‑run → checksum assinado → flag por mercado → rollback para versão anterior.

### 3.3 **Computar TWAP (5m) e Benchmarks**

* TWAP 5m (janelas 1/5/15m); benchmarks opcionais.
* **Freeze:** acionar se `|price−twap|/twap > 1,0%` em **2 janelas consecutivas** **ou** se **IC‑99%** for excedido por **3 amostras** na janela.
* Evento `twap_recomputed` emitido a cada recálculo (telemetria detalhada centralizada em 3.6).

### 3.4 **Orquestrar Painel (internal)**

* Preço, probabilidade, TWAP, profundidade, ordens recentes, eventos e trilha.
* Filtros por mercado/template; *drill‑down* para resoluções.

### 3.5 **Orquestrar Anti‑Abuso**

* Rate limit por usuário/mercado; *cooldown* pós‑spike; detecção de burst trades.
* **Risk‑caps por mercado (opcional):** `max_exposure_per_user`, `max_open_interest`, `max_trade_rate` (por janela).
* **Defaults sugeridos por template** (ajustáveis em `configs/policies/mbp_s3.yml`):

  * *Yes/No binário*: `max_exposure_per_user=1000`, `max_trade_rate=30/min`, `max_open_interest=10000`.
  * *Escala contínua*: `max_exposure_per_user=5000`, `max_trade_rate=60/min`, `max_open_interest=50000`.
* Fluxo de **pause/limit** de mercado + moderação (evidências, undo/redo).

### 3.6 **Instrumentar Observabilidade (A71–A72)**

* Spans: `rule.eval`, `twap.compute`, `abuse.detect` **correlacionados com audit** (`trace_id`).
* Eventos: `market_created_template`, `twap_recomputed`, `abuse_flagged`.

### 3.7 **Modelar Dados & CDC**

* Tabelas: `mbp_markets`, `mbp_quotes`, `mbp_resolutions`, `mbp_abuse_events`.
* **dbt tests** (unique/not null/FKs) + expectativas; `CDC lag p95 ≤ 120s`.

### 3.8 **Proteger Segurança/Privacidade (A108)**

* Logs sem PII; guarda de decisões/regras; redaction; *least‑privilege*.

### 3.9 **Documentar & Operar (Runbooks)**

* ADRs 002–004; Runbooks: Resolução, TWAP, Anti‑Abuso; Measurement Sheet S3.

**Fora do escopo S3:** oráculos externos/auto‑resolução (→ S5); fees dinâmicos; moderação avançada; simulações profundas.

---

## 4) Plano de 10 dias (quem faz o quê)

* **D1 — Templates:** schema/validações; flag on em *stage*; painel: TWAP/depth placeholders reais.
* **D2 — Rule Engine (Truth Source):** contrato; eventos `rule.eval`.
* **D3 — TWAP compute (1/5/15m):** cálculo e eventos `twap_recomputed`.
* **D4 — Anti‑abuso:** rate limits + burst detector; eventos `abuse_flagged`.
* **D5 — Dados/CDC:** modelos `mbp_*`; *dbt tests*; dashboards.
* **D6 — Observabilidade:** spans `rule.eval|twap.compute|abuse.detect`; correlação audit.
* **D7 — Perf:** *load* com 5–10 mercados; `p95≤0,8s`; `invariant=0`; `depth@2%≥500`.
* **D8 — Drills:** Resolução, TWAP, Abuso (simulados) + evidências.
* **D9 — Bug‑bash & Dry‑run Release:** checklist, owners, aborts.
* **D10 — Review/Demo; Retro; Gate Release**.

**Capacidade:** { PO: 0,5 • ST: 1,0 • PY: 1,0 • DC: 0,5 • ML: 1,0 • SRE: 0,5 • FE: 0,5 }
**WIP máx:** 2 por trilha (Templates/Resolução/TWAP/Obs/FE/Dados).

---

## 5) Test Plan & Perf Budget (S3)

* **Funcional:** criação por template → negociação → resolução via regra; fallback manual com evidência.
* **Perf:** 5–10 mercados; `N rps` (ORR); `p95 ≤ 0,8s`; `invariant=0`.
* **Preço:** `TWAP divergence ≤ 1,0%` com *spike tests*; bandas de tolerância.
* **Liquidez:** `depth@2% ≥ 500` com ordens programáticas.
* **Abuso:** bursts e rate‑limit; pausa/retoma.
* **Dados:** *dbt tests* e `CDC lag p95 ≤ 120s`.
* **UX:** `INP p75 ≤ 200ms`; RUM ativo; regressão CWV bloqueia deploy.
* **Aprovação:** watchers verdes; `P1=0`; *evidence pack* completo.

---

## 6) Measurement Sheet — S3

```csv
KPI,Fonte,Janela,SLO/Meta,Watcher,Hook,Owner,Query/Id
Mercados ativos (#),Engine,24h,>=5 e <=10,metrics_decision_hook_gap,open_incident,PM,engine.markets_active
Depth@2% (unid),Engine,15m,>=500,mbp_liquidity_depth,degrade,PM,engine.depth_2pct
TWAP divergence %,Engine,5m,<=1.0 (2 janelas) ou conf99 excedida×3,mbp_price_spike_divergence,freeze,PM/SRE,engine.twap_gap
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

## 7) Hooks A110 — exercícios (S3)

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

## 8) ORR — Gate Release (S3) (checklist)

* **Mercados ativos 5–10**; `depth@2% ≥ 500`; `TWAP divergence ≤ 1,0%`.
* **Perf:** `TTPV p95 ≤ 0,8s`; `invariant=0`; `P1=0`.
* **Watchers:** 100% must‑have verdes; exercícios de hooks **pass**.
* **Dados/CDC:** dbt ok; `CDC lag p95 ≤ 120s`.
* **Segurança/Privacidade:** logs sem PII; dep/SAST/SBOM sem críticos.
* **Change:** Release Plan publicado (escopo, rollback, comunicação).
* **Assinaturas:** **PO, Eng (ST), Data (DC), SRE, FE, SEC/RSK**.

---

## 9) Riscos & Mitigações (watcher/hook)

1. **Liquidez insuficiente** → `mbp_liquidity_depth` → degrade para programa/roteamento.
2. **TWAP > 1%** → `mbp_price_spike_divergence` → freeze + investigação; ajuste de janelas.
3. **Resolução atrasada** → `mbp_resolution_sla` → freeze + fallback manual.
4. **Abuso/manipulação** → `mbp_abuse_anomaly` → pause/limit; moderação.
5. **CDC lag** → `cdc_lag` → degrade/rollback; priorizar ingest.

---

## 10) Evidence Pack & Assinaturas

* **Evidências:** dashboards (depth/TWAP/p95), trace_ids, relatórios dbt/CDC, prints do painel e rule eval, resultados de exercícios A110, commit sha.
* **Assinaturas:** PO • ST • PY • DC • ML • SRE • FE • SEC/RSK.

---

## 11) Demo (Review)

* **Roteiro:** criar por template → prover liquidez programática → negociar → observar painel (TWAP/profundidade) → acionar resolução regrada (rule eval + audit) → simular spike para congelamento → reabrir após normalização.
* **AC (Given/When/Then):**

  * *Given* janela 5m; *When* computar TWAP; *Then* `|price−twap|/twap ≤ 1,0%` (ou freeze automático por 2 janelas).
  * *Given* mercado resolvido; *When* aplicar regra; *Then* `resolution_hours ≤ 24` + trilha OK.
  * *Given* trades programáticos; *When* medir profundidade; *Then* `depth@2% ≥ 500`.

### 11.0 Snippet de consulta (TWAP/divergência no painel)

> Exemplo simples (SQL) para abastecer o gráfico do painel

```sql
-- preço médio ponderado no tempo (5m) e divergência
WITH w AS (
  SELECT
    market_id,
    ts,
    price,
    AVG(price) OVER (
      PARTITION BY market_id
      ORDER BY ts
      RANGE BETWEEN INTERVAL '5 MINUTES' PRECEDING AND CURRENT ROW
    ) AS twap_5m
  FROM mbp_quotes
)
SELECT
  market_id,
  ts,
  price,
  twap_5m,
  ABS(price - twap_5m) / NULLIF(twap_5m,0) AS divergence
FROM w
WHERE ts >= NOW() - INTERVAL '1 DAY'
ORDER BY market_id, ts;
```

## 11.1 Exemplo numérico TWAP (5m) — validação rápida

> Cenário: preços minuto‑a‑minuto em 5 minutos: **[100, 101, 100, 99, 100]**; preço corrente = **101**.

1. **TWAP(5m)** = (100+101+100+99+100) / 5 = **100,0**.
2. **Divergência** = `|101 − 100| / 100 = 0,01` ⇒ **1,0%**.
3. **Critério:** se na próxima janela (mais 5m) a divergência **> 1,0%** **de novo**, **freeze**. Se o **IC‑99%** do TWAP for excedido por **3 amostras** na janela, **freeze** imediato.

---

## 12) Pós‑Review → Prep S4

* Mapear gaps/waivers (A106) com dono + timebox.
* Planejar **S4**: hardening MVP + CE$ Fundações (DEC p95≤0,8s; contratos/dbt; schema registry; ADRs 001–003 aprovados).
* Pré‑work: ajustar limiares TWAP, parametrizar templates; reforçar dbt tests.

---

## 13) Políticas & No‑Go (reafirmação)

* **Sem Release** com watchers críticos vermelhos; **sem logs com PII**; **waivers** só com timebox + rollback e aprovação **PO+Eng+Data+SRE**.

---

## 14) Resultado esperado da S3

**Gate Release aprovado** com **MVP interno** no ar: templates, resolução regrada, TWAP/benchmarks (5m), painel completo, anti‑abuso básico (com *risk‑caps* opcionais), telemetria 360°, dados/CDC e governança A110 ativas.

---

## Apêndice A — Modelagem de Dados (S3)

**Tabelas principais (DDL lógico):**

```sql
-- mercados
CREATE TABLE mbp_markets (
  market_id       STRING PRIMARY KEY,
  template_id     STRING NOT NULL,
  name            STRING NOT NULL,
  category        STRING NOT NULL,
  truth_source    STRING NOT NULL, -- enum('table','manual','endpoint')
  resolution_deadline TIMESTAMP NOT NULL,
  status          STRING NOT NULL, -- enum('open','paused','resolved','canceled')
  created_at      TIMESTAMP NOT NULL,
  updated_at      TIMESTAMP NOT NULL
);

-- cotações / trades agregados
CREATE TABLE mbp_quotes (
  market_id       STRING NOT NULL,
  ts              TIMESTAMP NOT NULL,
  price           DECIMAL(18,8) NOT NULL,
  volume          DECIMAL(18,8) NOT NULL,
  depth_2pct      DECIMAL(18,8) NOT NULL,
  twap_5m         DECIMAL(18,8),
  PRIMARY KEY (market_id, ts)
);

-- resoluções
CREATE TABLE mbp_resolutions (
  market_id       STRING PRIMARY KEY,
  started_at      TIMESTAMP NOT NULL,
  rule_version    STRING NOT NULL,
  source_kind     STRING NOT NULL, -- 'table'|'manual'|'endpoint'
  source_ref      STRING,
  decided_value   STRING,
  decided_at      TIMESTAMP,
  decided_by      STRING, -- user/email se manual
  evidence_uri    STRING,
  audit_trace_id  STRING
);

-- abuso / anomalias
CREATE TABLE mbp_abuse_events (
  id              STRING PRIMARY KEY,
  market_id       STRING NOT NULL,
  ts              TIMESTAMP NOT NULL,
  kind            STRING NOT NULL, -- 'burst'|'rate_limit'|'manipulation'
  severity        STRING NOT NULL, -- 'low'|'med'|'high'
  details         STRING,
  action_taken    STRING -- 'paused'|'limited'|'alert_only'
);
```

**dbt tests (exemplos):**

* `mbp_markets`: `unique(market_id)`, `not_null(name, category, truth_source)`.
* `mbp_quotes`: `unique(market_id, ts)`, FK `market_id → mbp_markets`.
* `mbp_resolutions`: `unique(market_id)`, `not_null(started_at, rule_version, source_kind)`.
* `mbp_abuse_events`: `unique(id)`, FK `market_id → mbp_markets`.

---

## Apêndice B — SPEC (Lamport‑Style)

**Variáveis**
`State ∈ { PLAN_OK, MVP_READY, RELEASE_READY, RELEASED }`
`Metrics = { ttpv_p95_ms, inp_p75_ms, invariant, depth_2pct, twap_divergence_pct, burn4h, p1 }`
`Policy = { thresholds, abort_rules, hash }`
`Evidence = { bundle_sha256, merkle_root, tx_hash_or_worm, signatures_2ofN }`

**Init**
`State = PLAN_OK ∧ ReadinessOk ∧ MetricsPresent ∧ Policy.hash = policy_hash.txt`

**Ações**

* **Collect:** atualiza `Metrics` com janelas consistentes; `cdc_lag_p95 ≤ 120s`.
* **EvaluateRules:** aplica Truth Source → `resolution_finished` ou fallback manual.
* **ComputeTWAP:** recalcula TWAP e divergência (1/5/15m) + bandas/IC.
* **AntiAbuse:** aplica rate‑limit/burst e *risk‑caps*; `pause|limit` mercado.
* **EvaluatePolicy:** se `Abort` ⇒ rollback/freeze e `State` inalterado; se `PromoteOk` ⇒ `State := Next(State)`.

**Invariantes (Safety)**

* **INV1 ResolutionAudit:** toda resolução tem fonte, evidência e audit_trace.
* **INV2 PriceBound:** `twap_divergence_pct ≤ 1,0%` (2 janelas) **ou** IC‑99 não excedido; violação ⇒ `freeze`.
* **INV3 LiquidityFloor:** `depth_2pct ≥ 500` para mercados ativos.
* **INV4 NoPII:** logs e eventos sem PII; redaction aplicada.
* **INV5 Determinism:** mesma `Policy.hash` + mesmas métricas ⇒ decisão idêntica.

**Progresso (Liveness)**

* **LF1 MVP:** `ReadinessOk` ∧ `Templates+TWAP+RuleEngine` completos ~> `MVP_READY`.
* **LF2 Release:** `MVP_READY` ∧ watchers verdes ~> `RELEASE_READY` ~> `RELEASED`.
---
## Anexo técnico — Quickstart S3 (gerado pelo prompt Codex)
- Rodar local: `python3 scripts/s3/twap_compute.py data/cdc/seeds/s3/price_stream_sample.csv out/s3_gatecheck/twap.csv`
- Checar freeze: `bash scripts/s3/twap_freeze_check.sh out/s3_gatecheck/twap.csv`
- Simular abuso: `python3 scripts/s3/anti_abuse.py data/cdc/seeds/s3/orders_sample.json && cat out/s3_gatecheck/abuse_flags.json`
- Criar mercado por template: `python3 scripts/s3/create_market_from_template.py TPL-YESNO-01 "Pergunta Interna 001"`
- CI/ORR: abra PR e verifique **MBP S3 ORR** verde.
