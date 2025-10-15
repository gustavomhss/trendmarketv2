---
file: 05-Observabilidade-Testes-e-Evidencias.md
version: v1.2 (A1 KB — Deepdive Supremo)
date: 2025-09-09
author: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: observability-canonical
---

# 05) Observabilidade, Testes & Evidências — A1 (v1.2)
> **Propósito:** tornar **medível, verificável e promovível** tudo que o A1 entrega (PM, Oráculos, FX), com **SLIs/SLOs formais**, **dashboards/alertas machine‑readable**, **estratégia de testes por camadas**, **sintéticos**, **evidence** e **gates**. *Sem dados ⇒ sem release.*

---

## 0) Readiness & Handshake (execução)
- Carregar `brief_context.yaml` (Arq. 01) — NSM alvo **p75≤500ms / p95≤800ms**; staleness p95<30s; FX route p95≤1500ms; CDC p95≤120s.  
- Verificar **collectors ON**: métricas, traces, logs e **sintéticos**.  
- Confirmar **watchers must‑have** (Arq. 01 §6) e **hooks** (Arq. 04 §3) **ativos**.  
- **No‑data ⇒ No‑release**: SLI sem coleta **bloqueia** promoção.

**Self‑check (machine‑readable)**
```yaml
obs_readiness:
  collectors: [metrics, traces, logs, synthetics]
  watchers_online: true
  dashboards_published: [Reliability, Oracles_FX, PM_Core, FX_Routing, CDC_Health, Web_API]
  alert_windows_muted: none
  tz: America/Bahia
```

---

## 1) **KPI Tree** — do NSM às entradas (com fórmulas)
```text
NSM: Time-to-Preço-Válido (p75/p95)
 ├─ Latência PM (p95) = p95(api_gw→pm_svc→decision)
 ├─ Oracles Staleness (p95) = p95(ts_ingest - ts_event)
 ├─ FX Route Latency (p95) = p95(t_fetch_quote)
 ├─ CDC Lag (p95) = p95(ts_consumer - ts_producer)
 └─ Web INP (p75)
```
**Regra:** toda entrega declara **qual folha** vai mover e **Δ** esperado. Evidence deve mostrar o **antes/depois**.

---

## 2) SLIs / SLOs / Orçamento de Erros
| Domínio | SLI | SLO (prod) | Burn‑policy |
|---|---|---:|---|
| **NSM** | `nsm.p75_ms / p95_ms` | ≤500 / ≤800 | 4h budget diário |
| **PM** | `pm.clearing_latency_ms.p95` | ≤150 | alert p95>150 por 10m |
| **Oráculos** | `oracle.staleness_ms.p95` | <30000 | alert por 5m |
| **Oráculos** | `oracle.divergence_eps` | ≤ ε (ativo/região) | alert por 10m |
| **FX** | `fx.route_latency.p95` | ≤1500 | ladder L1→L4 |
| **FX** | `fx.cip_delta_eps` | ≤ ε (par/tenor) | 10m |
| **CDC** | `cdc.lag_p95_s` | ≤120 | 15m |
| **Web** | `web.inp_p75_ms` | ≤200 | 30m |
| **APIs** | `api.breaking_change` | ==0 | imediata |

**Ambientes:** *stage* usa metas 10–20% **mais frouxas** (para testes de carga/chaos) e **shadow** habilitado.

---

## 3) Telemetria — Métricas, Traces, Logs & Sintéticos
### 3.1 Métricas (Prometheus‑like)
- **RED por serviço**: `requests_total`, `request_duration_ms_{p50,p90,p95,p99}`, `errors_total`, `inflight`.
- **Domínio**: `pm.clearing_latency_ms`, `oracle.staleness_ms`, `oracle.divergence_eps`, `fx.route_latency_ms`, `fx.cip_delta_eps`, `cdc.lag_s`.
- **Unidades/labels**: `*_ms` (milissegundos), `*_s` (segundos). Labels **permitidos**: `market_id`, `region`, `pair`, `tenor`, `route_id`. **Proibido**: `participant_id` (alta cardinalidade).
- **Orçamentos**: `series_cardinality<=100k`, scrape `15s`, retenção `90d` (prod), `14d` (stage).

### 3.2 Traces (OpenTelemetry)
- **Spans**: `api_gw → pm_svc → decision → fx_router → venue`.  
- **Resource attrs**: `service.name`, `service.version`, `deployment.environment`.  
- **Baggage**: `market_id`, `region`, `seed_id`, `pair`, `tenor`, `route_id`.  
- **Sampling**: head‑based 10% (prod), 30% (stage); **tail‑sampling** 100% para erros/P1.

### 3.3 Logs (JSON‑lines)
Esquema mínimo: `ts, level, svc, event, trace_id, actor?, market_id?, pair?, details{}` — sem PII. **Redação ON**.

### 3.4 Sintéticos (ativos)
- **PM Quote Path**: `POST /bids` (idempotente, payload mínimo válido) → esperar `pm_clearing_result` em sandbox.  
- **FX Quote Path**: `GET /quotes/fx?pair=USD/BRL&tenor=SPOT` → validar `expires_at>now` e `|F_mkt−F_model|<=ε`.
- **Oracles Freshness**: publicar *dummy* em `ingest-sandbox`, medir `staleness` end‑to‑end.

### 3.5 Data‑quality Monitors
`missing_rate`, `null_rate`, `parse_error_rate`, `ts_monotonicity_breaks` por feed/venue/rota (expostos como métricas).

---

## 4) Dashboards — Layout (YAML machine‑readable)
```yaml
dashboards:
  - id: Reliability
    panels:
      - { metric: nsm.p95_ms, target: 800, type: timeseries }
      - { metric: slo.error_budget.burn, target: 1.0, type: gauge }
  - id: Oracles_FX
    panels:
      - { metric: oracle.staleness_ms.p95, target: 30000 }
      - { metric: oracle.divergence_eps, target: eps_table[asset,region] }
      - { metric: fx.route_latency_ms.p95, target: 1500 }
      - { metric: fx.cip_delta_eps, target: eps_cip_table[pair,tenor] }
  - id: PM_Core
    panels:
      - { metric: pm.clearing_latency_ms.p95, target: 150 }
      - { metric: pm.auction_invariant_breach, target: 0 }
  - id: CDC_Health
    panels:
      - { metric: cdc.lag_p95_s, target: 120 }
      - { metric: schema_registry.drift, target: COMPATIBLE }
  - id: Web_API
    panels:
      - { metric: web.inp_p75_ms, target: 200 }
      - { metric: api.breaking_change, target: 0 }
```

---

## 5) Alertas / Watchers — Noise‑budget & Histerese
**Princípios**: (i) agregações temporais (`•`) e janelas **clear_when**; (ii) **≤2 alertas/h** por domínio; (iii) janelas de manutenção automáticas em deploy; (iv) **dedup key**.

**Alertas (PromQL em pseudo)**
```yaml
alerts:
  - id: oracle_staleness_p95
    expr: p95(oracle_staleness_ms[5m]) > 30000
    severity: P1
    dedup: A1/oracles/staleness
  - id: fx_route_latency
    expr: p95(fx_route_latency_ms[5m]) > 1500
    severity: P2
  - id: cip_delta_eps
    expr: fx_cip_delta_eps[10m] > eps(pair,tenor)
    severity: P2
  - id: cdc_lag
    expr: p95(cdc_lag_s[15m]) > 120
    severity: P1
  - id: slo_burn
    expr: slo_error_budget_burn[30m] > 1.0
    severity: P1
```
**Manutenções:** `mute_window` em `deploy_in_progress==true` (label de release do Arq. 07).  
**Auto‑remediação:** hooks do Arq. 04 são chamados via ChatOps/Runbooks.

---

## 6) Tabelas: **ε (CIP)** e **K/TAU (Oráculos)**
### 6.1 ε (CIP) por Par/Tenor — amostra inicial
| Pair | Tenor | ε |
|---|---|---:|
| USD/BRL | SPOT | 0.0010 |
| USD/BRL | 1W | 0.0012 |
| USD/BRL | 1M | 0.0015 |
| EUR/BRL | SPOT | 0.0012 |
| EUR/BRL | 1M | 0.0018 |

### 6.2 K (TWAP) & TAU (MAD) por Ativo/Região — amostra
| Ativo | Região | K (s) | TAU |
|---|---|---:|---:|
| PM:ELEICAO2026 | BR | 120 | 4.5 |
| PM:COPA2030 | BR | 90 | 4.0 |
| PM:ELEICAO2026 | LATAM | 150 | 5.0 |

**Recalibração semanal (pseudo):**
```python
def recalibrate(window):
  K = argmin_over_grid(p95_staleness_vs_volatility)
  TAU = pct(window, 75) / MAD(window)
  return K, clamp(TAU, 3.0, 6.0)
```

---

## 7) Estratégia de Testes (padrão ouro)
### 7.1 Unit
- **Clearing**: monotonicidade, budget‑balance, determinismo.  
- **Filtros robustos**: MAD/Quantis/Hampel — preservam mediana sob outliers.  
- **CIP**: `|F_mkt−F_model| ≤ ε` (mock markets).

### 7.2 Property‑based & Metamórficos
- **PM**: duplicar lances escala volume sem quebrar invariantes.  
- **Oráculos**: *jitter* temporal/outliers não deslocam mediana além de δ.  
- **FX**: rota ótima sob α/β/γ (políticas por par/tenor).

### 7.3 Integração
- Conectores **N≥3**; banimento temporário; idempotência `Idempotency-Key`.

### 7.4 E2E
- `bid → clearing → pm_clearing_result → DEC` e `oracle → TWAP → quote`.

### 7.5 Carga & Resiliência
- Alvos: PM p95 ≤800ms; FX p95 ≤1500ms.  
- **Chaos‑lite**: atraso artificial em 1 feed/venue; hooks devem disparar e recuperar.

### 7.6 SRM / A‑B (se houver modelo)
- **SRM**: `ab.srm==OK`; **Drift**: `psi≤0.2`, `ks≤0.1`.  
- *Hooks*: `a4_ab_srm_guard`, `a4_model_drift_guard`.

### 7.7 CDC / Contratos
- **Contract Tests** (Arq. 03): `schema_breaking==0`; exemplos válidos/ inválidos; registry A2.

---

## 8) **Evidence JSON** — Esquema v1.1 (retro‑compatível)
> Mantém os campos **obrigatórios** do v1 e adiciona **opcionais**. Consumidores v1 continuam válidos.
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "a1_evidence",
  "type": "object",
  "additionalProperties": false,
  "required": ["release_id","timestamp","nsm","oracles","fx","tests","hooks_fired","statusboards"],
  "properties": {
    "release_id": {"type":"string"},
    "timestamp": {"type":"string","format":"date-time"},
    "nsm": {"type":"object","required":["p75_ms","p95_ms"],"properties":{"p75_ms":{"type":"number"},"p95_ms":{"type":"number"}}},
    "oracles": {"type":"object","required":["staleness_p95_ms","divergence_eps"],"properties":{"staleness_p95_ms":{"type":"number"},"divergence_eps":{"type":"number"}}},
    "fx": {"type":"object","required":["route_latency_p95_ms","cip_delta_eps"],"properties":{"route_latency_p95_ms":{"type":"number"},"cip_delta_eps":{"type":"number"}}},
    "tests": {"type":"object","required":["unit","property","e2e","load"],"properties":{"unit":{"type":"integer"},"property":{"type":"integer"},"e2e":{"type":"integer"},"load":{"type":"string"}}},
    "hooks_fired": {"type":"array","items":{"type":"string"}},
    "statusboards": {"type":"array","items":{"type":"string"}},
    "artifacts": {"type":"array","items":{"type":"string"}},
    "web": {"type":"object","required":["inp_p75_ms"],"properties":{"inp_p75_ms":{"type":"number"}}},
    "cdc": {"type":"object","required":["lag_p95_s"],"properties":{"lag_p95_s":{"type":"number"}}}
  }
}
```
**Exemplo (pré‑promoção)**
```json
{
  "release_id": "a1-2025-09-09-rc1",
  "timestamp": "2025-09-09T15:05:00Z",
  "nsm": { "p75_ms": 480, "p95_ms": 770 },
  "oracles": { "staleness_p95_ms": 24000, "divergence_eps": 0.9 },
  "fx": { "route_latency_p95_ms": 1380, "cip_delta_eps": 0.0008 },
  "tests": { "unit": 210, "property": 60, "e2e": 24, "load": "pass" },
  "hooks_fired": ["a1_oracle_staleness_guard","a1_fx_router_latency_guard"],
  "statusboards": ["Reliability","Oracles_FX"],
  "artifacts": ["contracts/*.json","openapi/a1.yaml","hooks/a1.yaml"],
  "web": { "inp_p75_ms": 180 },
  "cdc": { "lag_p95_s": 95 }
}
```

---

## 9) Statusboards & Relatórios
- **Statusboards**: `Reliability`, `Oracles_FX`, `CDC_Health`, `FX_Routing`, `PM_Core`, `Web_API`.  
- **Ritual**: *stand‑up* semanal com última **Evidence** e diffs; *postmortem* linka spans/logs/PRs.

**Snapshot (YAML)**
```yaml
statusboards:
  Reliability: { nsm_p95_ms: 770, burn: 0.4 }
  Oracles_FX:  { staleness_p95_ms: 24000, cip_delta_eps: 0.0008 }
```

---

## 10) Ferramental & Pipelines
**Make targets**
```makefile
obs-lint:      node scripts/obs_lint.js dashboards/*.yaml alerts/*.yaml
obs-deploy:    ./scripts/deploy_dashboards.sh dashboards/*.yaml
obs-smoke:     ./scripts/synthetics.sh Oracles_FX FX_Routing PM_Core
obs-evidence:  node scripts/collect_evidence.js > evidence.json
```
**Estrutura**
```text
observability/
  dashboards/
    reliability.yaml
    oracles_fx.yaml
    fx_routing.yaml
    cdc_health.yaml
    web_api.yaml
    pm_core.yaml
  alerts/
    a1_alerts.yaml
  scripts/
    obs_lint.js
    deploy_dashboards.sh
    synthetics.sh
    collect_evidence.js
```

---

## 11) Go/No‑Go — **Gates Objetivos** (agregados 01–06)
- **Go**: `evidence.json` anexo (v1 ou v1.1); NSM p95≤800ms; staleness p95<30s; FX p95≤1500ms; CDC p95≤120s; `breaking==0`; hooks testados; dashboards publicados.  
- **No‑Go**: watcher crítico sem owner; SLI sem coleta; falha em **contract tests**; violação de privacidade.

---

## 12) Apêndices — Configs de referência
### 12.1 OpenTelemetry Collector (excerto)
```yaml
receivers:
  otlp:
    protocols: { http: {}, grpc: {} }
exporters:
  otlphttp: { endpoint: http://tempo.local:4318 }
  prometheusremotewrite: { endpoint: http://mimir.local/api/v1/push }
processors:
  batch: {}
  tail_sampling:
    decision_wait: 5s
    policies:
      - status_code: { status_codes: [ERROR] }
      - latency: { threshold_ms: 800 }
service:
  pipelines:
    traces: { receivers: [otlp], processors: [tail_sampling, batch], exporters: [otlphttp] }
    metrics:{ receivers: [otlp], processors: [batch], exporters: [prometheusremotewrite] }
```

### 12.2 Prometheus Alertmanager (rótulos chave)
```yaml
route:
  group_by: [service, domain]
  group_wait: 30s
  group_interval: 2m
  repeat_interval: 2h
inhibit_rules:
  - source_match: { severity: P1 }
    target_match: { severity: P2 }
    equal: [service]
```

### 12.3 Script k6 (FX quote)
```js
import http from 'k6/http';
import { check, sleep } from 'k6';
export const options = { vus: 50, duration: '3m' };
export default function() {
  const res = http.get('https://api.creditengine.local/a1/quotes/fx?pair=USD/BRL&tenor=SPOT');
  check(res, { '200': r => r.status === 200, 'p95<1500ms': r => r.timings.duration < 1500 });
  sleep(1);
}
```

---

## 13) Artefatos & Cross‑links
- **Arq. 01**: contexto/targets.  
- **Arq. 02**: domínios e invariantes.  
- **Arq. 03**: contratos/APIs + CDC.  
- **Arq. 04**: hooks/policies/runbooks.  
- **Arq. 06**: segurança/privacidade/on‑chain.

---
**Conclusão:** v1.2 entrega **padrão ouro 200%**: KPIs formais, coletores/limiares claros, **sintéticos ativos**, **testes por camadas**, **Evidence v1.1 retro‑compatível**, e *gates* prontos para o **Go/No‑Go**. Tudo no timezone **America/Bahia** e pronto para produção. 

