# Especificação Profissional — Sprint 5 (Q1)
**Projeto:** CE • **Trilha:** MBP Slice 2 (Escala) • **Versão:** v2.0 PRO  
**Liderança:** Steve Jobs (visión & foco) • Co‑autores: Leslie Lamport, Donald Knuth, Alan Kay, Fernando Pérez, Vitalik Buterin  
**Marcador:** #201293 • **Janela:** Q1 · Sprint 5  

---

## 0) Sumário executivo (one‑pager)
**Meta:** elevar o MBP a **GA‑Ready (M3)** em escala, com oráculos v1 (BR), auto‑resolução, fees dinâmicos, moderação avançada, simulação/backtesting e observabilidade completa.  
**Resultados verificáveis até D10:**
- **Oráculos v1 (BR)**: `staleness ≤ 30s` p95, `divergência ≤ 1.0%` (janela 5m), **quórum ≥ 2/3**, **failover TWAP < 60s**.  
- **Auto‑resolução**: mediana ≤ 60m / p95 ≤ 2h para incidentes do tipo X/Y, trilha de auditoria 100%.  
- **Fees dinâmicos**: `Δfee ≤ 20%/5m`, dentro de `[bmin, bmax]`, *cooldown* e **anti‑thrash** ativos.  
- **Simulação/backtesting (harness)**: 3 cenários (spike/gap/burst), reprodutível, relatórios comparáveis.  
- **Moderação**: **MTTD ≤ 5m / MTTM ≤ 15m**, pause/retomar com evidência.  
- **Dados/CDC**: tabelas novas contratadas + **dbt tests** verdes; **CDC lag p95 ≤ 120s**.  
- **Observabilidade A71–A72**: spans e painéis para `oracle.fetch`, `auto_resolve.eval`, `fee.update`, `sim.run`, `moderation.apply`.  

---

## 1) Escopo (in/out)
**IN**
1. Adapters de **Oráculos v1 (BR)** com agregação por **quórum (≥2/3)** e **TWAP** com failover < 60s.
2. **Auto‑resolução** governada por *Truth Source* + quórum; fallback manual com evidência.
3. **Fees dinâmicos**: \( fee(t) = base + α·vol(t) + β·(1/depth(t)) \), com bounds `[bmin,bmax]`, cooldown e anti‑thrash (Δ ≤ 20%/5m).
4. **Simulação & Backtesting**: harness determinístico; replay de eventos; relatórios comparáveis.
5. **Moderação avançada**: heurísticas de pause/limit; fluxo de apelação; evidência padronizada.
6. **Observabilidade** (A71–A72): métricas, logs estruturados e tracing; dashboards.
7. **Dados/CDC**: contratos **A106/A87** para `oracle_quotes`, `twap_*`, `simulation_runs`, `moderation_events` + **dbt tests**.
8. **ORR S5**: gates e evidências no artefato canônico `s4-orr-evidence`.

**OUT (não faz parte desta sprint)**
- CRD‑9 (Error Budget & Burn‑Rate) como gate de SLO no CI (entra na Sprint 6).  
- Qualquer dependência em BigQuery produtivo (mantemos DuckDB no CI).  

---

## 2) Requisitos funcionais (RF) e não‑funcionais (RNF)
### RF
RF‑01. Agregar cotações dos oráculos com **quórum ≥ 2/3**; rejeitar outliers pelo desvio permitido.  
RF‑02. Calcular **TWAP** contínuo; acionar **failover < 60s** em fonte primária caída.  
RF‑03. Detectar **staleness** > 30s e **divergência** > 1.0% (janela 5m); sinalizar.  
RF‑04. Executar **auto‑resolução** baseada em regra + quórum; registrar trilha; fallback manual.  
RF‑05. Calcular **fee(t)** com *cooldown* e anti‑thrash; respeitar `[bmin,bmax]`.  
RF‑06. **Simular** 3 cenários (spike/gap/burst) e produzir relatórios comparáveis.  
RF‑07. **Moderar** (pause/limit) com heurísticas; abrir **apelação**; anexar evidência.

### RNF
RNF‑01. **Disponibilidade**: 99.5%/30d dos serviços MBP.  
RNF‑02. **Performance**: **TTPV p95 ≤ 800ms**; pipelines p95 ≤ 10m (sem TLA).  
RNF‑03. **Reprodutibilidade**: harness determinístico; DBT no CI com DuckDB.  
RNF‑04. **Observabilidade**: métricas, logs e tracing com correlação; dashboards prontos.  
RNF‑05. **Segurança/Compliance**: logs de auditoria; RBAC das ações de moderação.

---

## 3) Arquitetura (visão de componentes)
- **Oracle Adapters** → **Quorum Aggregator** → **TWAP Engine** → **Quote Bus**  
- **Auto‑Resolver** (regra Truth Source + quórum) ↔ **Audit Log**  
- **Fee Engine** (base, α·vol, β·depth, bounds, cooldown, anti‑thrash)  
- **Moderation Service** (pause/limit/appeal)  
- **Simulation Harness** (scenarios runner + reports)  
- **Data Layer**: tabelas e **dbt** (DuckDB em CI; destino produtivo fora do escopo)  
- **Observability**: exporters, recording rules, dashboards  
- **ORR**: gates e evidências → `s4-orr-evidence`

---

## 4) Interfaces & contratos (exemplos)
### 4.1 Events (JSON)
`oracle.quote`  
```json
{ "ts": "<iso>", "source": "<id>", "symbol": "BRLUSD", "price": 5.4371, "staleness_ms": 3800 }
```
`fee.update`  
```json
{ "ts": "<iso>", "symbol": "BRLUSD", "fee": 0.0018, "components": {"base":0.001, "alpha_vol":0.0005, "beta_depth":0.0003}, "cooldown": true }
```
`moderation.action`  
```json
{ "ts":"<iso>", "symbol":"BRLUSD", "action":"pause", "reason":"divergence>1%", "evidence":"s3://.../id" }
```

### 4.2 API (REST/GRPC — esqueleto)
- `GET /oracle/quote?symbol=BRLUSD` → `{price, twap_1m, staleness_ms, quorum}`  
- `POST /moderation/pause` → `{id, status}`  
- `POST /resolve/apply` → `{decision_id, outcome}`

---

## 5) Dados & DBT (contratos A106/A87)
Tabelas (colunas principais; dbt tests: *not_null*, *unique*, *accepted_values*, *freshness*):
- `oracle_quotes(symbol, ts, source, price, staleness_ms)`
- `twap_1m/5m(symbol, ts, twap, quorum_ok)`
- `simulation_runs(id, scenario, started_at, finished_at, p95_latency_ms, result_path)`
- `moderation_events(id, ts, symbol, action, reason, evidence_uri, actor)`

**CI**: `dbt-duckdb~=1.8.0`; profile `ce_profile` → `./out/dbt/ce.duckdb`; rodar `deps/debug/run + tests`; evidências no artifact.

---

## 6) Observabilidade (A71–A72)
**Métricas**: `staleness_ms`, `diverg_pct`, `quorum_ok`, `failover_time_s`, `delta_fee_5m`, `ttpv_p95_ms`, `moderation_pauses`, `appeals_open`.  
**Traces**: `oracle.fetch`, `oracle.aggregate`, `auto_resolve.eval`, `fee.update`, `sim.run`, `moderation.apply`.  
**Logs**: JSON com `trace_id`, `span_id`.  
**Dashboards**: Oracles, Auto‑Resolve, Fees, Moderation, Simulation.

---

## 7) Perf budgets & SLOs
- **Oracles**: `staleness ≤ 30s` p95, `divergência ≤ 1.0%`/5m, `failover < 60s`, `quórum ≥ 2/3`.  
- **TTPV**: p95 ≤ 800ms.  
- **CDC lag**: p95 ≤ 120s.  
- **Moderation**: **MTTD ≤ 5m / MTTM ≤ 15m**.

---

## 8) ORR — Gates S5 (evidência obrigatória)
- **Oracles Gate**: `staleness`, `diverg_pct`, `quorum_ok`, `failover`.  
- **Fees Gate**: `Δfee ≤ 20%/5m` e bounds.  
- **Moderação Gate**: pausa/retomada com evidência.  
- **DBT Gate**: tests verdes + artefatos `target/**` + `out/dbt/ce.duckdb`.  
- **Bundle**: tudo em `s4-orr-evidence/out/**`.

---

## 9) Plano de validação (testes)
**Oracles**: injeção de *staleness* e *divergência*; simular falha principal → failover < 60s; verificar quórum.
**Auto‑resolução**: cenários X/Y; validação de trilha e fallback manual com evidência.
**Fees**: cenários de `vol(t)`, `depth(t)`; assert de Δfee e bounds; checar *cooldown/anti‑thrash*.
**Simulação**: `spike/gap/burst` com relatórios determinísticos.  
**Moderação**: falsos positivos; apelações; auditoria.  
**Dados/DBT**: tests e *freshness*; CDC lag.

---

## 10) Roadmap de 10 dias (milestones)
- **D1** Oracles (quórum, TWAP; métricas)  
- **D2** Auto‑resolver (regra + audit)  
- **D3** Fee engine (bounds/αβ/cooldown/anti‑thrash)  
- **D4** Harness simulação + cenários  
- **D5** Moderação (heurística + apelação)  
- **D6** Dados/DBT (contratos + tests)  
- **D7** Observabilidade (spans/dash)  
- **D8** Fault‑Injection & hardening  
- **D9** ORR pack + GA‑Ready checklist  
- **D10** Demo/Review + Retro

---

## 11) RACI
| Área | Responsável (R) | Accountable (A) | Consulted (C) | Informed (I) |
|---|---|---|---|---|
| Oracles | Data/Backend | Eng. Líder | SRE | CE |
| Auto‑resolver | Backend | Eng. Líder | Data, SRE | CE |
| Fees | Quant/Backend | Eng. Líder | Data | CE |
| Simulação | Data/ML | Eng. Líder | Backend | CE |
| Moderação | Ops/Backend | Eng. Líder | Sec/RSK | CE |
| Observabilidade | SRE/Obs | Eng. Líder | Backend/Data | CE |
| Dados/DBT | Data | Eng. Líder | Platform | CE |
| ORR & CI | Platform | Eng. Líder | Todos | CE |

---

## 12) Riscos & mitigação
- **Divergência entre fontes** → quórum + TWAP + bounds.  
- **Thrash de fee** → *cooldown* + Δ bound.  
- **Staleness elevada** → circuit‑breaker + alerta.  
- **Falsos positivos moderação** → apelação + heurística calibrada.  
- **CDC lag** → back‑pressure + observabilidade.  

---

## 13) Entregáveis (DoD — Definition of Done)
1) Gates ORR S5 verdes com evidências (`s4-orr-evidence`).  
2) Dashboards publicados e alinhados às métricas dos gates.  
3) DBT tests verdes e contratos versionados.  
4) Runbook de incidentes de oracles/fees/moderação.  
5) Demo + assinatura *PO, ST, PY, DC, ML, SRE, FE, SEC/RSK, PM/BC*.

---

## 14) Apêndices
**A. Fórmulas**: `Δfee ≤ 20%/5m`, `diverg_pct = |p_max - p_min| / p_mid`, `staleness = now - ts_src`.  
**B. Toggles**: `enable_quorum`, `enable_twap_failover`, `enable_auto_resolve`, `fees.cooldown_ms`, `fees.delta_bound`, `moderation.enabled`.  
**C. Config YAML (exemplo)**
```yaml
oracles:
  sources: [o1,o2,o3]
  quorum: 2
  divergence_pct_max: 0.01
  staleness_ms_max: 30000
  twap: {window_s: 60, failover_s: 60}
fees:
  base: 0.001
  alpha_vol: 0.5
  beta_depth: 0.3
  bounds: {min: 0.0005, max: 0.005}
  cooldown_s: 300
  delta_bound_pct_5m: 0.20
moderation:
  pause_thresholds: {diverg_pct: 0.015}
  appeal: {enabled: true}
```



---

## 15) Algoritmos (1‑página — pseudocódigo + complexidade)

### 15.1 Quórum de oráculos (agregação + detecção de divergência)
**Entrada:** `quotes = [{source, ts, price}]`, `staleness_ms_max=30000`, `diverg_pct_max=0.01`, `quorum=2` (em 3 fontes).  
**Saída:** `{agg_price, quorum_ok, staleness_ok, diverg_pct}`.
```pseudo
function aggregate_quorum(quotes, staleness_ms_max, diver_max, quorum):
  now = clock()
  valid = [q for q in quotes if (now - q.ts) <= staleness_ms_max]
  if len(valid) < quorum: return {quorum_ok:false, staleness_ok:false}
  prices = sort([q.price for q in valid])
  p_mid = median(prices)
  p_min = prices[0]; p_max = prices[-1]
  diverg_pct = abs(p_max - p_min) / p_mid
  staleness_ok = true  # pois filtramos acima
  quorum_ok = len(valid) >= quorum and diverg_pct <= diver_max
  agg_price = p_mid  # robusto a outliers
  return {agg_price, quorum_ok, staleness_ok, diverg_pct}
```
**Complexidade:** `O(n log n)` (ordenação), memória `O(n)`.  
**Bordas:** `n<quorum`, preços iguais, fontes simultaneamente stale.

### 15.2 TWAP com failover (janela fixa W=60s)
**Entrada:** stream `{ts, price}`; **Saída:** `twap_W`.  
**Falha fonte primária:** alternar para secundária se `staleness>W`.
```pseudo
class Twap60:
  W = 60s; dq = deque(); sum_pdt = 0; last_ts = None
  function ingest(ts, price):
    if last_ts != None:
      dt = ts - last_ts
      dq.push({ts: ts, price: price, dt: dt})
      sum_pdt += price * dt
    last_ts = ts
    while dq and (ts - dq.front.ts) > W:
      old = dq.pop_front()
      sum_pdt -= old.price * old.dt
  function twap(ts):
    window = min(W, (dq.back.ts - dq.front.ts) if dq else 0)
    if window == 0: return None
    return sum_pdt / window
```
**Failover:** monitorar `staleness` por fonte; se `>W`, trocar para fonte secundária (sinalizar evento).  
**Complexidade:** `O(1)` amortizado por amostra.

### 15.3 Atualização de fees dinâmicos
`fee(t) = base + α·vol(t) + β·(1/depth(t))`, com bounds `[bmin,bmax]`, *cooldown* e **anti‑thrash** (`Δfee ≤ 20%/5m`).
```pseudo
state last_fee, last_change_ts
function update_fee(now, base, alpha, beta, vol_t, depth_t, bounds, cooldown_s, delta_pct_max):
  raw = base + alpha*vol_t + beta*(1/max(depth_t, eps))
  clamped = clamp(raw, bounds.min, bounds.max)
  if last_fee == None: last_fee = clamped; last_change_ts = now; return last_fee
  # cooldown
  if (now - last_change_ts) < cooldown_s: return last_fee
  # anti-thrash (delta percentual máximo por 5m)
  delta = (clamped - last_fee) / last_fee
  if abs(delta) > delta_pct_max:
    clamped = last_fee * (1 + sign(delta) * delta_pct_max)
  last_fee = clamped; last_change_ts = now
  return last_fee
```
**Complexidade:** `O(1)`; **Bordas:** `depth→0` (usar `eps`), primeira atualização, clock drift.

---

## 16) Matriz de aceitação por requisito (RF‑01…RF‑07)
| RF | Métrica/Janela | Consulta/Regra | Alerta/Gate | Evidência no artifact |
|---|---|---|---|---|
| RF‑01 Quórum ≥2/3 | `quorum_ok` (5m) | contador `quorum_ok_ratio = ok/total` | Gate ORR: `>= 0.67` | `out/oracles/quorum_report.json` |
| RF‑02 TWAP/Failover | `failover_time_s < 60` | medição de `staleness` primária | Gate ORR + alerta SRE | `out/oracles/failover_events.json` |
| RF‑03 Staleness/Diverg. | `staleness≤30s p95`; `diverg_pct≤1%` (5m) | p95/percentil via Prom/relatório | Gate ORR | `out/oracles/stability_summary.json` |
| RF‑04 Auto‑resolução | p50≤60m; p95≤120m | tempo entre evento e *resolve* | Gate ORR | `out/resolve/metrics.jsonl` |
| RF‑05 Fees | `Δfee≤20%/5m` + bounds | variação percentual 5m | Gate ORR | `out/fees/audit.json` |
| RF‑06 Simulação | 3 cenários OK; reprodutível | `make sim-all` exit 0 | Checklist ORR | `out/sim/*.report.json` |
| RF‑07 Moderação | `MTTD≤5m` `MTTM≤15m` | diferença entre `create` e `first_action/resolve` | Gate ORR | `out/moderation/ops_report.json` |

> **Nota:** onde Prometheus não estiver ainda plugado, produzir **relatórios determinísticos** por job no CI e anexar ao `s4-orr-evidence`.

---

## 17) Interfaces canônicas (API & Eventos)

### 17.1 API (REST)
| Método | Endpoint | Request | Response (200) | Erros | SLA |
|---|---|---|---|---|---|
| GET | `/oracle/quote?symbol=BRLUSD` | — | `{price, twap_1m, staleness_ms, quorum_ok}` | 404 símbolo; 503 sem quorum | p95≤150ms |
| POST | `/moderation/pause` | `{symbol, reason}` | `{id, status}` | 400 inválido; 403 RBAC | p95≤300ms |
| POST | `/resolve/apply` | `{event_id, decision}` | `{decision_id, outcome}` | 409 conflito; 422 regra | p95≤300ms |

### 17.2 Eventos (Kafka/NATS, JSON)
- **`oracle.quote`**: `{ts, source, symbol, price, staleness_ms}`  
- **`fee.update`**: `{ts, symbol, fee, components, cooldown}`  
- **`moderation.action`**: `{ts, symbol, action, reason, evidence_uri, actor}`  
- **`resolve.decision`**: `{ts, event_id, rule, decision, actor}`

**Contrato de erro (REST):** `{code, message, trace_id}`.

---

## 18) Segurança, RBAC & Compliance
**Papéis (mínimo):** `viewer`, `operator`, `moderator`, `admin`.  
**Ações:**
- `moderation.pause/limit/resume` → `moderator|admin`
- `resolve.apply/fallback` → `operator|admin`
- leitura dashboards/relatórios → `viewer|*`

**Auditoria (obrigatória):** para cada ação crítica: `{ts, actor, role, action, target, payload_hash, trace_id, outcome}` (JSON line).  
**Retenção:** logs **90 dias** (quente), 12 meses (frio); evidências de ORR na release.  
**Privacidade:** sem PII; evidências sem dados sensíveis.  
**Segredos:** não no repo/CI; usar variáveis de ambiente e *providers* seguros.  
**Mudança:** PR+review obrigatório; feature flags documentadas; *rollback plan* por item.



---

## 19) Plano D1–D10 com *kill‑if‑slip*
> **Regra:** se um marco “kill‑if‑slip” escorregar, cortar imediatamente itens nice‑to‑have e priorizar a entrega do marco antes de prosseguir.

- **D1 — Oracles (quórum + TWAP básico + métricas)** — **kill‑if‑slip**  
  Entregar agregação por quórum, TWAP 60s, métricas `staleness_ms/diverg_pct/quorum_ok`.  
- **D2 — Auto‑resolver (regra + audit trail)**  
  Entregar fluxo mínimo de decisão + auditoria JSONL.  
- **D3 — Fee Engine (bounds/αβ/depth + cooldown + anti‑thrash)** — **kill‑if‑slip**  
  Entregar atualização de fee com Δ bound 20%/5m e cooldown.  
- **D4 — Harness de simulação (spike/gap/burst) + relatórios determinísticos**  
- **D5 — Moderação (pause/retomar + apelação + evidência)**  
- **D6 — Dados/DBT (contratos + tests)**  
- **D7 — Observabilidade (spans + dashboards)**  
- **D8 — Fault‑injection & hardening**  
- **D9 — ORR pack + GA‑Ready checklist**  
- **D10 — Demo/Review + Retro**

---

## 20) Reprodutibilidade total — Makefile & fixtures
**Makefile (alvos mínimos):**
```makefile
.PHONY: dbt-ci sim-all orr-bundle

# Executa deps/debug/run (DuckDB) + tests do dbt
dbt-ci:
	pip install 'dbt-duckdb~=1.8.0'
	dbt deps --profiles-dir ~/.dbt --profile ce_profile
	dbt debug --profiles-dir ~/.dbt --profile ce_profile
	dbt run   --profiles-dir ~/.dbt --profile ce_profile
	dbt test  --profiles-dir ~/.dbt --profile ce_profile

# Roda todos os cenários determinísticos
sim-all:
	SEED=42 python -m tools.sim_harness --fixtures fixtures --scenario spike --out out/sim/spike.report.json
	SEED=42 python -m tools.sim_harness --fixtures fixtures --scenario gap   --out out/sim/gap.report.json
	SEED=42 python -m tools.sim_harness --fixtures fixtures --scenario burst --out out/sim/burst.report.json

# Empacota evidências do ORR
orr-bundle:
	mkdir -p out && zip -r out/s4-orr-evidence.zip out/** target/** logs/** || true
```

**Fixtures (determinísticos):**
- Pasta `fixtures/` com `orders_spike.csv`, `orders_gap.csv`, `orders_burst.csv` e `market_depth.json` (campos min.: ts, best_bid/ask, size).  
- Harness usa `SEED=42` e reprocessa timestamps relativos para runs reprodutíveis.

---

## 21) Toggles & defaults (matriz)
| Toggle | Default | Escopo | Owner | Rollback |
|---|---:|---|---|---|
| `enable_quorum` | `true` | Oracles | Data/Backend | usar fonte única (dev‑only) |
| `enable_twap_failover` | `true` | Oracles | Data/Backend | TWAP sem failover |
| `fees.delta_bound_pct_5m` | `0.20` | Fees | Quant/Backend | elevar cooldown + travar Δ em 10% |
| `fees.cooldown_s` | `300` | Fees | Quant/Backend | aumentar para 600s |
| `moderation.enabled` | `true` | Moderação | Ops/Backend | somente leitura |
| `resolve.auto.enabled` | `true` | Auto‑resolver | Backend | manual‑only |
| `run_slo` (CI, S6) | `false` | ORR | Platform | NO‑OP |

---

## 22) Contratos de dados versionados
**Schema strategy:** JSON/Avro com `schema_version`, compatibilidade **backward**; versionamento no `schema registry` (ou diretório `schemas/`).

Ex.: `schemas/oracle.quote.v1.json`
```json
{ "schema_version": 1,
  "type": "object",
  "required": ["ts","source","symbol","price","staleness_ms"],
  "properties": {
    "ts": {"type":"string","format":"date-time"},
    "source": {"type":"string"},
    "symbol": {"type":"string"},
    "price": {"type":"number"},
    "staleness_ms": {"type":"integer","minimum":0}
  }
}
```

**dbt tests (amostra):** `not_null`, `unique` (quando aplicável), `accepted_values` (labels), `freshness` (para quotes/TWAP). Guardar resultados em `target/`.

---

## 23) Catálogo de erros & política de retry
| Código | Causa | Cliente deve | Retry policy | Idempotência |
|---|---|---|---|---|
| `429` | Rate limit | respeitar `Retry-After` | **Exponencial + jitter**, backoff inicial 250ms | usar `Idempotency-Key` |
| `503` | Service unavailable | retry | **Exponencial + jitter** até 60s | `Idempotency-Key` obrigatório |
| `409` | Conflito | corrigir/reattempt | **Retry** apenas se idempotente | manter `resource_version` |
| `422` | Unprocessable | corrigir input | **Sem retry** | n/a |
| `4xx` (auth) | RBAC/token | renovar credenciais | **Sem retry** | n/a |

**Eventos duplicados:** deduplicar por `event_id` / `hash(payload)` em janela de 24h.

---

## 24) Adversarial / Anti‑gaming (1‑página)
- **Depth spoofing**: inflar/retirar *depth* em livros → **Mitigação**: medianas por janela, filtros de volume mínimo, penalização de fontes inconsistentes.
- **Source drift**: uma fonte desvia lentamente → **Mitigação**: divergência relativa (1%), outlier detection e reponderação.
- **Sandbagging de fee**: manipular `vol(t)` para reduzir fee → **Mitigação**: suavização, cooldown e auditoria de deltas.
- **Staleness intencional**: atrasar quotes para gatilhar failover → **Mitigação**: monitorar `staleness_ms` por fonte; *quarantine* temporária.

---

## 25) Invariantes formais adicionais (safety/liveness)
**Safety**  
S‑1: `quorum_ok ⇒ (diverg_pct ≤ 0.01 ∧ staleness_ms ≤ 30000)`.  
S‑2: `abs(fee(t) − fee(t−5m)) / fee(t−5m) ≤ 0.20`.  

**Liveness**  
L‑1: `staleness_ms > W ⇒ ◇(failover_time_s < 60)`.  
L‑2: `moderation.pause ⇒ ◇(moderation.resume ∨ appeal.open)`.

> Opcional: esboçar TLA+ com variáveis `fee`, `delta5m`, `quorum_ok`, `staleness_ms` e invariantes acima.

---

## 26) Observabilidade canônica — labels e nomes
**Labels padrão:** `{service, env, region, symbol, source}`.  
**Métricas nomeadas:** `staleness_ms`, `diverg_pct`, `quorum_ok` (0/1), `failover_time_s`, `delta_fee_5m`, `ttpv_p95_ms`, `moderation_pauses_total`.

---

## 27) Mini‑runbook de incidentes (1 página)
**Oracles**: verificar `staleness/divergência/quorum`; se `quorum_ok=false` → alternar fonte, registrar `failover_event`, abrir ticket.  
**Fees**: picos de `delta_fee_5m` → aplicar `cooldown_hard`, revisar parâmetros; anexar auditoria.  
**Moderação**: ao disparar `pause`, abrir `appeal` automaticamente; SLAs de MTTD/MTTM; anexar evidências.

Checklist pós‑incidente: relatório curto + links (dashboards, logs, evidência ORR) anexados.

---

## 28) Capacidade & carga (alvos)
| Serviço | TPS alvo | p50 | p95 | Headroom |
|---|---:|---:|---:|---:|
| Oracle Aggregator | 200 | 50ms | 150ms | 30% |
| Auto‑Resolver | 50 | 80ms | 300ms | 30% |
| Fee Engine | 100 | 40ms | 120ms | 30% |
| Moderation | 20 | 80ms | 300ms | 30% |

**Nota:** **TTPV p95 ≤ 800ms** sem regressão; ajustar sinais de alerta.



---

## 29) Matriz de rastreabilidade (RF → Teste → Evidência → Owner)
| RF | Componente(s) | Teste(s) ID | Evidência (artefato) | Owner |
|---|---|---|---|---|
| RF‑01 Quórum ≥2/3 | Oracle Adapters, Aggregator | ORC‑Q01 (unit), ORC‑Q02 (integ) | `out/oracles/quorum_report.json` | Data/Backend |
| RF‑02 TWAP/Failover <60s | TWAP Engine | ORC‑T01 (unit), ORC‑F01 (fault) | `out/oracles/failover_events.json` | Data/Backend |
| RF‑03 Staleness≤30s p95, Diverg≤1%/5m | Oracles | ORC‑S01 (prom), ORC‑D01 (integ) | `out/oracles/stability_summary.json` | SRE/Data |
| RF‑04 Auto‑resolução | Auto‑Resolver | RES‑A01 (unit), RES‑A02 (integ) | `out/resolve/metrics.jsonl` | Backend |
| RF‑05 Fees Δ≤20%/5m | Fee Engine | FEE‑U01 (unit), FEE‑I01 (integ) | `out/fees/audit.json` | Quant/Backend |
| RF‑06 Simulação 3 cenários | Sim Harness | SIM‑S01/02/03 | `out/sim/*.report.json` | Data/ML |
| RF‑07 Moderação MTTD/MTTM | Moderation | MOD‑M01/M02 | `out/moderation/ops_report.json` | Ops/Backend |

---

## 30) Fluxos essenciais (diagramas de sequência — texto)
**Oracle → Aggregator → TWAP → Consumers**
```
Source_i -> Adapter_i: fetch()
Adapter_i -> Aggregator: quote{price, ts}
Aggregator -> Aggregator: aggregate_quorum()
Aggregator -> TWAP: ingest(price, ts)
TWAP -> API: twap_1m
API -> Client: {price_mid, twap_1m, staleness_ms, quorum_ok}
```
**Moderation**
```
Alert -> Moderator: propose(pause)
Moderator -> ModerationSvc: /moderation/pause
ModerationSvc -> Audit: log(action)
ModerationSvc -> System: apply(pause)
System -> ModerationSvc: status
ModerationSvc -> Client: {id, status}
```

---

## 31) Máquinas de estado (resumo)
**Auto‑Resolver**: `Idle → Evaluating → Applied | Rejected → Idle`  
- Guardas: `quorum_ok`, `diverg_pct`, `truth_rule_ok`  
- Saídas: `resolve.decision`, audit

**Moderação**: `Open → Paused → (Appeal Open) → Resumed | Closed`  
- SLAs: MTTD≤5m, MTTM≤15m; transições auditadas

---

## 32) Ameaças (STRIDE) & mitigação
| Categoria | Exemplo | Mitigação |
|---|---|---|
| Spoofing | fonte falsa de quote | autenticação fonte, allowlist, TLS |
| Tampering | manipular payload | assinatura/hmac e audit hash |
| Repudiation | negar ação de moderação | audit com `{trace_id, actor, payload_hash}` |
| Information Disclosure | logs sensíveis | sem PII; mascaramento; RBAC |
| DoS | bursts/picos | rate‑limit, backpressure, cooldown |
| Elevation of Privilege | pause indevido | RBAC mínimo, 4‑eyes para ações críticas |

---

## 33) Plano de carga & caos
- **Carga**: alvo TPS por serviço (§28), p95 dentro de budget; cenários spike/gap/burst.
- **Caos**: matar fonte primária; injetar staleness/divergência; latência de rede; loss 5–10%.
- **Aceite**: failover<60s; quórum≥2/3; Δfee dentro de bound; sem erro 5xx ≥1%.

---

## 34) Governança de dados & DQ (dbt)
- Tests por tabela: `not_null`, `unique` (quando aplicável), `accepted_values`, `freshness` (quotes/TWAP).  
- **Limiares de aceite**: 100% pass nos testes críticos; `freshness` dentro de janelas definidas.

---

## 35) Plano de release & rollback (canary)
- **Fases**: 5% → 25% → 100% (cada 2h) com abort se qualquer gate romper.  
- **Abort**: reverter feature flags (`enable_*`), rollback canário, nota de auditoria.  
- **Comms**: broadcast interno a cada fase; resumo final.

---

## 36) Checklist de aceite ORR (com IDs)
- [ ] ORC‑Q02: agregação por quórum aprovada  
- [ ] ORC‑F01: failover < 60s evidenciado  
- [ ] ORC‑S01/D01: staleness/divergência dentro do limiar  
- [ ] FEE‑I01: Δfee 5m ≤ 20%  
- [ ] MOD‑M01/M02: MTTD/MTTM ok  
- [ ] SIM‑S01/02/03: relatórios presentes  
- [ ] DBT tests: verdes com evidência

---

## 37) Launch Readiness Score (LRS)
`LRS = 0.4·GateCore + 0.2·Perf + 0.2·DataDQ + 0.2·Obs`  
- **GateCore** = média binária (Oracles, Fees, Moderação, Auto‑Resolver)  
- **Perf** = normalizado por orçamentos p95  
- **DataDQ** = proporção de testes dbt críticos pass  
- **Obs** = presença de métricas+traces+dashboards  
**Go/No‑Go:** LRS ≥ **0.90**.

---

## 38) SLIs/SLOs por serviço (amostra)
| Serviço | SLI | SLO | Consulta |
|---|---|---|---|
| Aggregator | disponibilidade | 99.5%/30d | `sum(rate(req_total{code!~"5.."}[5m]))/sum(rate(req_total[5m]))` |
| TWAP | latência cálculo | p95≤50ms | histograma p95 |
| Fee | TTPV | p95≤800ms | traço `fee.update` |
| Moderation | MTTD/MTTM | ≤5m/≤15m | logs → métricas |

---

## 39) Dashboards (painéis mínimos)
- **Oracles**: staleness, divergência, quorum, failover timeline  
- **Fees**: Δfee 5m, bounds, cooldown hits  
- **Auto‑Resolver**: decisões, tempos, erros  
- **Moderação**: pausas, apelações, SLAs  
- **Simulação**: resultados por cenário  
- **Saúde**: p95/p50, taxa 5xx, saturação

---

## 40) Ambientes & dependências (matriz)
| Item | Versão | Porta | Base Image |
|---|---|---:|---|
| Aggregator | 1.x | 8081 | gcr.io/distroless/base |
| TWAP Engine | 1.x | lib | alpine:3.19 |
| Fee Engine | 1.x | 8082 | gcr.io/distroless/base |
| ModerationSvc | 1.x | 8090 | python:3.11-alpine |

---

## 41) Plano de comunicação
- Kickoff S5, atualizações D3/D6/D9, convite demo D10, changelog na release.

---

## 42) Assunções & questões em aberto
- Ass.: três fontes de oráculos com SLA básico; latência <1s.  
- Q: tolerância de divergência por símbolo (pode variar?).  
- Q: limites de fee específicos por mercado.

---

## 43) OpenAPI (esqueleto mínimo)
```yaml
openapi: 3.0.3
info: {title: MBP APIs, version: 0.1.0}
paths:
  /oracle/quote:
    get:
      parameters:
        - in: query; name: symbol; schema: {type: string}
      responses:
        '200': {description: OK}
  /moderation/pause:
    post:
      requestBody: {required: true}
      responses:
        '200': {description: OK}
```

---

## 44) Biblioteca PromQL (consultas prontas)
- Staleness: `max_over_time(staleness_ms[5m])`  
- Divergência: `max(price) - min(price) / median(price)` (por janela)  
- Quórum_ok ratio: `sum(quorum_ok)/sum(total)`  
- Δfee 5m: `rate(fee_value[5m])/avg_over_time(fee_value[5m])`

---

## 45) Ergonomia Dev (pre‑commit, linters)
- Hooks: `black/ruff` (py), `shellcheck` (sh), `hadolint` (Dockerfile), `yamllint`.  
- CODEOWNERS por trilha, convenções de teste: `test_<unit|integ>_<nome>.py`.

---

## 46) Segurança no CI (regras)
- **Semgrep**: regras específicas para uso de `requests`, validação de entrada, secrets.  
- **Gitleaks**: baseline em `/.gitleaks.toml`.  
- **Trivy**: varredura das imagens base.

---

## 47) Privacidade & retenção (detalhe)
- Logs sem PII; retenção 90d (quente), 12m (frio); evidências anexas à release.

---

## 48) Instrumentação — tarefas
- Expor métricas: `quorum_ok`, `diverg_pct`, `staleness_ms`, `failover_time_s`, `delta_fee_5m`.  
- Tracing: spans nomeados e correlação com logs.

---

## 49) Acordos com fontes externas (oráculos)
- SLA mínimo; contratos de latência e uptime; canais de incidentes; plano de fallback documentado.

