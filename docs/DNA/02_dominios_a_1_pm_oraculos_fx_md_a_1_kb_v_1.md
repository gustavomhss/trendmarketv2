---
file: 02-Dominios-A1-PM-Oraculos-FX.md
version: v1.1 (A1 KB — Deepdive Ilustres)
date: 2025-09-09
owner: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: domain-canonical
---

# 02) Domínios A1 — PM Core, Oráculos, FX/CIP & Roteamento (versão inspeção "Comitê de Ilustres")
> **Propósito:** especificar o **como** técnico de PM Core, Oráculos Regionais e FX (CIP + Rotas) para cumprir o **NSM** (*Time‑to‑Preço‑Válido p95 ≤ 800 ms*) com **governança forte** (watchers + hooks A110), **segurança** e **auditoria**. Documento revisado com **padrões de excelência** (Bezos—Working Backwards, Jobs—Simplicidade, Knuth—Rigor, Perez—Operação).

---

## 0) Readiness & Handshake (antes de executar)
- Verifique `brief_context.yaml` (Arquivo 01) → NSM, SLOs, regiões/CLS.  
- Confirme **watchers ON**: `oracle_divergence_watch`, `fx_delta_benchmark_watch`, `auction_invariant_breach_watch`, `slo_budget_breach_watch`.  
- Lint de **hooks** (`hooks/a1.yaml`) e presença de **contratos** (Arquivo 03).  
- Publique *press‑note* (2 linhas) + **métrica de entrada** que a mudança vai mover.

**Press‑note (template):** “Entregamos <componente> reduzindo <métrica‑entrada> em <Δ> → NSM p95 melhora <Δ>.”

**Budget de latência (referência rápida):** PM‑cotação (505ms p95), PM+FX (675ms p95). Ver tabela no Arquivo 01.

---

## 1) PM Core — Mecanismos de Leilão, Fairness & Settlement
### 1.1 Modelo de Clearing por **Custo Efetivo**
**Objetivo:** maximizar eficiência e fairness mantendo invariantes formais.

**Função de custo efetivo (canônico):**
```math
\text{effective_cost}(b)=w_s\cdot p + w_q\cdot f_q(q) + w_r\cdot f_r(\sigma) + w_t\cdot f_t(\Delta t)
```
- `p`: preço; `q`: quantidade; `σ`: risco (vol); `Δt`: idade do lance; `w_*` calibrados via notebooks.

**Algoritmo (pseudo) — O(n log n) e determinístico:**
```python
SEED = public_seed()
bids = stable_sort(bids, key=(effective_cost, ts_server, H(SEED||bid_id)))
alloc = []; cap = 0
for b in bids:
    if cap >= K_star: break
    take = min(b.size, K_star - cap)
    alloc.append((b.id, take))
    cap += take
clearing_price = price_from_aggregate(alloc, bids)
```
**Tie‑break determinístico:** `effective_cost → ts_server → H(seed||bid_id)`.

**Invariantes (devem sempre ser verdade):**
- **Monotonicidade:** ∂alloc/∂price ≥ 0 (nenhum incentivo perverso).  
- **Budget‑balance:** ∑alloc ≤ **K\***.  
- **Determinismo:** mesma entrada + `SEED` ⇒ mesmo resultado.  
- **Complexidade:** O(n log n) (com prova em GN‑PM‑INV).

**Property‑based tests (exemplos):**
```python
# 1) Monotonicidade
assume(bi.price<=bj.price and bi.same_other_attrs(bj))
assert alloc(bi)<=alloc(bj)
# 2) Budget-balance
assert sum(q for _,q in alloc)<=K_star
# 3) Determinismo
assert run_with_seed(S)==run_with_seed(S)
```

### 1.2 Fairness por **ELO** (ponderação) com caps
```math
w_{elo}=clip\bigg(1+\frac{ELO-\bar{ELO}}{\kappa}\,,\,0.9,1.1\bigg),\quad ELO_{t+1}=ELO_t+K(\text{outcome}-\hat p)
```
- **Decay semanal:** 1%. **Caps:** ±10% no peso.

### 1.3 Settlement & Auditoria
- **Idempotência:** `Idempotency-Key` em `pm_bid_submitted`.  
- **Evento canônico:** `pm_clearing_result` com `hash_attestation`.  
- **Reprocesso seguro:** ordenação parcial `(market_id, ts_server)`; tolerância a replays.

### 1.4 Observabilidade (PM)
- Métricas: `pm.fill_rate`, `pm.thickness`, `pm.auction_invariant_breach`, `pm.clearing_latency_ms`.  
- Traces: `market_id`, `region`, `seed_id`.

---

## 2) Oráculos Regionais — Feeds, Qualidade, Quorum, TWAP & Failover
### 2.1 Pipeline
**Conectores (N≥3)** → normalização → **filtros robustos** (MAD/quantis/Hampel) → **quorum** (ponderado por `quality_score`) → **TWAP(K)** → persistência → `oracle_price_update`.

**Filtro MAD/Quantis (exemplo):**
```python
med = pct(window, 50)
mad = median(abs(x-med) for x in window)
score = abs(price-med)/(mad+1e-9)
keep = score < TAU(feed,asset,region)
```

**quality_score (0..1) sugerido:**
```math
q=0.4\cdot uptime_{30d}+0.3\cdot (1-divergence_{eps})+0.3\cdot recency_{p95}
```

**Quorum ponderado:**
```python
w = normalize([quality_score_i])
q_price = sum(w_i*price_i)/sum(w_i)
```

**TWAP(K):**
```python
TWAP = sum(p_i * dt_i) / sum(dt_i)  # janela K por ativo/região
```

### 2.2 SLOs & Qualidade
- **Staleness p95** < **30 s**; **recency pass ≥ 99,5%**; **error rate < 0,1%**.  
- **Divergência ε**: `|q_price − TWAP| ≤ ε` (ε por mercado/ativo; default no Arq. 05).  
- **Banimento temporário**: fonte com violação recorrente de divergência/staleness.

### 2.3 Failover & Histerese (Hooks)
```yaml
- id: a1_oracle_staleness_guard
  when: "oracle.staleness_ms>30000•5m"
  then: ["switch_to_twap_failover","notify=A1"]
  rollback: "yes"
- id: a1_oracle_divergence_guard
  when: "oracle.divergence_eps>EPS_LIMIT•10m"
  then: ["ban_source_temp","recalc_quorum","notify=A1"]
  rollback: "yes"
```

### 2.4 Observabilidade (Oráculos)
- Métricas: `oracle.staleness_ms.p95`, `oracle.divergence_eps`, `oracle.quorum_size`, `oracle.failover_events`.  
- Dashboards: “Oracle & PM Health” (Arquivo 05).

### 2.5 Calibração & Notas Operacionais
- **TAU** (limiar MAD) calibrado semanal por feed/ativo.  
- **K (TWAP)** por volatilidade/horário local.  
- **Holydays**/feriados regionais ajustam janelas e quorum.

---

## 3) FX — **CIP** & Roteamento Multi‑Venues
### 3.1 **CIP** (Covered Interest Parity)
**Linear:** \( F = S\cdot\frac{1 + r_d T}{1 + r_f T} \)  
**Contínuo:** \( F = S\cdot e^{(r_d - r_f)T} \)

**Detalhes práticos:**
- **T** conforme convenção **day‑count** (e.g., ACT/360, ACT/365).  
- **Forward points**: `pts = (F − S)·10^4`.  
- **NDF**: considerar `r_f` implícita.  
- **Triangular check** (opcional): arbitragem cruzada em 3 pares.

**Checagem:** `|F_mkt − F_model| ≤ ε` por **par/tenor** (ε por vol/liq.).

### 3.2 Agregação & **Best‑Execution**
**Score de rota (exemplo):**
```math
score = α·latency_ms + β·slippage_bps + γ·(1-uptime)
```
Com `α,β,γ` por **par/tenor** (ver política).

**Política (YAML):**
```yaml
route_policy:
  weights:
    USD/BRL:
      SPOT: { alpha: 0.6, beta: 0.3, gamma: 0.1 }
      "1M": { alpha: 0.5, beta: 0.4, gamma: 0.1 }
  breaker:
    when: "fx.route_latency.p95>1500•5m"
    then: ["degradar_para_pack_lite","prefer_low_latency"]
    clear_when: "fx.route_latency.p95<1200•10m"
  risk_controls:
    notional_cap_per_min: 5000000
    venue_quota_pct: 0.5
```

**Roteador (pseudo):**
```python
venues = discover(pair, tenor)
stats  = pull_stats(venues)
scored = [(v, α*s.lat + β*s.slip + γ*(1-s.up)) for v,s in stats]
best   = min(scored, key=lambda x: x[1])
quote  = fetch(best.venue)
assert abs(quote.forward - cip_model(...)) <= eps
return quote
```

### 3.3 CLS & Pay‑in Cutoffs
- Respeitar calendário **CLS** por par/moeda. Misses ⇒ `cls_payin_cutoff_watch` (A1 owner).  
- Regras operacionais por região/feriado (Arquivo 01 → `brief_context`).

### 3.4 Observabilidade (FX)
- Métricas: `fx.route_latency.p95`, `fx.venue_uptime`, `fx.cip_delta_eps`, `fx.quotes_per_min`.  
- Hooks: `a1_fx_router_latency_guard`.

### 3.5 Controles de Risco & Compliance
- **Notional cap** por janela e por venue.  
- **Quotas** por venue (anti concentração).  
- **Kill‑switch** manual; logs/auditoria ≥95%.

---

## 4) On‑chain (opcional) — Assinaturas & Auditoria
### 4.1 EIP‑712 (ordens/lances)
**Domain (exemplo):**
```json
{"name":"CreditEngine/PM","version":"1","chainId":1,"verifyingContract":"0x0000000000000000000000000000000000000000"}
```
**TypedData (bid):**
```json
{"types":{"Bid":[{"name":"market_id","type":"bytes16"},{"name":"participant","type":"bytes20"},{"name":"side","type":"uint8"},{"name":"price","type":"uint256"},{"name":"size","type":"uint256"},{"name":"nonce","type":"uint256"}]},"primaryType":"Bid"}
```
- **Nonce** por participante; **replay protection**; validação de domínio/chainId.

### 4.2 Commit‑Reveal (anti‑MEV)
```
1) Commit: hash = H(lance||salt||nonce)
2) Janela de commits
3) Reveal: lance + salt + nonce
4) Verificação e rejeição se fora da janela/ inválido
```

### 4.3 Âncoras de Auditoria
- Publicar hash de `pm_clearing_result` em rede pública/permissionada quando exigido.

---

## 5) Observabilidade — Mapa de Métricas (recorte)
| Domínio | Métrica | Alvo | Nota |
|---|---|---:|---|
| PM | `pm.fill_rate` | ≥ Y% | ajustar por mercado |
| PM | `pm.clearing_latency_ms.p95` | ≤ 150 | budget do pm‑svc |
| Oráculos | `oracle.staleness_ms.p95` | < 30000 | janela K por ativo |
| Oráculos | `oracle.divergence_eps` | ≤ ε | calibrar por vol |
| FX | `fx.route_latency.p95` | ≤ 1500 | breaker/histerese |
| FX | `fx.cip_delta_eps` | ≤ ε | par/tenor |

> Dashboards e painéis no Arquivo **05**.

---

## 6) Testes — Estratégia por Camada (A1)
### 6.1 Unit
- Clearing (monotonicidade, budget‑balance, determinismo).  
- Filtros (MAD/quantis) preservam mediana sob outliers.  
- CIP: `|F_mkt−F_model| ≤ ε` (par/tenor).

### 6.2 Property‑based
- PM: invariantes sob amostras aleatórias e seeds.  
- Oráculos: staleness/divergência sob jitter/falhas; **metamórficos** (duplicar/escala não muda mediana).  
- FX: escolha de rota ótima sob trade‑offs (latência vs slippage).

### 6.3 Integração
- Conectores reais (N≥3) e banimento temporário.  
- Venues FX com alternância e breaker.

### 6.4 E2E
- Book → clearing → `pm_clearing_result` → DEC.  
- Oráculos → TWAP → cotação PM/FX.

### 6.5 Carga/Resiliência
- p95 E2E (PM) ≤ 800 ms; p95 rota FX ≤ 1500 ms.  
- Caos‑lite: atraso artificial em 1 feed/venue → hooks disparam e recuperam.

### 6.6 Cobertura & Gates
- **Cobertura alvo:** unit ≥ 80%, critical paths 100% (clearing, hooks).  
- **Gates:** reprovação se **contract tests** ou **hooks** falharem.

---

## 7) FMEA — Falhas, Detecção & Mitigação
| Componente | Falha | Detecção | Hook/Runbook | Mitigação |
|---|---|---|---|---|
| Oráculo | *Staleness* ↑ | `oracle.staleness_ms.p95` | `a1_oracle_staleness_guard` | Failover TWAP + reweight quorum |
| Oráculo | Divergência | `oracle.divergence_eps` | `a1_oracle_divergence_guard` | Banir fonte + recalibrar ε |
| PM | Violação de invariante | `pm.auction_invariant_breach` | `a1_auction_invariant_guard` | `pause_market` + dump + postmortem |
| FX | Latência de rota ↑ | `fx.route_latency.p95` | `a1_fx_router_latency_guard` | `pack_lite` + alternar venue |
| FX | CIP desancorado | `fx.cip_delta_eps` | alerta SLO | ajustar pesos/tenor ou suspender execução |

---

## 8) Interfaces & Hand‑offs
- **→ A2 (Data):** contratos/CDC/dbt; *breaking* bloqueia release; `schema_registry_drift_watch`.  
- **→ A3 (Decision/APIs/FE):** `pm_clearing_result`, `fx_quote`; tratadores de erro/idempotência; `api_breaking_change_watch`.  
- **↔ A4 (ML):** features/sinais; metadados de `model_score_event`; SRM em A/B.  
- **↔ A5 (SRE):** SLO/alertas; runbooks; DR tabletop.

---

## 9) Roadmap Domínio (30/60/90)
- **D0–30:** PM matching/clearing + invariantes; 3 conectores; filtros/quorum/TWAP; métricas base.  
- **D31–60:** Failover/histerese; settlement/idempotência; CIP check; dashboards; hooks.  
- **D61–90:** Multi‑venues/roteamento; breaker; âncoras de auditoria; carga #1; hardening.

---

## 10) Artefatos & Onde Encontrar
- **Contratos:** Arquivo 03 (`contracts/*.schema.json`).  
- **APIs:** Arquivo 03 (`openapi/a1.yaml`).  
- **Hooks/Policies:** Arquivo 04 (`hooks/a1.yaml`).  
- **Dashboards/Evidence:** Arquivo 05.  
- **Segurança/On‑chain/Glossário:** Arquivo 06.

---
**Fim (v1.1).** Documento **refinado pelo Comitê**: PM/Oráculos/FX executáveis, auditáveis e reversíveis. Impacto direto no **NSM**, com simplicidade (Jobs), rigor (Knuth), operação (Perez) e foco em resultado (Bezos).

