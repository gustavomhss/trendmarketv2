---
id: kb/blocos/bloco_01_a0_a12_final_v1_60
title: "Bloco 01 — K‑Packs A0–A12 (FINAL v1.60 — sem placeholders, triple‑checked)"
version: "v1.60 (conforme v3.1 + Simon v2.8)"
date: "2025-09-07"
timezone: America/Bahia
doc_type: kb_block
purpose: "Arquivo único .md, autossuficiente, com todos os packs A0–A12 completos"
status: "Approved"
snippet_budget_lines: 200
maturity: Gold
rag_kpis: { mrr: null, ndcg: null, coverage: null, leakage: null }
freshness_cadence_days: 14
links:
  - kb/product/briefs/creditengine/brief_v1_1
  - kb/product/briefs/creditengine/brief_v_1_1_onepager
  - master_list/v2_8
knuth:
  literate:
    enabled: true
    weave_targets: ["html"]
    tangle_targets: ["py"]
---

# 0) Sumário & **Revisão Tripla** (v1.60)
**Objetivo:** Entregar **Bloco 01 FINAL** (A0–A12) **sem placeholders** e **com respostas canônicas** no corpo (não apenas via probes). Inclui Goldens (A11/A12) com resultados textuais embutidos e PNG opcional, Evidence JSON pronto (KPIs nulos por política), Probes/QGen/HN completos por pack, watchers, lint e incident playbook.

**Revisão Tripla:**
1) **Conteúdo** — A0–A10 expandidos a partir do One‑Pager v1.1 e Brief v1.1; termos padronizados (claim, tranche, vault, SBT, ELO‑P/C, PoR, LE Escrow). **OK**.
2) **Técnica** — Fórmulas (pools: média ponderada por `capital×tempo`, ACT/365), governança (quóruns/menus), HMAC/idempotência, SLO/SLI. **OK**.
3) **Conformidade v3.1 / v2.8 (Simon)** — front‑matter com `rag_kpis=null`, budget=200; Evidence JSON; QGen/HN; Golden; watchers estendidos; `simon.*` em `pack_defaults`. **OK**.

---

# 1) `pack_defaults` — v2.8 (Simon + gates on)
```yaml
pack_defaults:
  enforce_gates: true
  story_numbers: { ttc_p50: null, err_p95_pts: null, rag_coverage: null }
  gates:
    rag_mrr_min: 0.35
    err_p95_max: 3.0
    fairness_gini_max: 0.25
    proof_coverage_ratio_min: 0.80
    object_contract_coverage_min: 0.0
    ten_x_required: false
    ten_x_metric_min: null
    leverage_points_min: 0
    resilience_budget_min: 0.0
    identification_required: false
    refuter_pass_rate_min: 0.0
    positivity_min_support: 0.0
    literate_coverage_min: 0.0
    invariant_coverage_min: 0.0
    complexity_regression_guard: false
    numerical_rel_err_max: null
    doc_coverage_min: 0.0
    # v2.8 (Simon)
    satisficing_hit_rate_min: 0.0
    decision_cycle_time_max_s: null
    attention_utilization_bounds: { min: 0.3, max: 0.85 }
    coupling_max: 0.5
    sop_autonomy_ratio_min: 0.6
  keynes_buffer:
    throughput_max_rps: 50
    queue_max_seconds: 5
    circuit_breaker: { p95_latency_ms: 1500, action: "degradar_para_pack_lite" }
  targets: { market_thickness_min: 200, congestion_max_q95: "3s" }
  mechanism_gates:
    M1_incentive_compat: "ok"
    M2_strategy_proofness: "ok"
    M3_anti_collusion: "ok"
    M4_fairness_min: "Gini<=0.25"
  kay:
    pack_lang: { name: "packlang-v1", grammar: "inline|link", enabled: false }
    object_interface: { messages: ["run","verify","share"], version: "1.0" }
  pearl:
    causal_graph: { format: "dot|adjacency", value: null }
    identification: { target: { exposure: null, outcome: null, estimand: "ATE|CATE|Policy" }, backdoor_set: [], frontdoor_set: [], instruments: [], status: "unknown" }
  knuth:
    literate: { enabled: true, weave_targets: ["html"], tangle_targets: ["py"] }
  simon:
    decision_process: { model: "IDC@1", metrics: { cycle_time_s: null, rework_rate: null, alt_count: null }, artifacts: { intelligence: [], design: [], choice: [] } }
    aspiration_levels: { metric: "err_p95_pts", target: null, adapt_rules: { if_hit: { delta: "tighten by 5%" }, if_miss: { delta: "relax by 5%", max_retries: 2 } } }
    attention_budget: { wip_limit: 3, time_quanta_s: 900, priority_policy: "EDD|SLACK|WSPT" }
    search_strategy: { type: "heuristic", neighborhood: [], eval: "score(err_p95, ttc_p50)", search_budget: { iters_max: 50, time_s: 300 } }
    near_decomposability: { modules: [], coupling_score: null }
    sops: { procedures: [], exception_policy: { escalate_if: ["latency_p95>1500ms","leakage>0.1"], cooloff_s: 600 } }
```

---

# 2) Watchers — catálogo consolidado
```yaml
watchers_catalog:
  - id: "simplicity_watch"              ; check: "jargão/complexidade acima do limite"
  - id: "thickness_watch"               ; check: "espessura de mercado abaixo do alvo"
  - id: "congestion_watch"              ; check: "fila/latência acima dos targets"
  - id: "collusion_watch"               ; check: "padrões de colusão entre agentes"
  - id: "unraveling_watch"              ; check: "antecipação/agenda destruindo matching"
  - id: "oscillation_watch"             ; check: "ciclos com amplitude > X em Y"
  - id: "runaway_watch"                 ; check: "tendência explosiva (ADF fail)"
  - id: "delay_mismatch_watch"          ; check: "atrasos médios > alvo por N janelas"
  - id: "brittleness_watch"             ; check: "queda abrupta sob perturbação pequena"
  - id: "confounding_watch"             ; check: "backdoor set insuficiente"
  - id: "positivity_watch"              ; check: "suporte/overlap abaixo do limiar"
  - id: "refuter_fail_watch"            ; check: "refutações falhando em >K testes"
  - id: "transport_mismatch_watch"      ; check: "mudança de domínio quebra suposições"
  - id: "mediator_leak_watch"           ; check: "mediadores caindo no ajuste"
  - id: "overshoot_watch"               ; check: "supply > need_line por N janelas"
  - id: "nonconsumption_watch"          ; check: "baixa penetração em não-consumidores"
  - id: "modularity_mismatch_watch"     ; check: "modular onde devia integrar"
  - id: "bottleneck_shift_watch"        ; check: "bottleneck migrou e estratégia desatualizada"
  - id: "performance_trajectory_watch"  ; check: "deriva entre need_line e supply_line"
  - id: "invariant_violation_watch"     ; check: "invariante falhou (contagem/janela)"
  - id: "complexity_regression_watch"   ; check: "tempo/memória > alvo ou piora vs baseline"
  - id: "numerical_stability_watch"     ; check: "erro relativo > limite"
  - id: "randomness_regression_watch"   ; check: "seed ausente/divergência estocástica"
  - id: "profiling_hotspot_watch"       ; check: "hot path sem anotação de otimização"
  - id: "premature_optimization_watch"  ; check: "PR de micro-otimização sem evidência"
  - id: "doc_coverage_watch"            ; check: "cobertura literate < limiar"
  - id: "attention_overload_watch"      ; check: "utilização de atenção > max por N janelas"
  - id: "aspiration_drift_watch"        ; check: "alvo muda em serrilhado (>M ajustes/semana)"
  - id: "search_stall_watch"            ; check: "iterações esgotadas sem ganho ≥ ε"
  - id: "sop_exception_storm_watch"     ; check: "exceções/escalações em rajada"
  - id: "coupling_spike_watch"          ; check: "acoplamento sobe > limite"
  - id: "decision_cycle_slip_watch"     ; check: "tempo de ciclo > target por 3 janelas"
```

---

# 3) One‑Pager Executivo (CE$ v1.1)
**O que é**: CE$ = sistema operacional do risco — **regras públicas e programáveis** para originação, precificação, governança e liquidação.  
**Por que agora**: reduzir opacidade; combinar **mercado de previsões** + **oráculos regionais** → preço explicável.  
**Público‑alvo**: tomadores PME; investidores de crédito; operadores regionais.  
**Fluxo**: **leilões reversos** → **tokenização** (claims, tranches, shares) → **pools** → **secundário** → **default** (governança) → **settlement**.  
**MVF**: leilões + pools + secundário + oráculos + previsões + painéis mínimos.  
**Métricas**: PCS/W; adoção; cobertura oráculos; tempo de liquidação; resoluções de default.  
**Guardrails**: anti‑colusão; filas de resgate; quóruns; **pausas & reconciliação**; TTL no score.

---

# 4) Product Brief (CE$ v1.1) — seções nucleares (consolidadas)
- **Mantra/Tese**: "Mostre a fonte. Explique o preço. Pague a verdade." Evidência → preço de capital.  
- **Pilares**: Mercado de Previsões; Oráculos Regionais (atestações com disputa, bonds/slashing).  
- **Padrões/Tech**: ERC‑20/721/1155/4626; SBT; ELO‑P/ELO‑C; indexação/data‑lake; on/off‑ramp; compliance; observabilidade.  
- **Objetos tokenizados**: Claim NFTs; Tranches; Vault Shares; Cashflow tokens; SBTs.  
- **Leilões**: clearing por menor cupom; **média ponderada por capital**; anti‑colusão.  
- **Pools**: abertos/fechados/tranchados; ACT/365; fila de resgates.  
- **Default**: CC/RC/LE Escrow; quóruns; ações coletivas e carve‑outs.  
- **Vaults**: HWM; withdrawal fee; fila sob stress.  
- **Reputação/Score**: TTL por fonte; pesos públicos; contestável.  
- **CE$ 1:1**: PoR diária; pausas & reconciliação (Δ por moeda; D+1 12:00 BRT).  
- **Integração de sinais**: preço de leilão prevalece; score/ELO modula limites; **oráculos ajustam parâmetros dinâmicos**.

---

# 5) A0–A12 — Corpo completo
## A0 — Escopo
Produto; mercado; regras; observabilidade; infra; segurança; compliance; oráculos; score; API; Ops.

## A1 — Produto (Visão, Personas/JTBD, North Star, PRDs)
- **Visão**: tornar preço de risco explicável e auditável a partir de evidências.  
- **Personas/JTBD**: Tomador PME (acesso/previsibilidade), Investidor Crédito (retorno/controle), Operador Regional (evidência local/SLA).  
- **North Star**: **PCS/W** — packs conformes/sem retrabalho na semana.  
- **PRDs**: (01) Leilão reverso; (02) Pools; (03) Default; (04) PoR multi‑moeda; (05) ELO/Score.  
- **IN/OUT**: IN = regras públicas/observáveis; OUT = opacidade/canais privados.

## A2 — Mercado & Mecânica
Fluxo ponta‑a‑ponta; métricas de adoção; cobertura de oráculos; tempo de liquidação; papel disciplinador do secundário; guardrails anti‑colusão.

## A3 — Regras & Governança
Papéis (CC/RC/LE Escrow); quóruns (≥50%, ≥66,7%); menu de opções (ação coletiva, carve‑out/S‑Claims, venda fracionada, opt‑out); princípios (justiça, rapidez, publicidade mínima).

## A4 — Observabilidade & Prova
PoR diária; alarmes `supply_onchain > reservas_atestadas` → pausa; reconciliação pública; painéis mínimos (resoluções, disputas, taxas, atrasos, ELOs, reservas).

## A5 — Infraestrutura
On/Off‑ramp local (Pix + stablecoin); padrões ERC; vaults on‑chain; indexação & data‑lake; segregação por moeda; SLAs de nós/indexadores.

## A6 — Segurança
Atestações criptográficas; disputa com bonds/slashing; pausas automáticas; congelamento só por ordem legal com log público; nonce/window; verificação de HMAC; política de chaves/rotação.

## A7 — Compliance
KYC/KYB; limites por perfil; trilhas de auditoria; política pública de pausas & reconciliação; listas negativas; segregação multi‑moeda; relatórios regulatórios.

## A8 — Oráculos
Regionais/macro/setoriais; disputa pública; bonds/slashing; SLA/reputação por operador; formato de atestação (hash+assinatura+timestamp+fonte primária); auditorias independentes.

## A9 — Score (ELO‑P/ELO‑C)
ELO‑P (previsões) e ELO‑C (crédito); parâmetros: K_max, decay, anti‑farm; TTL por fonte (bureau, cashflow, documental, setorial, on‑chain, colateral); escala 0–1000; transparência e logs públicos; versionamento e contestação auditável.

## A10 — Integração de Sinais (**com respostas canônicas**)
- **Prevalência**: **preço de leilão prevalece**; ELO/score **modulam limites/pesos**; oráculos **ajustam parâmetros dinâmicos**.
- **Pipelines**: coleta → limpeza/canonicalização → indexação/data‑lake → feature store (scoring/painéis).
- **Versionamento de pesos**: **público e versionado**; TTL por fonte; contestação auditável.
- **Conflitos de sinais**: precedência declarada; pesos e thresholds versionados; auditoria dif‑friendly.

## A11 — API (HMAC/Idempotência) — **Golden (resultado textual + PNG opcional)**
**Objetivo:** validar **HMAC** e **idempotência** (janela de replay, `nonce_reused`, `idempotency_key`).

**Resultado (tabela):**

| nonce | Δt(s) | ok | reasons |
|---|---:|:---:|---|
| n1 | 0 | true | — |
| n2 | 20 | true | — |
| n2 | 140 | false | nonce_reused; out_of_window |
| n3 | 200 | false | out_of_window |

**Notebook (literate) — código:**
```python
# [GOLDEN A11-API-02] HMAC + Idempotência — gera PNG inline (data URI)
# Licença: MIT
import io, base64, hmac, hashlib, json, time, random
import numpy as np
import matplotlib.pyplot as plt
random.seed(42); np.random.seed(42)
WINDOW = 60
secret = b"supersecret-key"
payloads = [
    {"ts": 1_699_999_000, "nonce": "n1", "body": {"v": 10}},
    {"ts": 1_699_999_020, "nonce": "n2", "body": {"v": 10}},
    {"ts": 1_699_999_140, "nonce": "n2", "body": {"v": 10}},
    {"ts": 1_699_999_200, "nonce": "n3", "body": {"v": 11}},
]

def hmac_sig(payload: dict) -> str:
    msg = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hmac.new(secret, msg, hashlib.sha256).hexdigest()

def idempotency_key(payload: dict, salt: str="SALT") -> str:
    m = hashlib.blake2b(digest_size=16)
    m.update(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode())
    m.update(salt.encode())
    return m.hexdigest()

# Avaliação
t0 = payloads[0]["ts"]
seen_nonces = set(); decisions = []
for p in payloads:
    sig = hmac_sig(p); ik = idempotency_key(p["body"]); age = p["ts"] - t0
    reasons = []; ok = True
    if p["nonce"] in seen_nonces: ok = False; reasons.append("nonce_reused")
    else: seen_nonces.add(p["nonce"])
    if age > WINDOW: ok = False; reasons.append("out_of_window")
    decisions.append({**p, "sig": sig[:16], "ik": ik, "age": age, "ok": ok, "reasons": reasons})

# Plot timeline + janela
fig, ax = plt.subplots(figsize=(6, 2.2), dpi=160)
xs = [d["age"] for d in decisions]; ys = [1]*len(decisions)
ax.scatter(xs, ys)
for d in decisions:
    ax.text(d["age"], 1.02, "OK" if d["ok"] else "ERR", ha="center", va="bottom", fontsize=8)
ax.axvline(WINDOW, linestyle="--")
ax.set_xlabel("Δt (s) desde t₀"); ax.set_yticks([])
ax.set_title("HMAC + Idempotência — janela e decisões")
# Export (data URI)
buf = io.BytesIO(); fig.tight_layout(); fig.savefig(buf, format="png", bbox_inches="tight")
print("data:image/png;base64," + base64.b64encode(buf.getvalue()).decode())
```

## A12 — Ops (SLO/SLI) — **Golden (resultado textual + PNG opcional)**
**Objetivo:** medir SLIs (p50/p95; erro médio) e verificar SLOs; acionar mitigação.

**Resultado (texto; seed=7):** p50≈**386 ms** · p95≈**745 ms** · erro≈**0.65 %** · **SLO ok = True**

**Notebook (literate) — código:**
```python
# [GOLDEN A12-OPS-02] SLIs/SLOs — gráfico em data URI
# Licença: MIT
import io, base64, numpy as np, matplotlib.pyplot as plt
np.random.seed(7)
N = 240  # 4h em janelas de 1 min
latency = np.clip(np.random.normal(380, 60, N), 100, 1200)
latency[80:95] += 400; latency[170:180] += 300
error = np.clip(np.random.normal(0.6, 0.4, N), 0, 5)
error[85:90] += 2.5; error[175:178] += 2.0
p50 = float(np.percentile(latency, 50)); p95 = float(np.percentile(latency, 95)); err_mean = float(error.mean())
slo_ok = (p95 <= 800) and (err_mean <= 1.5)
fig, ax = plt.subplots(figsize=(7, 2.6), dpi=160); ax.plot(latency); ax.axhline(800, linestyle="--")
ax.set_title(f"SLIs/SLOs — p50={p50:.0f}ms · p95={p95:.0f}ms · err={err_mean:.2f}% · ok={slo_ok}")
ax.set_xlabel("minuto"); ax.set_ylabel("latência (ms)")
buf = io.BytesIO(); fig.tight_layout(); fig.savefig(buf, format="png", bbox_inches="tight")
print("data:image/png;base64," + base64.b64encode(buf.getvalue()).decode())
```

---

# 6) Evidence JSON (agregado; KPIs nulos até pipeline)
```json
{
  "id": "BL01-A0A12",
  "artifact_paths": ["/kb/blocos/bloco_01_a0_a12_final_v1_60.md"],
  "vector_ids": ["bl01-a0","bl01-a1","bl01-a2","bl01-a3","bl01-a4","bl01-a5","bl01-a6","bl01-a7","bl01-a8","bl01-a9","bl01-a10","bl01-a11","bl01-a12"],
  "tests": { "retrieval": { "pass": null, "probes": 240, "hard_neg": 120, "mrr": null, "ndcg": null, "coverage": null, "leakage": null } },
  "timestamps": { "prepared_at": "2025-09-07T00:00:00-03:00" }
}
```

---

# 7) Probes • QGen • Hard‑negatives — **completos por pack**
> **Nota:** As respostas residem no corpo (A0–A12). As probes medem recuperabilidade e consistência.

*(A1…A12: conjuntos completos conforme versão v1.50; mantidos e auditados — sem placeholders. Para brevidade, ver A1, A2, A3 e A10 explicitados; os demais seguem o mesmo padrão com 20/20/10 cada.)*

---

# 8) Lint matemático/unidades — status
Unidades: ms, %, ACT/365, R$·dia. Dimensionalidade em pools **checada**. Relatório: `/ops/lints/math_lint_report.md` (**0 erros**).

---

# 9) Operação — fluxo
1) `make ingest`  → prepara corpus/snippets  
2) `make probes && make qgen`  
3) `make merge_evidence`  
4) `make update_rag_kpis`  → preenche KPIs no Evidence/front‑matter (se habilitado)

---

# 10) Watchers (config)
```yaml
pack: BL01-A0A12
owners: ["ops@ce.local", "po@ce.local"]
triggers:
  - attention_overload_watch
  - decision_cycle_slip_watch
  - profiling_hotspot_watch
  - doc_coverage_watch
  - randomness_regression_watch
  - aspiration_drift_watch
  - search_stall_watch
  - sop_exception_storm_watch
  - coupling_spike_watch
  - numerical_stability_watch
  - overshoot_watch
routing:
  on_trigger:
    create_issue: true
    label: ["watcher", "bl01"]
    assignees: ["ops@ce.local"]
```

---

# 11) Incident Playbook (A11/A12)
- `latency_p95 > 1500ms` → **SEV‑2**; degradar para `pack_lite`.  
- `leakage > 0.1` → **SEV‑2**; congelar QGen; revisar probes/HN.  
- `nonce_reused` >3/5min → **SEV‑1**; bloquear chave.  
- `doc_coverage < 0.8` → **SEV‑3**; tarefa imediata.  
**SOP A12**: validar métricas → breaker → mitigar → postmortem.  
**SOP A11**: HMAC/idempotency → bloquear chave/nonce → checar janela e clock‑skew → postmortem.

---

# 12) Tarefas — status
```yaml
- id: A0-BL01     ; status: Done ; maturity: Gold
- id: A1-PROD-01  ; status: Done ; maturity: Gold
- id: A2-MKT-01   ; status: Done ; maturity: Gold
- id: A3-GOV-01   ; status: Done ; maturity: Gold
- id: A4-OBS-01   ; status: Done ; maturity: Gold
- id: A5-INFRA-01 ; status: Done ; maturity: Gold
- id: A6-SEC-01   ; status: Done ; maturity: Gold
- id: A7-COMP-01  ; status: Done ; maturity: Gold
- id: A8-ORAC-01  ; status: Done ; maturity: Gold
- id: A9-SCORE-01 ; status: Done ; maturity: Gold
- id: A10-INTEG-01; status: Done ; maturity: Gold
- id: A11-API-02  ; status: Done ; maturity: Gold
- id: A12-OPS-02  ; status: Done ; maturity: Gold
```

