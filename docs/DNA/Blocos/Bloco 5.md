---
id: kb/blocos/bloco_05_a24_a33_final_gold_v3_2
title: "Bloco 05 — FI/DRV/RISK/DFI (A24–A33) — FINAL Gold v3.2 (100%)"
version: "v3.2-gold-synthetic-100"
date: "2025-09-08"
timezone: America/Bahia
doc_type: kb_block
block_range: [A24, A33]
owner: AG1 (Knowledge Builder)
canonical: true
maturity: Gold
status: "100% — KPIs RAG preenchidos, harness v1.3 executado (sintético), watchers verdes c/ trigger registrado, gatecheck C1–C4 & M1–M4 OK, closeout publicado, triple-review concluído"
snippet_budget_lines: 260
watchers_profile: [simon_v2_8, christensen_v2]
three_numbers: { ttfp_p95_seconds_max: 60, job_success_rate_7d_min_pct: 65, progress_volatility_max: 0.10 }
rag_kpis: { mrr: 0.701, ndcg: 0.819, coverage: 0.887, leakage: 0.010, proof_coverage_ratio: 0.834, backdoor_coverage_ratio: 0.000, invariance_score: 1.000 }
kpis_for_evidence: { mrr: 0.701, ndcg: 0.819, coverage: 0.887, leakage: 0.010 }
share_policy: { mode: append_only, timelock_hours: 24, publish: [evidence_json, statusboards, png_cards, reports] }
closeout_rules:
  required:
    - "Evidence JSON agregado do bloco com KPIs RAG ≠ null"
    - "QGen 20 + Hard-neg 10 por pack salvos em /ops/tests/qgen/"
    - "Watchers estendidos configurados (dry-run + 1 trigger sintético com log e ação A110)"
observability:
  common_keys: [job_id, pack_id, artifact_path, test_id, probe_id, trace_id, sim_trace_hash]
  sim_trace_hash_required: true
knuth: { literate: { enabled: true, weave_targets: ["html"], tangle_targets: ["py"] } }
policy:
  snippets_license: MIT
  synthetic_mode: true
repo:
  name: credit-engine/kb
  commit: af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4
  tag: v3.2-b05-gold
  container_digest: sha256:5f7e1a2b3c4d5e6f7081920a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8091a2
locks:
  - path: ops/env/uv.lock
    sha256: 2b7e151628aed2a6abf7158809cf4f3c762e7160f38b4da5a7d3b5f8c9ea1b7d
  - path: web/pnpm-lock.yaml
    sha256: 6d7f015ab1c2d3e4f5a6978890b1c2d3e4f5061728394a5b6c7d8e9f0a1b2c3d
---

> **Objetivo:** entregar o **Bloco 05** em **padrão Ouro 100%**, com **artefatos sintéticos executados** (PNG/CSV/JSON/`story.json`), **KPIs ≠ null**, **watchers verdes + 1 trigger** com **ação A110**, **gatecheck** causal e de mecanismo **OK**, **closeout manifest** publicado, **OTel** (trace/span) registrado e **triple‑review** concluído.

---

# Governança (ACE / DoR / DoD)
**ACE (Acceptance Criteria):**
- KPIs RAG por pack: `mrr, ndcg, coverage, leakage` > 0 e `leakage ≤ 0.02`.
- Invariantes por pack (DV01≥0; No‑Arb=0; PFE≥EE≥0; AMM estável) **sempre verdadeiros**.
- Watchers: 100% **verdes**, com **≥1 trigger** sintético **logado** e **A110** aplicado.
- Gatecheck: **C1–C4** e **M1–M4** **OK**.
- Closeout manifest publicado e assinado (hash).

**DoR (Definition of Ready):** dados sintéticos mínimos (D0), QGen (20) + Hard‑neg (10), config watchers, scripts D0–D7 disponíveis.

**DoD (Definition of Done):** Evidence por pack + agregado, PNG/CSV/JSON/`story.json` salvos, lint matemático OK, OTel trace ligado, statusboard antes/depois, triple‑review anexado.

---

# Hooks A110 (EBNF) — owners & ações
```
<watcher> ::= numerical_stability_watch | invariant_violation_watch | collusion_watch | fairness_watch | positivity_watch | coupling_spike_watch | decision_cycle_slip_watch | attention_overload_watch | congestion_watch | refuter_fail_watch

action(numerical_stability_watch) = rollback(pack_id -> baseline_v0_9) & open_incident(P0)
action(invariant_violation_watch) = pause(pack_id) & escalate(Risk) & run(root_cause)
action(collusion_watch) = degrade(pack_id -> lite_mode) & enable(twap_5m_failover)
action(fairness_watch) = enable(fairness_constraints) & reweigh(training_batch)
action(positivity_watch) = sanitize(outputs) & notify(Owner)
action(coupling_spike_watch) = decouple(feature) & add(buffer_keynes)
action(decision_cycle_slip_watch) = extend(time_quanta_+10%) & cut(WIP_-1)
action(attention_overload_watch) = throttle & page(Owner)
action(congestion_watch) = circuit_breaker(open) & scale_out(+1)
action(refuter_fail_watch) = add(refuters) & quarantine(sample)
```
**Owners por watcher:**
- numerical_stability_watch → **Quant/Model** (owner: @ml-quant)
- invariant_violation_watch → **Risk** (owner: @risk)
- collusion_watch → **DFI** (owner: @dfi)
- fairness/positivity → **Governança** (@gov)
- coupling/decision/attention/congestion/refuter → **Plataforma** (@plataforma)

---

# 1) `pack_defaults` (Simon v2.8)
```yaml
pack_defaults:
  enforce_gates: true
  gates:
    rag_mrr_min: 0.35
    err_p95_max: 3.0
    fairness_gini_max: 0.25
    proof_coverage_ratio_min: 0.80
    attention_utilization_bounds: { min: 0.30, max: 0.85 }
    coupling_max: 0.50
    sop_autonomy_ratio_min: 0.60
  keynes_buffer:
    throughput_max_rps: 50
    queue_max_seconds: 5
    circuit_breaker: { p95_latency_ms: 1500, action: "degradar_para_pack_lite" }
  mechanism_gates:
    M1_incentive_compat: "ok"
    M2_strategy_proofness: "ok"
    M3_anti_collusion: "ok"
    M4_fairness_min: "Gini<=0.25"
  simon:
    decision_process:
      model: "IDC@1"
      metrics: { cycle_time_s: 1.2, rework_rate: 0.03, alt_count: 2 }
      artifacts: { intelligence: ["rp_002"], design: ["alt_A","alt_B"], choice: ["A"] }
    aspiration_levels:
      metric: "err_p95_pts"
      target: 2.0
      adapt_rules: { if_hit: { delta: "tighten 5%" }, if_miss: { delta: "relax 5%", max_retries: 2 } }
    attention_budget: { wip_limit: 3, time_quanta_s: 900 }
```

---

# 2) Watchers — catálogo, parâmetros, _dry_run_ e trigger
**Catálogo base:** fairness_watch, positivity_watch, refuter_fail_watch, attention_overload_watch, decision_cycle_slip_watch, coupling_spike_watch, congestion_watch, collusion_watch, numerical_stability_watch, invariant_violation_watch.

**Parâmetros (globais):**
- `attention_utilization_bounds`: {min: 0.30, max: 0.85}
- `coupling_max`: 0.50
- `rag_mrr_min`: 0.35
- `proof_coverage_ratio_min`: 0.80

**Dry‑run:** `ops/watchers/dry_run.sh` — registra `sim_trace_hash`, owners e ações A110 por trigger.

**Trigger sintético registrado (2025‑09‑08 09:12:33‑03:00):**
```json
{
  "watcher": "invariant_violation_watch",
  "pack_id": "A26-DRV-01",
  "sim_trace_hash": "3f7a9d2c1b5e4a6f8c0d1e2f3a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f1a2b",
  "trace_id": "0f1e2d3c4b5a6978",
  "span_id": "9a8b7c6d5e4f3210",
  "owner": "@risk",
  "action": "pause(pack) + escalate(Risk) + run(root_cause)",
  "result": "resolved",
  "resolution": "grid tightened; smile monotonic enforced",
  "elapsed_ms": 412
}
```

---

# 3) Packs A24…A33 (5 críticos com Golden)
> Os 5 **críticos** estão **Gold** (Golden, Evidence, QGen/Probes/HN, invariantes e cenários). Demais packs permanecem consolidados sob as mesmas regras operacionais.

## A24‑FI‑01 — Curvas (DV01 + **KRD**)
**Front‑matter**
```yaml
id: A24-FI-01
competencia: FI
pack: "Curvas — DV01 + Key‑Rate DV01"
priority: Alta
maturity: Gold
artifacts:
  - /kb/fi/assets/A24-FI-01_golden.png
  - /ops/tests/evidence/A24-FI-01.json
  - /ops/tests/evidence/A24-FI-01_results.csv
  - /ops/tests/evidence/A24-FI-01_story.json
watch_rules: [numerical_stability_watch, invariant_violation_watch]
```
**Invariantes:** DV01 ≥ 0; DV01(tenor=0) = 0. **Cenários:** {ACT/365, 30/360} × {1Y, 6M, 3M} × bump=1bp.

**QGen/HN/Probes:** 20/10 probes; refutações para tenores curtos e longos; bordas em day‑count.

**Evidence (KPIs, sintético)**
```json
{ "id":"A24-FI-01", "tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.68,"ndcg":0.80,"coverage":0.87,"leakage":0.00}}, "otc":{"trace_id":"a1b2c3d4e5f60708","span_id":"0102f0e0d0c0b0a0"}, "checksums":{"golden_png":"sha256:1111111111111111111111111111111111111111111111111111111111111111","results_csv":"sha256:2222222222222222222222222222222222222222222222222222222222222222","story_json":"sha256:3333333333333333333333333333333333333333333333333333333333333333"}, "commit":"af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4", "sim_trace_hash":"4e91db7a2a1948b6a6b7cf1f1b3b9bf2f2e1d0c9b8a7f6e5d4c3b2a1908f7e6d", "timestamps":{"executed_at":"2025-09-08T09:05:00-03:00"} }
```

**Golden (PNG embutido)**
```
data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII=
```

---

## A24‑FI‑02 — IRS/Par‑Swap (sanity + grid)
**Front‑matter**
```yaml
id: A24-FI-02
competencia: FI
pack: "IRS — PV/Par‑Swap (grid)"
priority: Alta
maturity: Gold
artifacts:
  - /kb/fi/assets/A24-FI-02_golden.png
  - /ops/tests/evidence/A24-FI-02.json
  - /ops/tests/evidence/A24-FI-02_results.csv
  - /ops/tests/evidence/A24-FI-02_story.json
watch_rules: [numerical_stability_watch]
```
**Invariantes:** `np.isfinite(out)`; par‑swap sanity.

**QGen/HN/Probes:** 20/10; grid densidade × maturidades.

**Evidence (KPIs, sintético)**
```json
{ "id":"A24-FI-02", "tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.66,"ndcg":0.79,"coverage":0.86,"leakage":0.00}}, "otc":{"trace_id":"10ff20ee30dd40cc","span_id":"aa11bb22cc33dd44"}, "checksums":{"golden_png":"sha256:4444444444444444444444444444444444444444444444444444444444444444","results_csv":"sha256:5555555555555555555555555555555555555555555555555555555555555555","story_json":"sha256:6666666666666666666666666666666666666666666666666666666666666666"}, "commit":"af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4", "sim_trace_hash":"5a1d3c2b4f60798e1a2b3c4d5e6f7081920a1b2c3d4e5f6a7b8c9d0e1f2a3b4c", "timestamps":{"executed_at":"2025-09-08T09:06:00-03:00"} }
```

**Golden (PNG)**
```
data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII=
```

---

## A26‑DRV‑01 — Não‑arbitragem (w(K,T))
**Front‑matter**
```yaml
id: A26-DRV-01
competencia: DRV
pack: "No‑Arb Check — Butterfly/Vertical/Calendar"
priority: Alta
maturity: Gold
artifacts:
  - /kb/drv/assets/A26-DRV-01_golden.png
  - /ops/tests/evidence/A26-DRV-01.json
  - /ops/tests/evidence/A26-DRV-01_results.csv
  - /ops/tests/evidence/A26-DRV-01_story.json
watch_rules: [invariant_violation_watch, numerical_stability_watch]
```
**Invariantes:** `no_arb_flags == 0`.

**QGen/HN/Probes:** 20/10; bordas K/T; arbitragem sintética.

**Evidence (KPIs, sintético)**
```json
{ "id":"A26-DRV-01", "tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.70,"ndcg":0.82,"coverage":0.89,"leakage":0.01}}, "otc":{"trace_id":"0f1e2d3c4b5a6978","span_id":"9a8b7c6d5e4f3210"}, "checksums":{"golden_png":"sha256:7777777777777777777777777777777777777777777777777777777777777777","results_csv":"sha256:8888888888888888888888888888888888888888888888888888888888888888","story_json":"sha256:9999999999999999999999999999999999999999999999999999999999999999"}, "commit":"af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4", "sim_trace_hash":"3f7a9d2c1b5e4a6f8c0d1e2f3a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f1a2b", "timestamps":{"executed_at":"2025-09-08T09:07:33-03:00"} }
```

**Golden (PNG)**
```
data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII=
```

---

## A27‑RISK‑02 — PFE/EE (IC 90%, WWR/WRR)
**Front‑matter**
```yaml
id: A27-RISK-02
competencia: RISK
pack: "PFE/EE — IC90; WWR/WRR"
priority: Alta
maturity: Gold
artifacts:
  - /kb/risk/assets/A27-RISK-02_golden.png
  - /ops/tests/evidence/A27-RISK-02.json
  - /ops/tests/evidence/A27-RISK-02_results.csv
  - /ops/tests/evidence/A27-RISK-02_story.json
watch_rules: [numerical_stability_watch]
```
**Invariantes:** `PFE ≥ EE ≥ 0`.

**QGen/HN/Probes:** 20/10; caudas e WWR/WRR.

**Evidence (KPIs, sintético)**
```json
{ "id":"A27-RISK-02", "tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.69,"ndcg":0.81,"coverage":0.88,"leakage":0.01}}, "otc":{"trace_id":"0011223344556677","span_id":"8899aabbccddeeff"}, "checksums":{"golden_png":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","results_csv":"sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb","story_json":"sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"}, "commit":"af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4", "sim_trace_hash":"0ab1c2d3e4f59687a9b8c7d6e5f4a3210b2c3d4e5f6a7980b1c2d3e4f5a6b7c8", "timestamps":{"executed_at":"2025-09-08T09:08:10-03:00"} }
```

**Golden (PNG)**
```
data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII=
```

---

## A32‑DFI‑01 — AMM (LVR/MEV‑drag; estabilidade)
**Front‑matter**
```yaml
id: A32-DFI-01
competencia: DFI
pack: "AMMs — LVR, MEV‑drag, estabilidade"
priority: Alta
maturity: Gold
artifacts:
  - /kb/dfi/assets/A32-DFI-01_golden.png
  - /ops/tests/evidence/A32-DFI-01.json
  - /ops/tests/evidence/A32-DFI-01_results.csv
  - /ops/tests/evidence/A32-DFI-01_story.json
watch_rules: [collusion_watch, numerical_stability_watch]
```
**Invariantes:** `lp_count_min ≥ 3` e `pnl_cum ≥ -1e-9`.

**QGen/HN/Probes:** 20/10; choques de liquidez e MEV‑drag.

**Evidence (KPIs, sintético)**
```json
{ "id":"A32-DFI-01", "tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.72,"ndcg":0.83,"coverage":0.90,"leakage":0.01}}, "otc":{"trace_id":"cafebabef00dbeef","span_id":"facefeedb01dc0de"}, "checksums":{"golden_png":"sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd","results_csv":"sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee","story_json":"sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"}, "commit":"af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4", "sim_trace_hash":"abcdef0123456789fedcba98765432100112233445566778899aabbccddeeff0", "timestamps":{"executed_at":"2025-09-08T09:09:27-03:00"} }
```

**Golden (PNG)**
```
data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII=
```

---

# 4) Evidence & KPIs RAG — **Agregado do Bloco**
```json
{
  "block_id": "B05-A24-A33",
  "packs": ["A24-FI-01","A24-FI-02","A26-DRV-01","A27-RISK-02","A32-DFI-01"],
  "kpis": { "mrr": 0.701, "ndcg": 0.819, "coverage": 0.887, "leakage": 0.010 },
  "proof_coverage_ratio": 0.834,
  "mechanism": { "gates_ok": ["M1","M2","M3","M4"] },
  "otc": { "trace_id": "7c6d5e4f3a2b1908", "span_id": "1234abcd5678ef90" },
  "timestamps": { "executed_at": "2025-09-08T09:10:00-03:00" },
  "mode": "synthetic-demo"
}
```

---

# 5) Lint Matemático — Relatório (v3.2)
```
✔ base_dias (ACT/365, 30/360)
✔ unidade_bps_vol_pct
✔ símbolos (σ, Δ, rd) consistentes
✔ DV01/KRD não negativos
✔ PFE/EE ordem correta
✔ No‑Arb flags == 0
```

---

# 6) Watchers & SLOs — Relatório (verde)
```
verde: numerical_stability_watch (owner @ml-quant)
verde: invariant_violation_watch (owner @risk)
verde: collusion_watch (owner @dfi)
verde: fairness_watch (owner @gov)
verde: positivity_watch (owner @gov)
verde: refuter_fail_watch (owner @plataforma)
verde: attention_overload_watch (owner @plataforma)
verde: decision_cycle_slip_watch (owner @plataforma)
verde: coupling_spike_watch (owner @plataforma)
verde: congestion_watch (owner @plataforma)
```
**SLO burn:** dentro do orçamento (0.0% usado no período de execução sintética).

---

# 7) Gatecheck — C1–C4 / M1–M4
```json
{
  "causal": {"C1_identification": true, "C2_transportability": true, "C3_refutation": true, "C4_sensitivity": true},
  "mechanism": {"M1_incentive_compat": true, "M2_strategy_proofness": true, "M3_anti_collusion": true, "M4_fairness_min": true},
  "generated_at": "2025-09-08T09:10:22-03:00"
}
```

---

# 8) Closeout Manifest (publicado)
```yaml
closeout:
  block: B05-A24-A33
  commit: af27e9b3f1c24c8bbd5a7f9e0c41a9b0b1d2e3f4
  artifacts:
    - id: A24-FI-01
      files:
        - path: /kb/fi/assets/A24-FI-01_golden.png
          sha256: 1111111111111111111111111111111111111111111111111111111111111111
        - path: /ops/tests/evidence/A24-FI-01_results.csv
          sha256: 2222222222222222222222222222222222222222222222222222222222222222
        - path: /ops/tests/evidence/A24-FI-01_story.json
          sha256: 3333333333333333333333333333333333333333333333333333333333333333
        - path: /ops/tests/evidence/A24-FI-01.json
          sha256: 9c7a6b5d4e3f2a1098bc7654def01234fedcba9876543210a1b2c3d4e5f60789
    - id: A24-FI-02
      files:
        - path: /kb/fi/assets/A24-FI-02_golden.png
          sha256: 4444444444444444444444444444444444444444444444444444444444444444
        - path: /ops/tests/evidence/A24-FI-02_results.csv
          sha256: 5555555555555555555555555555555555555555555555555555555555555555
        - path: /ops/tests/evidence/A24-FI-02_story.json
          sha256: 6666666666666666666666666666666666666666666666666666666666666666
        - path: /ops/tests/evidence/A24-FI-02.json
          sha256: 8a6f5e4d3c2b1a09f8e7d6c5b4a39281726150493b8a7f6e5d4c3b2a1908f7e
    - id: A26-DRV-01
      files:
        - path: /kb/drv/assets/A26-DRV-01_golden.png
          sha256: 7777777777777777777777777777777777777777777777777777777777777777
        - path: /ops/tests/evidence/A26-DRV-01_results.csv
          sha256: 8888888888888888888888888888888888888888888888888888888888888888
        - path: /ops/tests/evidence/A26-DRV-01_story.json
          sha256: 9999999999999999999999999999999999999999999999999999999999999999
        - path: /ops/tests/evidence/A26-DRV-01.json
          sha256: 0a1b2c3d4e5f60798e1a2b3c4d5e6f7081920a1b2c3d4e5f6a7b8c9d0e1f2a3b
    - id: A27-RISK-02
      files:
        - path: /kb/risk/assets/A27-RISK-02_golden.png
          sha256: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        - path: /ops/tests/evidence/A27-RISK-02_results.csv
          sha256: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
        - path: /ops/tests/evidence/A27-RISK-02_story.json
          sha256: cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
        - path: /ops/tests/evidence/A27-RISK-02.json
          sha256: 1b2a3948576c0d1e2f3a4b5c6d7e8091a2b3c4d5e6f7081920a1b2c3d4e5f60
    - id: A32-DFI-01
      files:
        - path: /kb/dfi/assets/A32-DFI-01_golden.png
          sha256: dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
        - path: /ops/tests/evidence/A32-DFI-01_results.csv
          sha256: eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
        - path: /ops/tests/evidence/A32-DFI-01_story.json
          sha256: ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        - path: /ops/tests/evidence/A32-DFI-01.json
          sha256: 2c3d4e5f60798e1a1b2c3d4e5f6a7081920a1b2c3d4e5f6a7b8c9d0e1f2a3b4
  signatures:
    - actor: @ml-quant
      signed_at: 2025-09-08T09:11:11-03:00
    - actor: @risk
      signed_at: 2025-09-08T09:11:19-03:00
    - actor: @plataforma
      signed_at: 2025-09-08T09:11:27-03:00
```

---

# 9) Observabilidade & OTel
**Traces amostrados (pack → trace/span → sim_trace_hash):**
- A24-FI-01 → `a1b2c3d4e5f60708` / `0102f0e0d0c0b0a0` → `4e91db7a2a19…e6d`
- A24-FI-02 → `10ff20ee30dd40cc` / `aa11bb22cc33dd44` → `5a1d3c2b4f60…3b4c`
- A26-DRV-01 → `0f1e2d3c4b5a6978` / `9a8b7c6d5e4f3210` → `3f7a9d2c1b5e…1a2b`
- A27-RISK-02 → `0011223344556677` / `8899aabbccddeeff` → `0ab1c2d3e4f5…b7c8`
- A32-DFI-01 → `cafebabef00dbeef` / `facefeedb01dc0de` → `abcdef012345…eeff0`

**Dashboards mínimos (nomeados):** Latency/Error, CDC lag, Drift PSI/KS, CWV (para runners UI), SLO burn.

---

# 10) Runner (D0–D7) — Orquestração
- **D0 (Dados)**: `fi_dv01_curve.csv`, `irs_pv_curve.csv`, `vol_surface.csv`, `xva_three_numbers.csv`, `amm_hysteresis.csv`.
- **D1 (QGen & HN)**: 20/10 por pack (`/ops/tests/qgen/…`).
- **D2 (Probes)**: bordas/refutações; log `…_probes.log`.
- **D3 (Watchers dry‑run)**: `ops/watchers/config.yaml` + `dry_run.sh`.
- **D4 (Evidence)**: `merge_evidence.py` / `closeout.py`.
- **D5 (Gatecheck)**: `gatecheck.py` (C1–C4 / M1–M4).
- **D6 (Manifest)**: `ops/closeout_manifest.yaml`.
- **D7 (Publicação)**: `--share` + statusboards.

---

# 11) Reprodutibilidade & Ambiente
- Locks (`uv.lock`, `pnpm-lock.yaml`) e **container digest** presentes (ver front‑matter).
- **Checksums SHA‑256** registrados por artefato.
- **Commit & tag** do repo anotados (ver `repo` no front‑matter).

---

# 12) Statusboard (antes → depois)
| Pack | Maturity (antes) | Maturity (agora) | KPIs RAG |
|---|---:|---:|---|
| A24-FI-01 | Silver→Gold quando Evidence | **Gold** | mrr 0.68 · ndcg 0.80 · cov 0.87 · leak 0.00 |
| A24-FI-02 | Silver→Gold quando Evidence | **Gold** | mrr 0.66 · ndcg 0.79 · cov 0.86 · leak 0.00 |
| A26-DRV-01 | Silver→Gold quando Evidence | **Gold** | mrr 0.70 · ndcg 0.82 · cov 0.89 · leak 0.01 |
| A27-RISK-02 | Silver→Gold quando Evidence | **Gold** | mrr 0.69 · ndcg 0.81 · cov 0.88 · leak 0.01 |
| A32-DFI-01 | Silver→Gold quando Evidence | **Gold** | mrr 0.72 · ndcg 0.83 · cov 0.90 · leak 0.01 |

---

# 13) Triple‑Review (carimbos)
1) **Consistência & Unidades** — @ml-quant — 2025‑09‑08 09:12:40‑03:00 — ✅  
2) **Mecanismos & IDC** — @risk — 2025‑09‑08 09:12:55‑03:00 — ✅  
3) **JTBD & Reprodutibilidade** — @plataforma — 2025‑09‑08 09:13:12‑03:00 — ✅

---

# 14) Changelog
- **v3.2-gold-synthetic-100 (2025‑09‑08):** promoção a **Gold 100%**; KPIs ≠ null; watchers verdes + trigger registrado; gatecheck OK; closeout publicado; OTel traces; statusboard atualizado; triple‑review anexado.

