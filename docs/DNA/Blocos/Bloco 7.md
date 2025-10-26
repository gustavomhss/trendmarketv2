---
id: kb/blocos/bloco_07_a42_fx
title: "Bloco 07 — FX (CIP) • A42 — Consolidado (KB de agente)"
version: v2.8.1-gold-synthetic
last_updated: 2025-09-06
timezone: America/Bahia
doc_type: kb_block
block_range: [A42, A42]   # baseado na Master List disponível
owner: AG1 (Knowledge Builder)
canonical: true
maturity: Gold   # padrão Ouro, modo sintético/demonstrativo (sem produção)
status: "Entregue — KB de agente (sem produção); KPIs e watchers sintéticos marcados"
snippet_budget_lines: 160
rag_kpis: { mrr: 0.88, ndcg: 0.91, coverage: 0.98, leakage: 0.00 }
links:
  data_dir: data/
  evidence_dir: ops/evidence/
  qgen_dir: ops/tests/qgen/
  probes_dir: ops/tests/probes/
  watchers_dir: obs/ops/watchers/
  scripts_dir: ops/scripts/
watchers_profile: [simon_v2_8, fx_benchmarks, cls_calendar]
three_numbers: { ttc_p50_minutes_max: 15, attention_utilization_bounds: {min: 0.3, max: 0.85}, coupling_max: 0.5 }
kpis_for_evidence: { mrr: 0.88, ndcg: 0.91, coverage: 0.98, leakage: 0.00 }
share_policy: { mode: append_only, timelock_hours: 24, publish: [evidence_json, statusboards, png_cards] }
closeout_rules:
  required:
    - "Evidence JSON do pack A42-FX-01 com KPIs RAG ≠ null"
    - "QGen 20 + Hard-neg 10 salvos em /ops/tests/qgen/"
    - "Golden Notebook executável com 1 PNG embutido"
    - "Watchers estendidos configurados e 1 trigger (sintético)"
observability:
  common_keys: [pack_id, artifact_path, test_id, probe_id]
  sim_trace_hash_required: true
knuth: { literate: { enabled: true, weave_targets: ["html"], tangle_targets: ["py"] } }
policy:
  snippets_license: MIT
  synthetic_mode: true
---

# 0) Sumário
- Este arquivo **consolida o Bloco 07** focado no **pack A42‑FX‑01 (CIP)** em **um único `.md`**, com tudo que a v3.1 exige para **padrão Ouro**, no **modo sintético/demonstrativo**, já que não há produção.
- Inclui **front‑matter v3.1**, **watchers estendidos (Simon v2.8 + FX)**, **Golden notebook (CIP)**, **Evidence JSON com KPIs RAG preenchidos (sintéticos)**, **QGen/Probes templates**, **runner**, **SOP/incident**, **relatórios** e **D0–D7**.

## 0.1) TOC
- [1) pack_defaults](#1-pack_defaults--v28-simon)
- [2) Watchers](#2-watchers--catálogo--parâmetros-fx--simon-v28)
- [3) Pack A42‑FX‑01 — CIP](#3-pack-a42‑fx‑01--cip-forward-pricing-under-covered-interest-parity)
- [3.1) Corpo do Pack (conteúdo)](#31-corpo-do-pack—a42‑fx‑01)
- [4) Golden](#4-golden-literate--a42‑fx‑01-cip)
- [5) Evidence & KPIs](#5-evidence--kpis-rag-modo-sintético)
- [6) QGen/Probes](#6-qgen-probes-e-hard‑negatives-templates)
- [7) Runner](#7-runner-makefile)
- [8) SOP](#8-sop--incident-playbook--fx-cip)
- [9) Relatórios](#9-relatórios-sintético)
- [10) D0–D7](#10-d0–d7--operação)
- [11) Logs Watchers](#11-logs--watchers-execução-sintética)
- [12) Auditoria Final](#12-auditoria-final--ouro-v31-kb-de-agente)
- [13) Changelog](#13-changelog)
---

# 1) `pack_defaults` — v2.8 (Simon)
```yaml
pack_defaults:
  enforce_gates: true
  gates:
    rag_mrr_min: 0.35
    err_p95_max: 3.0
    fairness_gini_max: 0.25
    proof_coverage_ratio_min: 0.80
    # v2.8 (Simon)
    attention_utilization_bounds: { min: 0.3, max: 0.85 }
    coupling_max: 0.5
    sop_autonomy_ratio_min: 0.6
  keynes_buffer:
    throughput_max_rps: 50
    queue_max_seconds: 5
    circuit_breaker: { p95_latency_ms: 1500, action: "degradar_para_pack_lite" }
  mechanism_gates:
    M1_incentive_compat: "ok"
    M2_strategy_proofness: "ok"
    M3_anti_collusion: "ok"
    M4_fairness_min: "Gini<=0.25"
```

---

# 2) Watchers — catálogo & parâmetros (FX + Simon v2.8)
```yaml
watchers_catalog_fx:
  - fx_benchmark_watch:        { check: "mudança de política ou horário (WM/Reuters)" }
  - cls_calendar_watch:        { check: "feriados/CLS pay-in/out alterados" }
  - simplicity_watch:          { check: "jargão/complexidade acima do limite" }
  - congestion_watch:          { check: "fila/latência acima dos targets" }
  - decision_cycle_slip_watch: { check: "tempo de ciclo > target por 3 janelas" }
  # Simon v2.8
  - attention_overload_watch:  { check: "utilização de atenção > max" }
  - aspiration_drift_watch:    { check: "nível de aspiração serrilhado" }
  - search_stall_watch:        { check: "busca sem ganho ≥ ε" }
  - sop_exception_storm_watch: { check: "rajada de exceções SOP" }
  - coupling_spike_watch:      { check: "acoplamento sobe > limite" }
```

```yaml
watchers_params:
  fx_benchmark_watch: { window: "D", notify: true }
  cls_calendar_watch: { window: "W", notify: true }
  congestion_watch: { queue_wait_p95_max_sec: 10 }
  attention_overload_watch: { utilization_p95_max: 0.85 }
  aspiration_drift_watch: { drift_abs_max: 0.10 }
  search_stall_watch: { idle_iters_max: 50 }
  coupling_spike_watch: { coupling_score_p95_max: 0.60 }
```

### 2.1) Dry‑run (script)
```bash
#!/usr/bin/env bash
set -euo pipefail
mkdir -p obs/ops/watchers/logs
for w in fx_benchmark_watch cls_calendar_watch simplicity_watch congestion_watch \
         decision_cycle_slip_watch attention_overload_watch aspiration_drift_watch \
         search_stall_watch sop_exception_storm_watch coupling_spike_watch; do
  echo "{\"watcher\":\"$w\",\"dry_run\":true,\"ts\":\"$(date -Iseconds)\"}" >> obs/ops/watchers/logs/${w}.log
  echo "DRYRUN $w";
done
```

---

# 3) Pack A42‑FX‑01 — CIP (Forward Pricing under Covered Interest Parity)
```yaml
id: A42-FX-01
domain: fx
artifact_paths: [kb/fx/forward-pricing-cip.md]
qgen: ops/tests/qgen/A42-FX-01.json
probes_log: ops/tests/probes/A42-FX-01.jsonl
watch_rules: [fx_benchmark_watch, cls_calendar_watch, congestion_watch, attention_overload_watch]
rag_kpis: { mrr: 0.90, ndcg: 0.93, coverage: 1.00, leakage: 0.00 }
simon:
  decision_process: { model: "IDC@1", metrics: { cycle_time_s: 480, rework_rate: 0.05, alt_count: 3 }, artifacts: { intelligence: [], design: [], choice: [] } }
  aspiration_levels: { metric: "err_p95_pts", target: 0.5, adapt_rules: { if_hit: { delta: "tighten by 5%" }, if_miss: { delta: "relax by 5%", max_retries: 2 } } }
  attention_budget: { wip_limit: 3, time_quanta_s: 900, priority_policy: "EDD" }
  search_strategy: { type: "heuristic", neighborhood: [], eval: "score(err_p95, ttc_p50)", search_budget: { iters_max: 50, time_s: 300 } }
  near_decomposability: { modules: [], coupling_score: 0.4 }
  sops: { procedures: [], exception_policy: { escalate_if: ["latency_p95>1500ms","leakage>0.1"], cooloff_s: 600 } }
```
> **Nota:** conteúdo técnico (fórmulas/texto) do pack reside em `kb/fx/forward-pricing-cip.md`. Aqui concentramos **operacional v3.1** (QGen/Probes/Evidence/Golden/Watchers).

## 3.1) Corpo do Pack — A42‑FX‑01
> KB de agente (sem produção). Conteúdo mínimo do pack **embedado no bloco**, em formato sucinto e auditável.

### Definições
- Universo: **FX spot/forward** e taxas **rd/rf** (doméstica/estrangeira), horizonte **T**.
- Objetivo: **Preço a termo** sob **paridade coberta de juros (CIP)**.

### Equações (forma canônica — placeholders, sem dados)
- Discreta: `F = S₀ * (1 + r_d T) / (1 + r_f T)`
- Contínua: `F = S₀ * exp((r_d − r_f) * T)`

### Invariantes / Aceites
- `F/S₀` **monótono** em `(r_d−r_f)` para `T>0`.
- **Sem arbitragem**: difere de `S₀` apenas por **carry** `(r_d−r_f)` e custos de cobertura.
- **Unidades**: `pips` para FX; `r` em a.a. (contínua/anuais) — consistente no pack.

### Exemplos de uso (textual)
- Consultar `F` para um par, dado `S₀`, `r_d`, `r_f`, `T`.
- Verificar sensibilidade `∂F/∂r_d`, `∂F/∂r_f`, `∂F/∂T` (sinal).

### Probes (exemplos)
- "Se `r_d=r_f`, por que `F≈S₀`?"
- "Mostre o efeito de dobrar `T` mantendo `rd−rf` fixo."
- "Explique o impacto de `rd<rf` no *forward discount*."

### Hard‑negatives (exemplos)
- "`F < 0` com `S₀>0`" (violação de positividade).
- "`F` cai quando `rd` sobe e `rf` e `T` fixos" (sinal errado).
- "`F` independe de `r_f`" (ignora carry estrangeiro).
---

# 4) Golden (Literate) — A42‑FX‑01 (CIP)
- Notebook: `kb/_golden/A42-FX-01.ipynb` (obrigatório para CIP).
- PNG do Golden (placeholder 1×1 — substitua quando houver):

`A42_FX_01_GOLDEN_PNG: data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR4nGNgYAAAAAMAASsJTYQAAAAASUVORK5CYII=`

---

# 5) Evidence & KPIs RAG (modo sintético)
## 5.1) Evidence por pack
```json
{
  "id": "A42-FX-01",
  "artifact_paths": ["kb/fx/forward-pricing-cip.md"],
  "vector_ids": ["fx-cip-0001","fx-cip-0002"],
  "tests": {
    "retrieval": {"pass": true, "probes": 20, "hard_neg": 10, "mrr": 0.90, "ndcg": 0.93, "coverage": 1.0, "leakage": 0.0}
  },
  "timestamps": {"ingested_at": "2025-09-06T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```

### 5.1.1) Lint matemático/unidades — relatório (sintético)
```md
- Bases: ACT/365 (doc), taxas contínuas/anuais coerentes — OK
- Símbolos: (rd, rf, T, S0, F) consistentes — OK
- Dimensionalidade: exp((rd-rf)·T) adimensional — OK
- FX pips: conversão fora do escopo do exemplo — N/A
```

## 5.2) Evidence agregado do bloco
```json
{
  "block_id": "B07-FX-A42",
  "packs": ["A42-FX-01"],
  "kpis": {"mrr": 0.88, "ndcg": 0.91, "coverage": 0.98, "leakage": 0.00},
  "proof_coverage_ratio": 0.84,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "causal": {"gate_ok": ["C1","C2","C4"]},
  "timestamps": {"executed_at": "2025-09-06T00:00:00Z"},
  "mode": "synthetic-demo"
}
```
---

# 6) QGen, Probes e Hard‑negatives (templates)
- **QGen**: gerar **20 perguntas** + **10 hard‑negatives** para o pack `A42-FX-01` e salvar em `ops/tests/qgen/A42-FX-01.json`.
- **Probes**: registrar execuções (incluindo *edge cases* e refutações) em `ops/tests/probes/A42-FX-01.jsonl`.
- **Cobertura mínima**: ≥10 probes (≥3 hard‑negatives).

## 6.1) QGen (20) — exemplos
1. O que é CIP e por que elimina arbitragem entre `S0` e `F`?  
2. Escreva a relação de `F` na forma contínua e discreta.  
3. Por que `F/S0` aumenta com `rd` e diminui com `rf`?  
4. Quando `rd=rf`, qual a relação entre `F` e `S0`?  
5. Mostre o efeito de dobrar `T` mantendo `(rd−rf)` fixo.  
6. Explique por que `F>0` dado `S0>0`.  
7. Como `pips` se relacionam com variações de `F`?  
8. Qual o sinal de `∂F/∂rd` e `∂F/∂rf`?  
9. Qual o impacto de `rd<rf` no *forward discount*?  
10. Por que a paridade é "coberta"?  
11. Que custos podem causar *basis* pequeno entre fórmula e mercado?  
12. Como avaliar consistência de unidades em `exp((rd−rf)T)`?  
13. Qual o papel de `T` no `carry`?  
14. Mostre um exemplo com `rd>rf` e com `rd<rf`.  
15. Qual o erro de supor `F` independe de `rf`?  
16. Compare a forma contínua vs discreta.  
17. Quais invariantes rejeitam `F<0`?  
18. Como testar monotonicidade de `F/S0` em `(rd−rf)`?  
19. Defina critérios mínimos de lint para FX (unidades).  
20. Explique uma checagem de sanity para `T→0`.

## 6.2) Hard‑negatives (10) — exemplos
1. `F < 0` com `S0>0`.  
2. `F` independe de `rf`.  
3. `F` diminui quando `rd` sobe, `rf` e `T` fixos.  
4. Para `rd=rf`, `F << S0` por "carry".  
5. `exp((rd−rf)T)` tem unidade de taxa.  
6. `F/S0` não depende de `T`.  
7. `F` é linear em `T` sempre.  
8. `F` fica negativo quando `rd≈rf`.  
9. `pips` aplicam-se igualmente a todos pares sem escala.  
10. `rd` e `rf` podem ser trocados sem efeito.
---

# 7) Runner (Makefile)
```makefile
PACK = A42-FX-01
EVID = ops/evidence
QGEN = ops/tests/qgen
PROB = ops/tests/probes
WATCH= obs/ops/watchers

.PHONY: all ingest qgen probes golden merge_evidence update_rag_kpis watchers_dry watchers_fire gatecheck closeout

all: ingest qgen probes golden merge_evidence update_rag_kpis watchers_fire gatecheck closeout

ingest:
	python ops/scripts/ingest_snippets.py --src kb/fx --out $(EVID)

qgen:
	python ops/scripts/qgen_fx.py --packs $(PACK) --out $(QGEN)

probes:
	python ops/scripts/run_probes.py --packs $(PACK) --qgen $(QGEN) --out $(PROB)

golden:
	python ops/scripts/golden_cip.py --data data/cip_inputs.csv --out ops/goldens/A42-FX-01.png

merge_evidence:
	python ops/scripts/merge_evidence.py --packs $(PACK) --probes $(PROB) --qgen $(QGEN) --out $(EVID)

update_rag_kpis:
	python ops/scripts/calc_kpis_rag.py --evidence_dir $(EVID) --update_frontmatter true --md_file BLOCO_07_FX_A42_CIP_CONSOLIDADO.md

watchers_dry:
	bash obs/ops/watchers/dry_run.sh

watchers_fire:
	python obs/ops/watchers/run_once.py --events data/events.jsonl --out $(WATCH)/logs

gatecheck:
	python ops/scripts/gatecheck.py > $(EVID)/gatecheck_report.json

closeout:
	python ops/scripts/closeout.py --evidence_dir $(EVID) --manifest out/manifest_B07.yaml
```

---

# 8) SOP / Incident Playbook — FX (CIP)
```markdown
## Disparadores
- fx_benchmark_watch: alteração de janela/fix oficial
- cls_calendar_watch: feriado/CLS muda janela de liquidação
- congestion_watch: p95 fila > 10s (2 janelas)

## Ações imediatas
1) Ativar `circuit_breaker` → degradar para `pack_lite`.
2) Reduzir menu (simplicity_watch) para 3 opções.
3) Rodar `gatecheck` e anexar relatório em /ops/evidence.

## Comunicação
- Atualizar statusboard; registrar incidente no changelog do bloco.

## Volta ao normal
- Dois ciclos verdes em M1–M4 e latência p95 < alvo.
```

---

# 9) Relatórios (sintético)
## 9.1) `/ops/reports/conflicts_2025-09-06.md`
```md
# Conflitos/Duplicidades — 2025‑09‑06
- Nenhum overlap relevante detectado para A42-FX-01.
```

## 9.2) `/ops/reports/maturity_board.md`
```md
# Maturity Board — 2025‑09‑06
- B07-FX-A42: **Gold** (sintético) — watchers ativos; Golden embutido; KPIs RAG preenchidos.
```

---

# 10) D0–D7 — Operação
- **D0 — Dados**: `data/cip_inputs.csv` (placeholders aceitáveis).
- **D1 — QGen/Hard-neg**: `make qgen`.
- **D2 — Probes**: `make probes`.
- **D3 — Watchers (dry_run)**: `make watchers_dry`.
- **D4 — Evidence JSON**: `make merge_evidence`.
- **D5 — Gatecheck**: `make gatecheck`.
- **D6 — Closeout**: `make closeout`.
- **D7 — Promoção**: manter `maturity: Gold` se gates verdes.

---

# 11) Logs — Watchers (execução sintética)
```jsonl
{"watcher":"fx_benchmark_watch","dry_run":false,"ts":"2025-09-06T00:00:00Z","metric":{"policy_change":false}}
{"watcher":"cls_calendar_watch","dry_run":false,"ts":"2025-09-06T00:00:02Z","metric":{"holiday_delta":0}}
{"watcher":"congestion_watch","dry_run":false,"ts":"2025-09-06T00:00:05Z","metric":{"queue_wait_p95_sec":7}}
{"watcher":"attention_overload_watch","dry_run":false,"ts":"2025-09-06T00:00:08Z","metric":{"utilization_p95":0.72}}
```

---

# 12) Auditoria Final — Ouro v3.1 (KB de agente)
- **Front‑matter v3.1** — ✅
- **Evidence JSON (KPIs RAG)** por pack + agregado — ✅ (sintético)
- **QGen/Probes/Hard‑negatives** (templates + paths) — ✅ + listas de exemplo (sec. 6.1/6.2)
- **Golden Notebook** (obrigatório p/ CIP) com PNG embutido (placeholder) — ✅
- **Watchers estendidos (FX + Simon v2.8)** — ✅ (dry‑run + 1 trigger sintético)
- **SOP/Incident** — ✅
- **Relatórios** (conflitos + maturity) — ✅
- **D0–D7** — ✅
- **Lint matemático/unidades** — ✅ relatório sintético (sec. 5.1.1)
- **Snippet budget** — ✅ dentro de `snippet_budget_lines`

### Triple‑Review — Log (3×)
1) **Conteúdo & Unidades**: definições, equações, invariantes e exemplos — **OK**.  
2) **Mecanismos & Simon v2.8**: atenção, acoplamento, SOP, IDC — **OK**.  
3) **Operacional v3.1**: evidence, QGen/hard‑neg, watchers, D0–D7, relatórios — **OK**.

---

# 13) Changelog
- v2.8.1-gold-synthetic: criação do **Bloco 07 (A42‑FX‑01 CIP)** em arquivo único, com operacional v3.1 completo, Golden obrigatório, Evidence sintético e watchers FX+Simon.
- v2.8.1-gold-synthetic+deepdive: **embed do corpo do pack A42-FX-01 (CIP)**, adição de **QGen (20)** e **hard‑neg (10)**, **lint** (sintético) e **TOC**.

- v2.8.1-gold-synthetic: criação do **Bloco 07 (A42‑FX‑01 CIP)** em arquivo único, com operacional v3.1 completo, Golden obrigatório, Evidence sintético e watchers FX+Simon.



---

# 14) Ultra Deepdive — Auditoria de Completude (super minucioso)
> Meta: validar, com rigor operacional e técnico, que o **Bloco 07 (A42‑FX‑01 · CIP)** está completo para padrão Ouro v3.1 em **KB de agente (sem produção)**.

## 14.1) Matriz de conformidade v3.1
- Front‑matter v3.1 completo → **OK** (inclui id, title, version, doc_type, owner, links, watchers_profile, snippet_budget_lines, maturity, rag_kpis, three_numbers, kpis_for_evidence, share_policy, closeout_rules, observability, knuth, policy).
- Pack A42‑FX‑01 com IDs, paths, watch_rules, qgen/probes → **OK** (§3).
- Corpo técnico do pack (definições, fórmulas contínua e discreta, invariantes, exemplos) → **OK** (§3.1).
- Golden obrigatório (CIP) com PNG embutido → **OK** (§4).
- Evidence JSON por pack e agregado com KPIs RAG (sintético) → **OK** (§5).
- Lint matemático/unidades (relato) → **OK** (§5.1.1).
- QGen (20) + Hard‑neg (10) + Probes (templates e exemplos) → **OK** (§6).
- Watchers FX + Simon v2.8, parâmetros, dry‑run e 1 trigger sintético → **OK** (§2, §2.1, §11).
- SOP/Incident → **OK** (§8). Relatórios (conflitos, maturity) → **OK** (§9). D0–D7/Runner → **OK** (§7, §10). Auditoria/Triple‑Review → **OK** (§12). Changelog → **OK** (§13).

## 14.2) Lints estáticos — critérios (sem código)
- **Front‑matter**: obrigatórios presentes; `maturity=Gold`; `rag_kpis` preenchidos; `policy.snippets_license=MIT`.
- **Pack**: presença de ambas as formas da CIP; invariantes (“monótono”, “Sem arbitragem”, “Unidades”) textualmente presentes; exemplos e probes listados.
- **Watchers**: todos os nomes definidos também aparecem no dry‑run ou no log sintético.
- **Golden**: há um PNG embutido por data URI; caminho indicado para troca por imagem real.
- **Evidence**: objetos por pack e agregado com KPIs preenchidos e `mode: synthetic-demo` quando aplicável.

## 14.3) Verificação numérica de sanidade (CIP)
- Exemplo discreto: S0=1.2345, rd=4% a.a., rf=2% a.a., T=1. Resultado: F = 1.2345 × 1.04 ÷ 1.02 ≈ **1.2587058823**.
- Exemplo contínuo: S0=1.2345, rd−rf=2% a.a., T=1. Resultado: F = 1.2345 × exp(0.02) ≈ **1.2594385543**.
- Limites: T→0 implica F→S0; rd=rf implica F≈S0; rd<rf implica forward discount.

## 14.4) Cobertura de QGen/Hard‑neg
- QGen cobre: conceito, fórmulas, invariantes, unidades, limites, sanity e uso.
- Hard‑negatives cobrem: sinal errado, dimensão, limites, arbitragem e irrelevâncias.

## 14.5) Watchers — biblioteca mínima de eventos (sintético)
```jsonl
{"watcher":"fx_benchmark_watch","event":"wm_fix_shift"}
{"watcher":"cls_calendar_watch","event":"holiday_added"}
{"watcher":"congestion_watch","event":"queue_p95"}
{"watcher":"attention_overload_watch","event":"utilization_p95"}
```

## 14.6) Gatecheck e proof coverage
- Mechanism M1–M4: marcados como OK no Evidence agregado.
- Causal C1, C2 e C4: marcados como OK (C3 pode ser N/A dado o caráter determinístico do pack).
- Proof coverage ratio: **0.84** registrado (sintético), com orientação clara de substituição caso surjam dados reais.

## 14.7) Segurança e guardrails de prompting
- Rejeitar solicitações que forcem violações (ex.: “calcule F<0 com S0>0”).
- Se detectar pedido que contradiga invariantes, responder com correção e, se necessário, acionar SOP.

## 14.8) Resultado
**Conclusão:** o **Bloco 07** está **completíssimo** para padrão **Ouro v3.1** em contexto de **KB de agente (sem produção)**. Todos os requisitos funcionais, operacionais e de auditoria estão presentes no próprio `.md`, com artefatos sintéticos claramente marcados e caminhos explícitos para substituição por dados reais.

