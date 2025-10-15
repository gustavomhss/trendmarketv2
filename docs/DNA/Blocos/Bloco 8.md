---
id: B08-CORE_DECISIONING
title: "Bloco 08 — CORE_DECISIONING (A43–A49) — FINAL"
version: "v2.8.1"
timezone: "America/Bahia"
doc_type: "kb_block"
block_range: ["A43","A49"]
maturity: "Gold (synthetic)"
status: "active"
snippet_budget_lines: 200
synthetic_mode: true
watchers_profile: ["simon_v2_8","causal_pearl_v1"]
rag_kpis:
  mrr_block_avg: 0.72
  ndcg_block_avg: 0.78
  coverage_block_avg: 0.83
  leakage_block_avg: 0.06
links:
  self: "BLOCO_08_CORE_DECISIONING_v2_8_1_FINAL.md"
closeout_rules:
  require_all_gates_green: true
  require_no_open_incidents: true
  require_block_kpis_above: { mrr: 0.65, ndcg: 0.70, coverage: 0.75, leakage: 0.10 }
observability:
  evidence_publish: { mode: "append_only", timelock_hours: 24 }
  audit_frequency_days: 14
policy:
  licenses: ["CC0","MIT","Apache-2.0","BSD","PSF"]
  pii: { allowed: false }
  red_team: { enabled: true, cadence_days: 30 }
---

> **Nota**: Versão **FINAL** sem placeholders. Todos os campos preenchidos e coerentes com Simon v2.8 e Diretrizes Builder v3.1.

# 0) Sumário

* [1) Front-matter v3.1](#1-front-matter-v31)
* [2) pack_defaults (Simon v2.8)](#2-pack_defaults-simon-v28)
* [3) Watchers: catálogo, parâmetros e dry_run](#3-watchers-catálogo-parâmetros-e-dry_run)
* [4) Packs A43…A49](#4-packs-a43a49)
  * [A43](#a43)
  * [A44](#a44)
  * [A45](#a45)
  * [A46](#a46)
  * [A47](#a47)
  * [A48](#a48)
  * [A49](#a49)
* [5) Goldens](#5-goldens)
* [6) Evidence e KPIs RAG](#6-evidence-e-kpis-rag)
* [7) QGen, Probes e Hard-negatives](#7-qgen-probes-e-hard-negatives)
* [8) Runner e scripts](#8-runner-e-scripts)
* [9) SOP e Incident](#9-sop-e-incident)
* [10) Relatórios de conflitos e maturidade](#10-relatórios-de-conflitos-e-maturidade)
* [11) D0–D7 — operação](#11-d0d7-—-operação)
* [12) Auditoria Final — checklist v3.1 + Triple-Review](#12-auditoria-final-—-checklist-v31--triple-review)
* [13) Golden Notebook + Lint Matemático](#13-golden-notebook--lint-matemático)
* [14) Changelog](#14-changelog)

---

## 1) Front-matter v3.1

Front-matter consolidado no cabeçalho YAML acima, com políticas, watchers e KPIs de bloco já definidos.

---

## 2) `pack_defaults` (Simon v2.8)

```yaml
pack_defaults:
  enforce_gates: true
  gates:
    rag_mrr_min: 0.35
    err_p95_max: 3.0
    fairness_gini_max: 0.25
    proof_coverage_ratio_min: 0.80
    satisficing_hit_rate_min: 0.60
    decision_cycle_time_max_s: 900
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
      metrics: { cycle_time_s: null, rework_rate: null, alt_count: null }
      artifacts: { intelligence: [], design: [], choice: [] }
    aspiration_levels:
      metric: "err_p95_pts"
      target: 2.0
      adapt_rules: { if_hit: { delta: "tighten by 5%" }, if_miss: { delta: "relax by 5%", max_retries: 2 } }
    attention_budget: { wip_limit: 3, time_quanta_s: 900, priority_policy: "EDD|SLACK|WSPT" }
    search_strategy: { type: "heuristic", neighborhood: [], eval: "score(err_p95, ttc_p50)", search_budget: { iters_max: 50, time_s: 300 } }
    near_decomposability: { modules: [], coupling_score: 0.4 }
    sops: { procedures: [], exception_policy: { escalate_if: ["latency_p95>1500ms","leakage>0.1"], cooloff_s: 600 } }
```

---

## 3) Watchers: catálogo, parâmetros e `dry_run`

### 3.1 Catálogo consolidado

```yaml
watchers_catalog:
  - { id: simplicity_watch,              check: "jargão acima do limite" }
  - { id: thickness_watch,               check: "espessura de mercado abaixo do alvo" }
  - { id: congestion_watch,              check: "fila ou latência acima dos targets" }
  - { id: collusion_watch,               check: "padrões de colusão entre agentes" }
  - { id: unraveling_watch,              check: "antecipação destrói matching" }
  - { id: oscillation_watch,             check: "ciclos com amplitude alta" }
  - { id: runaway_watch,                 check: "tendência explosiva" }
  - { id: delay_mismatch_watch,          check: "atrasos médios fora do alvo" }
  - { id: brittleness_watch,             check: "queda sob pequena perturbação" }
  - { id: confounding_watch,             check: "backdoor set insuficiente" }
  - { id: positivity_watch,              check: "overlap abaixo do limiar" }
  - { id: refuter_fail_watch,            check: "refutações falhando em excesso" }
  - { id: transport_mismatch_watch,      check: "mudança de domínio quebra suposições" }
  - { id: mediator_leak_watch,           check: "mediadores caem no ajuste" }
  - { id: overshoot_watch,               check: "supply acima de need_line" }
  - { id: nonconsumption_watch,          check: "baixa penetração em não consumidores" }
  - { id: modularity_mismatch_watch,     check: "modular quando devia integrar" }
  - { id: bottleneck_shift_watch,        check: "bottleneck migrou" }
  - { id: performance_trajectory_watch,  check: "deriva need_line vs supply_line" }
  - { id: invariant_violation_watch,     check: "invariante falhou" }
  - { id: complexity_regression_watch,   check: "tempo ou memória pioram" }
  - { id: numerical_stability_watch,     check: "erro relativo acima do limite" }
  - { id: randomness_regression_watch,   check: "seed ausente" }
  - { id: profiling_hotspot_watch,       check: "hot path sem otimização" }
  - { id: premature_optimization_watch,  check: "micro otimização sem evidência" }
  - { id: doc_coverage_watch,            check: "cobertura de documentação abaixo do limiar" }
  - { id: attention_overload_watch,      check: "utilização de atenção acima do máximo" }
  - { id: aspiration_drift_watch,        check: "alvo muda demais por semana" }
  - { id: search_stall_watch,            check: "busca estagna" }
  - { id: sop_exception_storm_watch,     check: "rajada de exceções de SOP" }
  - { id: coupling_spike_watch,          check: "acoplamento acima do limite" }
  - { id: decision_cycle_slip_watch,     check: "tempo de ciclo acima do target" }
```

### 3.2 Parâmetros do bloco

```yaml
watchers_params:
  attention_overload_watch: { window: 5, max_util: 0.85 }
  decision_cycle_slip_watch: { windows_required: 3, target_s: 900 }
  coupling_spike_watch: { limit: 0.50 }
  congestion_watch: { p95_ms: 1500 }
```

### 3.3 Script `dry_run`

```bash
#!/usr/bin/env bash
set -euo pipefail
BLK="A43 A44 A45 A46 A47 A48 A49"
echo "watchers_dry_run: início"
for P in $BLK; do
  echo "pack=$P status=ok attention_util=0.62 cycle_time_s=740 coupling=0.41"
done
echo "watchers_dry_run: fim"
```

### 3.4 Trigger sintético (`watchers_triggers.jsonl`)

```jsonl
{"ts":"2025-09-07T00:00:00-03:00","pack":"A46","watch":"attention_overload_watch","util":0.88,"action":"abrir_incidente"}
```

---

## 4) Packs A43–A49

As definições abaixo incluem metadados e corpo canônico sintético. Todos os packs possuem `golden_obrigatorio: true` com PNG mínimo em data URI.

### A43

```yaml
id: A43
titulo_canonico: "Enquadramento e Objetivos da Decisão"
domain: "pm"
artifact_paths:
  md: packs/A43_decision_frame.md
  evidence_json: evidence/A43.json
  golden_png: goldens/A43.png
  qgen: qgen/A43_20q.txt
  hard_neg: hardneg/A43_10.txt
qgen:
  seed: 4301
  style: "diagnostic|operational"
probes_log: probes/A43_probes.log
watch_rules: [attention_overload_watch, decision_cycle_slip_watch]
rag_kpis: { mrr: 0.71, ndcg: 0.77, coverage: 0.84, leakage: 0.06 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A44, A46]
overlaps: [A47]
supersedes: []
```

**dominio**: pm

**resumo_canonico**: Define o propósito, o escopo, as métricas e as restrições de uma decisão central. Evita ambiguidade e orienta coleta de evidências e trade-offs.

**formulas_ou_regras**:

* Objetivo composto: $J = w_1 U - w_2 R - w_3 C$ com $w_i \in [0,1], \sum w_i = 1$.
* Restrições duras: $C \leq C_{max}$, tempo de ciclo $T \leq T_{max}$.
* Nível de aspiração inicial $A_0$ com ajuste de Simon a cada janela.
* Aceitação condicional se $J \geq J_{min}$ e gates M1–M4 verdes.

**invariantes_ou_aceites**:

* Pesos $w_i$ documentados e somando um.
* Definições de utilidade/risco/custo claras e mensuráveis.
* Teto de tempo de ciclo compatível com `decision_cycle_time_max_s`.
* Regra de satisficing ativada para a métrica principal.

**exemplos_de_uso**:

* Entrada: w={0.5,0.3,0.2}, U=0.8, R=0.2, C=0.1 ⇒ J=0.34.
* Entrada: T=800 s e T_max=900 s ⇒ gate de ciclo atendido.

**links**: see_also=A44|A46 · overlaps=A47 · supersedes=∅

---

### A44

```yaml
id: A44
titulo_canonico: "Matriz de Evidências e Pesos"
domain: "ops"
artifact_paths:
  md: packs/A44_evidence_matrix.md
  evidence_json: evidence/A44.json
  golden_png: goldens/A44.png
  qgen: qgen/A44_20q.txt
  hard_neg: hardneg/A44_10.txt
qgen:
  seed: 4402
  style: "matrix|weights"
probes_log: probes/A44_probes.log
watch_rules: [doc_coverage_watch, confounding_watch]
rag_kpis: { mrr: 0.73, ndcg: 0.79, coverage: 0.86, leakage: 0.05 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A43, A46]
overlaps: [A45]
supersedes: []
```

**dominio**: ops

**resumo_canonico**: Consolida fontes de evidência, qualidade, direção do efeito e peso normalizado, com revisão de viés e cobertura de prova.

**formulas_ou_regras**:

* Normalização: $w_i = \frac{q_i}{\sum_j q_j}$ onde $q_i$ é qualidade da fonte.
* Score de evidência: $E = \sum_i w_i s_i$ com $s_i \in [-1,1]$.
* Cobertura de prova mínima $\geq 0.8$ antes de avançar.
* Penalidade de viés: $q_i' = q_i\cdot(1-b_i)$ com $b_i \in [0,1]$.

**invariantes_ou_aceites**:

* Pesos somam um e são reprodutíveis.
* Proveniência/licença registradas.
* Registro de sinais pró e contra.
* Refutadores executados quando causal.

**exemplos_de_uso**:

* q=[0.9,0.6], s=[+0.5,+0.2] ⇒ E≈0.38.
* b_2=0.3 ajusta q_2 para 0.42 e atualiza pesos.

**links**: see_also=A43|A46 · overlaps=A45 · supersedes=∅

---

### A45

```yaml
id: A45
titulo_canonico: "Geração e Seleção de Opções"
domain: "teoria"
artifact_paths:
  md: packs/A45_generate_select.md
  evidence_json: evidence/A45.json
  golden_png: goldens/A45.png
  qgen: qgen/A45_20q.txt
  hard_neg: hardneg/A45_10.txt
qgen:
  seed: 4503
  style: "dominance|pruning"
probes_log: probes/A45_probes.log
watch_rules: [search_stall_watch, attention_overload_watch]
rag_kpis: { mrr: 0.70, ndcg: 0.76, coverage: 0.81, leakage: 0.07 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A44, A46]
overlaps: [A43]
supersedes: []
```

**dominio**: teoria

**resumo_canonico**: Expande alternativas com busca heurística e poda por dominância, preservando diversidade suficiente para escolha.

**formulas_ou_regras**:

* A domina B se $U_A \geq U_B$, $R_A \leq R_B$, $C_A \leq C_B$ e ao menos uma estrita.
* Orçamento de atenção: WIP $\leq 3$; quanta de 900 s.
* Parada: ganho $< \epsilon$ em E por $k$ iterações.
* Diversidade mínima: Hamming médio $\geq d_{min}$.

**invariantes_ou_aceites**:

* Log de alternativas e podas.
* Sem exclusão de alternativas não avaliadas.
* Orçamento respeitado.
* Diversidade calculada.

**exemplos_de_uso**:

* A(U=0.7,R=0.2,C=0.2) domina B(0.6,0.3,0.3) ⇒ poda B.
* Ganho marginal $<0.01$ por 5 iterações ⇒ parar.

**links**: see_also=A44|A46 · overlaps=A43 · supersedes=∅

---

### A46

```yaml
id: A46
titulo_canonico: "Função de Utilidade e Trade-offs"
domain: "pricing"
artifact_paths:
  md: packs/A46_utility_tradeoffs.md
  evidence_json: evidence/A46.json
  golden_png: goldens/A46.png
  qgen: qgen/A46_20q.txt
  hard_neg: hardneg/A46_10.txt
qgen:
  seed: 4604
  style: "utility|risk"
probes_log: probes/A46_probes.log
watch_rules: [numerical_stability_watch, invariant_violation_watch]
rag_kpis: { mrr: 0.75, ndcg: 0.81, coverage: 0.85, leakage: 0.05 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A43, A44, A45]
overlaps: []
supersedes: []
```

**dominio**: pricing

**resumo_canonico**: Modela utilidade com aversão a risco e custo, calibrando pesos por evidência e controlando instabilidade numérica.

**formulas_ou_regras**:

* Utilidade ajustada: $U^* = \alpha U - \beta R - \gamma C$ com $\alpha+\beta+\gamma=1$.
* Aversão a risco exponencial: $U = 1 - e^{-k x}$ para ganho relativo $x$.
* Penalização se $\mathrm{rel\_err} > 10^{-6}$.
* Fairness: Gini $\leq 0.25$ no desfecho agregado.

**invariantes_ou_aceites**:

* Pesos calibrados por A44, em cache.
* Erro relativo documentado.
* Fairness por janela.
* Gate de estabilidade numérica verde.

**exemplos_de_uso**:

* k=1, x=0.5 ⇒ U=1−e^{−0.5}; U^* com pesos {0.6,0.3,0.1}.
* rel_err=2e−6 ⇒ penalização de 5% em U^*.

**links**: see_also=A43|A44|A45 · overlaps=∅ · supersedes=∅

---

### A47

```yaml
id: A47
titulo_canonico: "Gatecheck do Ciclo Decisório D0–D7"
domain: "ops"
artifact_paths:
  md: packs/A47_cycle_gatecheck.md
  evidence_json: evidence/A47.json
  golden_png: goldens/A47.png
  qgen: qgen/A47_20q.txt
  hard_neg: hardneg/A47_10.txt
qgen:
  seed: 4705
  style: "gates|checklist"
probes_log: probes/A47_probes.log
watch_rules: [decision_cycle_slip_watch, doc_coverage_watch]
rag_kpis: { mrr: 0.69, ndcg: 0.75, coverage: 0.80, leakage: 0.07 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A43, A48, A49]
overlaps: [A44]
supersedes: []
```

**dominio**: ops

**resumo_canonico**: Define entradas e saídas por estágio com critérios objetivos de passagem e retorno controlado quando um gate falha.

**formulas_ou_regras**:

* Tempo de ciclo total $\leq 900$ s.
* Cobertura documental $\geq 0.8$ por estágio.
* Falha em qualquer gate ⇒ retorno ao estágio anterior com ação corretiva.
* Autonomia de SOP $\geq 0.6$.

**invariantes_ou_aceites**:

* Timestamp por transição.
* Evidência anexada antes de promover.
* Registro de causa de retorno com ação.
* Sem promoção com documentação abaixo do mínimo.

**exemplos_de_uso**:

* D3 falha por cobertura 0.7 ⇒ retorna a D2 com reforço de prova.
* Soma de tempos 880 s ⇒ passa no gate de ciclo.

**links**: see_also=A43|A48|A49 · overlaps=A44 · supersedes=∅

---

### A48

```yaml
id: A48
titulo_canonico: "Fallback, Pack Lite e Escalonamento"
domain: "ops"
artifact_paths:
  md: packs/A48_fallback_lite_escalate.md
  evidence_json: evidence/A48.json
  golden_png: goldens/A48.png
  qgen: qgen/A48_20q.txt
  hard_neg: hardneg/A48_10.txt
qgen:
  seed: 4806
  style: "fallback|escalation"
probes_log: probes/A48_probes.log
watch_rules: [sop_exception_storm_watch, congestion_watch]
rag_kpis: { mrr: 0.71, ndcg: 0.77, coverage: 0.82, leakage: 0.06 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A47, A49]
overlaps: [A43]
supersedes: []
```

**dominio**: ops

**resumo_canonico**: Define variantes lite, critérios de degradação e trilhas de escalonamento para manter serviço e segurança decisória quando recursos ficam limitados.

**formulas_ou_regras**:

* Disparador: $p95\_latency > 1500\,ms$ ⇒ `pack_lite`.
* Escalonamento por severidade: S1 imediato, S2 em 30 min, S3 em 24 h.
* Autonomia de SOP $\geq 0.6$ para fallback sem bloqueio.
* Retorno ao modo completo após duas janelas verdes consecutivas.

**invariantes_ou_aceites**:

* Registro de causa por degradação.
* Comunicação por severidade.
* Evidência de restauração anexada.
* Sem degradação silenciosa.

**exemplos_de_uso**:

* Pico de latência ⇒ `pack_lite` e profundidade de busca −50%.
* Duas janelas verdes ⇒ volta ao modo completo.

**links**: see_also=A47|A49 · overlaps=A43 · supersedes=∅

---

### A49

```yaml
id: A49
titulo_canonico: "Pós-decisão, Aprendizagem e Deltas"
domain: "ops"
artifact_paths:
  md: packs/A49_post_decision_learning.md
  evidence_json: evidence/A49.json
  golden_png: goldens/A49.png
  qgen: qgen/A49_20q.txt
  hard_neg: hardneg/A49_10.txt
qgen:
  seed: 4907
  style: "aftercare|learning"
probes_log: probes/A49_probes.log
watch_rules: [aspiration_drift_watch, performance_trajectory_watch]
rag_kpis: { mrr: 0.74, ndcg: 0.80, coverage: 0.85, leakage: 0.05 }
golden_obrigatorio: true
golden_data_uri: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
see_also: [A43, A47, A48]
overlaps: [A44]
supersedes: []
```

**dominio**: ops

**resumo_canonico**: Mede resultados pós-decisão, compara com alvos, ajusta aspiração e atualiza pesos e módulos quase decompostos.

**formulas_ou_regras**:

* Erro de metas: $e = m_{obs} - m_{alvo}$ por métrica.
* Aspiração: acerto ⇒ +5% (aperta), falha ⇒ −5% (relaxa), até 2 tentativas.
* Atualiza `coupling_score` com média móvel.
* Publica deltas e evidências em modo `append_only`.

**invariantes_ou_aceites**:

* Comparação com janela de controle.
* Registro de ajuste de aspiração (data/motivo).
* Sem alterar pesos sem evidência.
* Publicação imutável de deltas.

**exemplos_de_uso**:

* Cobertura alvo 0.85, observado 0.88 ⇒ novo alvo 0.8925.
* `coupling_score` > 0.5 ⇒ ação de modularização.

**links**: see_also=A43|A47|A48 · overlaps=A44 · supersedes=∅

---

## 5) Goldens

* **Padrão**: todos os packs possuem `golden_obrigatorio: true` com PNG mínimo em data URI.
* **Exemplo de trigger**:

```json
{ "pack": "A43", "trigger": "golden_detected", "artifact": "goldens/A43.png", "ts": "2025-09-07T00:00:00-03:00" }
```

---

## 6) Evidence e KPIs RAG

### 6.1 Por pack

```json
{
  "A43": { "mrr": 0.71, "ndcg": 0.77, "coverage": 0.84, "leakage": 0.06 },
  "A44": { "mrr": 0.73, "ndcg": 0.79, "coverage": 0.86, "leakage": 0.05 },
  "A45": { "mrr": 0.70, "ndcg": 0.76, "coverage": 0.81, "leakage": 0.07 },
  "A46": { "mrr": 0.75, "ndcg": 0.81, "coverage": 0.85, "leakage": 0.05 },
  "A47": { "mrr": 0.69, "ndcg": 0.75, "coverage": 0.80, "leakage": 0.07 },
  "A48": { "mrr": 0.71, "ndcg": 0.77, "coverage": 0.82, "leakage": 0.06 },
  "A49": { "mrr": 0.74, "ndcg": 0.80, "coverage": 0.85, "leakage": 0.05 }
}
```

### 6.2 Agregado do bloco

```json
{ "mrr_block_avg": 0.72, "ndcg_block_avg": 0.78, "coverage_block_avg": 0.83, "leakage_block_avg": 0.06 }
```

---

## 7) QGen, Probes e Hard-negatives

> QGen orientados a diagnóstico/execução; hard-negatives explicitam violações graves.

### A43 — 20 QGen

1) Escreva a função objetivo J e explique U, R e C.  
2) Como validar que os pesos w_i somam 1?  
3) Qual a regra para o teto de tempo de ciclo?  
4) Quando aceitar a decisão segundo J_min e os mechanism gates?  
5) Como definir e ajustar o nível de aspiração A_0?  
6) Dê um exemplo numérico de J com U/R/C e w.  
7) O que caracteriza uma restrição “dura” vs. “mole” aqui?  
8) Como mapear métricas aos componentes U, R e C?  
9) Quais evidências pedem re‑enquadramento do escopo?  
10) Qual o papel do satisficing na métrica principal?  
11) Como registrar T e verificar `decision_cycle_time_max_s`?  
12) Que artefatos entram em Intelligence/Design/Choice (IDC)?  
13) Como lidar com trade‑offs quando R cai e C sobe?  
14) Quando reabrir A44 (pesos) após mudar J_min?  
15) Como conectar o frame com a poda de A45?  
16) Quais sinais disparam revisão do objetivo composto?  
17) Como aplicar pesos públicos herdados de A44?  
18) Quais invariantes bloqueiam promoção de estágio?  
19) Como documentar rationale de aceitação/recusa?  
20) Qual a relação entre T, WIP e budget de atenção?  

**A43 — 10 Hard neg**

1) Aceitar a decisão mesmo com T > T_max se J for alto.  
2) Permitir que os pesos w_i somem 1,2 para priorizar utilidade.  
3) Dispensar definição operacional de U/R/C para acelerar.  
4) Ignorar mechanism gates se J ≥ J_min.  
5) Tratar satisficing como opcional em decisões centrais.  
6) Não registrar tempos por transição de estágio.  
7) Ajustar pesos sem evidência documentada.  
8) Aceitar cobertura documental < 0,5 em qualquer estágio.  
9) Ignorar restrições duras se houver consenso qualitativo.  
10) Descartar rationale final para reduzir ruído no log.  

### A44 — 20 QGen

1) Como normalizar pesos a partir de qualidades q_i?  
2) O que é o score de evidência E e seu intervalo?  
3) Qual a cobertura mínima antes de promover um estágio?  
4) Como aplicar penalidade de viés com b_i?  
5) Que registros de proveniência e licença são obrigatórios?  
6) Como anotar sinais pró e contra na matriz?  
7) Quando executar refutadores?  
8) Exemplo numérico de normalização e cálculo de E.  
9) Como detectar fontes redundantes/colineares?  
10) Como versionar pesos com trilha de auditoria?  
11) Qual a relação entre A44 e calibração de A46?  
12) Como lidar com fontes conflitantes (sinais opostos)?  
13) Estratégias para elevar cobertura de prova ≥ 0,8.  
14) Como incorporar TTL/decadência de fontes?  
15) Qual o impacto de b_i alto em q_i'?  
16) Como manter reprodutibilidade do experimento de pesos?  
17) Como validar licenças permissivas nas fontes?  
18) Como registrar evidências contrárias sem viés de confirmação?  
19) Quando reabrir coleta (D2) para fechar lacunas?  
20) Como publicar pesos e seus deltas ao público?  

**A44 — 10 Hard neg**

1) Avançar com cobertura de prova de 0,6.  
2) Ignorar fontes com viés se reforçam a hipótese.  
3) Somar pesos sem normalizar por ∑q_j.  
4) Omitir sinais contrários para manter coerência.  
5) Não registrar licenças das fontes.  
6) Rodar refutadores apenas se o resultado for desfavorável.  
7) Tratar s_i fora de [-1,1] como válido.  
8) Aceitar pesos que somam 0,8 para favorecer fonte principal.  
9) Não versionar mudanças de peso.  
10) Misturar dados sob licença restritiva sem marcação.  

### A45 — 20 QGen

1) Defina dominância entre alternativas.  
2) Por que exigir pelo menos uma desigualdade estrita?  
3) Como aplicar o WIP ≤ 3 na prática?  
4) O que é o quantum de 900 s?  
5) Critério de parada por ganho < ε em E.  
6) Como medir diversidade por Hamming médio?  
7) Como registrar o log de podas?  
8) Quando não se deve podar uma alternativa?  
9) Como equilibrar exploração vs. custo de atenção?  
10) Como reabrir busca quando o ganho volta a subir?  
11) Qual a ligação entre diversidade e risco de lock‑in?  
12) Como validar que WIP foi respeitado?  
13) Como evitar viés na geração inicial de alternativas?  
14) Como lidar com empates de dominância?  
15) Quando promover shortlist para simulação (D5)?  
16) Como ajustar ε e k ao budget disponível?  
17) Como detectar estagnação (watcher `search_stall_watch`)?  
18) Como conectar A45 com pesos de A44?  
19) Como representar alternativas reprovadas para auditoria?  
20) Como medir cobertura de espaço de design?  

**A45 — 10 Hard neg**

1) Podar alternativas sem avaliação prévia.  
2) Ignorar orçamento de atenção quando há urgência.  
3) Aceitar ganho negativo por várias iterações como progresso.  
4) Dispensar diversidade mínima para acelerar.  
5) Declarar dominância com todas desigualdades não estritas.  
6) Não registrar log de podas.  
7) Encerrar busca na primeira melhoria.  
8) Aumentar WIP para 10 por conveniência.  
9) Usar ε variável sem registrar.  
10) Promover shortlist sem simulação.  

### A46 — 20 QGen

1) Escreva e explique $U^*$ e seus pesos.  
2) Como garantir que α+β+γ=1?  
3) Quando aplicar a utilidade exponencial de risco?  
4) O que é x (ganho relativo) no contexto?  
5) Como medir/registrar erro relativo numérico?  
6) Qual a penalidade quando rel_err > 1e-6?  
7) Como checar fairness (Gini ≤ 0,25) por janela?  
8) Como calibrar α,β,γ a partir de A44?  
9) Exemplo numérico de $U$ e $U^*$.  
10) Como lidar com saturação de U quando k é alto?  
11) Como versionar pesos e evitar drift?  
12) Quando reabrir A44 por instabilidade em U*?  
13) Como tratar custos não lineares no termo C?  
14) Como propagar incerteza de R para U*?  
15) Quais cenários exigem outra família de utilidade?  
16) Como testar sensibilidade de k?  
17) Como integrar fairness ao critério final de escolha?  
18) Como checar o watcher de estabilidade numérica?  
19) Como documentar casos de borda (under/overflow)?  
20) Como auditar a consistência com A43 (J vs U*)?  

**A46 — 10 Hard neg**

1) Aceitar α+β+γ≠1 para privilegiar α.  
2) Ignorar penalização mesmo com rel_err alto.  
3) Omitir fairness por janela.  
4) Calibrar pesos sem referência a A44.  
5) Tratar k como arbitrário sem estudo de sensibilidade.  
6) Usar x absoluto, não relativo, por conveniência.  
7) Não registrar erros numéricos.  
8) Desconsiderar custos C ao calcular U*.  
9) Publicar pesos sem versionamento.  
10) Misturar pesos e utilidade de domínios distintos sem validação.  

### A47 — 20 QGen

1) Quais são os estágios D0–D7 e suas entregas?  
2) Qual o target para tempo de ciclo total?  
3) Como medir cobertura documental por estágio?  
4) O que acontece quando um gate falha?  
5) Como verificar autonomia de SOP ≥ 0,6?  
6) Como auditar timestamps de transição?  
7) Quais evidências são mínimas antes de promover?  
8) Como registrar a causa de retorno e a ação corretiva?  
9) Como acionar watchers de slip de ciclo?  
10) Como integrar A47 com A48 (fallback)?  
11) Como tratar exceções multi‑estágio?  
12) Qual a relação com A49 (pós‑decisão)?  
13) Como consolidar um decision log D0→D7?  
14) Como testar gates com simulação (D5)?  
15) Como medir rework_rate do IDC?  
16) Como versionar critérios de passagem?  
17) Como lidar com documentação sensível (PII proibido)?  
18) Como reagir a doc_coverage_watch em vermelho?  
19) Como definir janelas e agregação para o ciclo?  
20) Como manter audit trail imutável?  

**A47 — 10 Hard neg**

1) Promover estágios sem evidência documentada.  
2) Ignorar cobertura < 0,8 se o time concordar.  
3) Não registrar timestamps nas transições.  
4) Manter SOP autonomia < 0,6 em fallback.  
5) Aceitar tempo de ciclo > 900 s como normal.  
6) Omitir causa da falha do gate.  
7) Pular retorno ao estágio anterior.  
8) Dispensar simulação pré‑gate.  
9) Misturar PII nos anexos.  
10) Não versionar critérios de passagem.  

### A48 — 20 QGen

1) Quando ativar `pack_lite`?  
2) Como medir p95_latency e thresholds?  
3) O que define S1, S2 e S3?  
4) Quem comunica em cada severidade e como?  
5) Quais evidências anexar na degradação?  
6) Como verificar autonomia de SOP ≥ 0,6?  
7) Como voltar ao modo completo (2 janelas verdes)?  
8) Como reduzir profundidade de busca no modo lite?  
9) Como lidar com `sop_exception_storm_watch`?  
10) Como registrar incident timeline?  
11) Quando escalar para coordenação em 30 min?  
12) Como tratar filas de resgates e overload?  
13) Como documentar rationale do escalonamento?  
14) Como sincronizar com A47 (gates) durante fallback?  
15) Como ativar circuit breaker do bloco (Keynes buffer)?  
16) Como auditar comunicação e SLAs por severidade?  
17) Como validar restauração com evidências?  
18) Como lidar com degradação em cascata?  
19) Como atualizar playbooks após o incidente?  
20) Como prevenir regressão pós‑restauração?  

**A48 — 10 Hard neg**

1) Ativar `pack_lite` por preferência subjetiva.  
2) Omitir a causa da degradação.  
3) Pular comunicação em S1 por “ser óbvio”.  
4) Voltar ao modo completo com 1 janela verde.  
5) Fallback com SOP autonomia < 0,6.  
6) Não anexar evidências na restauração.  
7) Ignorar congestion_watch durante picos.  
8) Não registrar incident timeline.  
9) Aumentar profundidade de busca no modo lite.  
10) Manter degradação silenciosa para evitar barulho.  

### A49 — 20 QGen

1) Como calcular e interpretar e = m_obs − m_alvo?  
2) Quando apertar ou relaxar a aspiração e em quanto?  
3) Qual o limite de tentativas de ajuste?  
4) Como manter registro (data/motivo) do ajuste?  
5) Como atualizar coupling_score e interpretar > 0,5?  
6) Como publicar deltas em modo append_only?  
7) Como escolher a janela de controle?  
8) Como detectar aspiration_drift_watch?  
9) Como revisar módulos quase decompostos após deltas?  
10) Como retroalimentar A44 com novos pesos?  
11) Como evitar alterar pesos sem evidência?  
12) Como validar integridade dos registros públicos?  
13) Como fechar o laço D7 → D0?  
14) Como medir impacto em Coverage/Leakage do bloco?  
15) Como lidar com outliers na janela de controle?  
16) Como comunicar mudanças ao público?  
17) Como priorizar ações corretivas por impacto?  
18) Como sincronizar com performance_trajectory_watch?  
19) Como usar telemetria para predição de falhas futuras?  
20) Como definir critério de “aprendizagem suficiente”?  

**A49 — 10 Hard neg**

1) Ajustar aspiração sem limite de tentativas.  
2) Alterar pesos sem evidência nova.  
3) Publicar deltas em modo editável.  
4) Ignorar janela de controle nas comparações.  
5) Omitir motivo/data nos ajustes.  
6) Desconsiderar coupling_score após mudanças.  
7) Não retroalimentar A44 com deltas.  
8) Ignorar aspiration_drift_watch.  
9) Excluir deltas negativos para manter imagem.  
10) Não comunicar mudanças relevantes.  

---

## 8) Runner e scripts

### 8.1 Makefile

```makefile
.PHONY: ingest qgen probes goldens merge_evidence update_rag_kpis watchers_dry watchers_fire gatecheck closeout simon_check

ingest:
	python ops/tools/embed_png_as_data_uri.py goldens/ > ops/out/data_uris.json

qgen:
	python ops/tools/qgen.py --packs A43 A44 A45 A46 A47 A48 A49 --seed 808

probes:
	python ops/tools/probes.py --packs A43 A44 A45 A46 A47 A48 A49 --logdir probes/

goldens:
	mkdir -p goldens && python - <<'PY'
import base64,sys
b64="iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO5nWmEAAAAASUVORK5CYII="
for p in ['A43','A44','A45','A46','A47','A48','A49']:
    open(f'goldens/{p}.png','wb').write(base64.b64decode(b64))
print('goldens ok')
PY

merge_evidence:
	python ops/tools/merge_evidence.py evidence/ > evidence/_merged.json

update_rag_kpis:
	python ops/tools/calc_kpis_rag.py evidence/_merged.json --update self

watchers_dry:
	bash ops/watchers/dry_run.sh

watchers_fire:
	python ops/watchers/run_once.py --triggers ops/watchers/watchers_triggers.jsonl

gatecheck:
	python ops/tools/gatecheck.py --block B08

closeout:
	python ops/tools/closeout.py --block B08

simon_check:
	python ops/tools/simon_check.py --block B08
```

### 8.2 utilitários mínimos

**ops/tools/merge_evidence.py**

```python
import json, sys, os
acc = {}
for fn in sorted(os.listdir(sys.argv[1])):
    if not fn.endswith('.json'): continue
    with open(os.path.join(sys.argv[1], fn)) as f:
        d = json.load(f)
        acc[os.path.splitext(fn)[0]] = d
print(json.dumps(acc, ensure_ascii=False, separators=(',',':')))
```

**ops/tools/calc_kpis_rag.py**

```python
import json, sys
with open(sys.argv[1]) as f:
    data = json.load(f)
vals = [v for k,v in data.items() if k.startswith('A')]
avg = {
  'mrr_block_avg': round(sum(v['mrr'] for v in vals)/len(vals),2),
  'ndcg_block_avg': round(sum(v['ndcg'] for v in vals)/len(vals),2),
  'coverage_block_avg': round(sum(v['coverage'] for v in vals)/len(vals),2),
  'leakage_block_avg': round(sum(v['leakage'] for v in vals)/len(vals),2)
}
print(json.dumps(avg, ensure_ascii=False))
```

**ops/tools/embed_png_as_data_uri.py**

```python
import sys, base64, os, json
out = {}
for root,_,files in os.walk(sys.argv[1]):
    for fn in files:
        if fn.lower().endswith('.png'):
            p = os.path.join(root, fn)
            b64 = base64.b64encode(open(p,'rb').read()).decode('ascii')
            out[p] = f"data:image/png;base64,{b64}"
print(json.dumps(out))
```

**ops/watchers/run_once.py**

```python
import argparse, json
p = argparse.ArgumentParser()
p.add_argument('--triggers', default='ops/watchers/watchers_triggers.jsonl')
a = p.parse_args()
for line in open(a.triggers):
    ev = json.loads(line)
    print(f"fire {ev['watch']} on {ev['pack']} action={ev['action']}")
```

**ops/tools/gatecheck.py**

```python
import json
E = json.load(open('evidence/_merged.json'))
ok = all(E[k]['coverage']>=0.8 and E[k]['leakage']<=0.1 for k in E if k.startswith('A'))
print('gates=green' if ok else 'gates=red')
```

---

## 9) SOP e Incident

**Disparadores**: congestionamento alto, sobrecarga de atenção, desvio de aspiração, slip de ciclo.  
**Ações**: ativar `pack_lite`, reequilibrar WIP, revisar pesos, reabrir A44 ou A45 conforme causa.  
**Comunicação**: S1 núcleo imediato; S2 coordenação em 30 min; S3 em 24 h.  
**Volta ao normal**: duas janelas verdes consecutivas.

---

## 10) Relatórios de conflitos e maturidade

* **Conflitos**: divergência entre A44 e A46 sobre pesos/utilidade abre revisão com registro de decisão e rationale.  
* **Maturidade**: promoção para Gold quando mechanism gates verdes, `proof_coverage_ratio ≥ 0.8` e KPIs de bloco atendidos.

---

## 11) D0–D7 — operação

* **D0** inteligência do problema e stakeholders.  
* **D1** desenho de alternativas iniciais.  
* **D2** coleta e padronização de evidências.  
* **D3** calibração de pesos e utilidade.  
* **D4** poda e seleção de shortlist.  
* **D5** simulação e verificação de gates.  
* **D6** escolha e documentação final.  
* **D7** pós-decisão e aprendizagem com deltas.

---

## 12) Auditoria Final — checklist v3.1 + Triple-Review

* Packs A43–A49 presentes e consistentes.  
* Nenhum símbolo de interrogação dentro dos packs.  
* Fórmulas alinhadas a regras; pesos normalizados; métricas definidas.  
* QGen e hard neg específicos por pack.  
* Evidence JSON por pack e agregado presentes.  
* Watchers e triggers válidos.  
* Scripts mínimos executáveis e consistentes.  
* Golden obrigatório com PNG data URI por pack.  
* Revisões A, B e C concluídas e registradas.

---

## 13) Golden Notebook + Lint Matemático

**Equação didática**  
$U^* = \alpha U - \beta R - \gamma C \quad \text{com} \quad \alpha+\beta+\gamma=1$

**ops/tools/mathlint.py**

```python
import sys, re
text = open(sys.argv[1]).read() if len(sys.argv)>1 else sys.stdin.read()
errs = []
for m in re.finditer(r"U\^\*\s*=\s*([0-9\.]+)U\s*-\s*([0-9\.]+)R\s*-\s*([0-9\.]+)C", text):
    a,b,c = map(float, m.groups())
    if abs((a+b+c)-1.0) > 1e-9:
        errs.append((a,b,c))
print("MATHLINT: ok" if not errs else f"MATHLINT: pesos não somam 1 -> {errs}")
```

---

## 14) Changelog

* **v2.8.1 — 2025-09-07**: versão FINAL do Bloco 08, 100% preenchida (sem placeholders), com packs A43–A49, goldens, Evidence por pack e agregado, QGen/Hard-neg por pack, watchers e scripts mínimos, políticas e closeout rules.

