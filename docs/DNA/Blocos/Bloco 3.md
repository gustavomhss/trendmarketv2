---
id: kb/blocos/bloco_03_a13_a23_final_v3_00
title: "Bloco 03 — A13–A23 (Foundations & Disruption Overlay) • FINAL v3.00 — sem placeholders"
version: "v3.00 (conforme v3.1 + Simon v2.8 + Christensen overlay)"
date: "2025-09-07"
timezone: America/Bahia
owner: AG1 (Knowledge Builder)
stewards: [Research, Builder]
doc_type: kb_block
block_range: [A13, A23]
domain: foundations
snippet_budget_lines: 200
maturity: Gold  # modo demonstrativo: watchers + playbooks + closeout sintético; KPIs RAG preenchidos via pipeline
dag_policy: { deterministic_seeds: true }
rag_kpis: { mrr: null, ndcg: null, coverage: null, leakage: null }
watchers_profile: [christensen_v2, simon_v2_8, causal_pearl_v1]
links:
  - kb/blocos/bloco_01_a0_a12_final_v1_60
  - kb/blocos/bloco_02_autopilot_final_v2_10
  - master_list/v2_8
observability:
  common_keys: [job_id, pack_id, artifact_path, trace_id]
  sim_trace_hash_required: true
---

# 0) Sumário & **Revisão Tripla** (v3.00)
**Objetivo:** Entregar **Bloco 03 (A13–A23)** **100% preenchido** (sem placeholders), com **conteúdo canônico inline**, **Evidence JSON** por pack + **agregado**, **Probes/QGen/Hard‑negatives (20/20/10)** por pack, **watchers + parâmetros**, **runbooks**, **statusboards**, **conflitos/duplicidades**, e **closeout sintético**. Goldens: **N/A** (sem packs críticos em DL/matemática aqui). Lint matemático: **N/A**.

**Revisão Tripla:**
1) **Conteúdo** — Packs A13–A23 completos; respostas canônicas **no corpo** (não só probes). **OK**.
2) **Técnica** — Gates v2.8 (Simon); watchers; CI/gates; ADRs; statusboards; Evidence pronto. **OK**.
3) **Conformidade v3.1** — front‑matter com `rag_kpis=null`; snippet budget=200; Evidence JSON; QGen/HN; watchers; maturidade documentada. **OK**.

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
    object_contract_coverage_min: 0.0
    ten_x_required: false
    ten_x_metric_min: null
    leverage_points_min: 0
    resilience_budget_min: 0.0
    identification_required: false
    refuter_pass_rate_min: 0.0
    positivity_min_support: 0.0
    sensitivity_threshold_min: null
    literate_coverage_min: 0.0
    invariant_coverage_min: 0.0
    complexity_regression_guard: false
    numerical_rel_err_max: null
    doc_coverage_min: 0.0
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
  simon:
    decision_process: { model: "IDC@1", metrics: { cycle_time_s: null, rework_rate: null, alt_count: null }, artifacts: { intelligence: [], design: [], choice: [] } }
    aspiration_levels: { metric: "err_p95_pts", target: null, adapt_rules: { if_hit: { delta: "tighten by 5%" }, if_miss: { delta: "relax by 5%", max_retries: 2 } } }
    attention_budget: { wip_limit: 3, time_quanta_s: 900, priority_policy: "EDD|SLACK|WSPT" }
    search_strategy: { type: "heuristic", neighborhood: [], eval: "score(err_p95, ttc_p50)", search_budget: { iters_max: 50, time_s: 300 } }
    near_decomposability: { modules: [], coupling_score: null }
    sops: { procedures: [], exception_policy: { escalate_if: ["latency_p95>1500ms","leakage>0.1"], cooloff_s: 600 } }
```

---

# 2) Watchers — catálogo & parâmetros
```yaml
watchers:
  - simplicity_watch: { check: "jargão/complexidade acima do limite" }
  - thickness_watch: { check: "espessura de mercado abaixo do alvo" }
  - congestion_watch: { check: "fila/latência acima dos targets" }
  - collusion_watch: { check: "padrões de colusão entre agentes" }
  - unraveling_watch: { check: "antecipação/agenda destruindo matching" }
  - decision_cycle_slip_watch: { check: "tempo de ciclo > target por 3 janelas" }
  - attention_overload_watch: { check: "utilização de atenção > teto" }
  - aspiration_drift_watch: { check: "deriva de aspiração" }
  - search_stall_watch: { check: "ociosidade na busca heurística" }
  - sop_exception_storm_watch: { check: "tempestade de exceções de SOP" }
  - coupling_spike_watch: { check: "pico de acoplamento" }
  - confounding_watch: { check: "backdoor set insuficiente" }
  - instrument_strength_watch: { check: "F-stat < 10" }
  - transport_mismatch_watch: { check: "quebra de suposições em transporte" }
  - mev_inclusion_delay_watch: { check: "p95 de inclusão por slot > alvo" }
params:
  attention_overload_watch: { utilization_p95_max: 0.90 }
  decision_cycle_slip_watch: { cycle_time_s_p95_max: 900 }
  instrument_strength_watch: { f_stat_min: 10 }
  mev_inclusion_delay_watch: { slots_p95_max: 6 }
```

---

# 3) Statusboards
```yaml
statusboards:
  jobs:    "/statusboard/panels/jobs.yml"            # KPIs: ttfp_p95, job_success_rate_7d, repeat_hire
  port:    "/statusboard/panels/portfolio.yml"       # discovery vs delivery
  mlops:   { drift: "mlops/monitoring.yml", retraining: "mlops/retraining.yml" }
  growth:  { funnel: "growth/funnel.yml", cac_ltv: "growth/metrics.yml" }
  compl:   { kyc_aml: "compliance/kyc_aml.md" }
```

---

# 4) ADRs e CI/Gates (disruption‑ready)
```md
/strategy/adr_disruptive_option.md
Objetivo (Job): J1_milkshake — desbloquear não‑consumo.
Métricas: TTFP p95, success_rate, repeat_hire, volatility.
Riscos: canibalização controlada, trade‑offs de SLO.
```
```diff
# /ci/gates/promote.yml
+ requires: [job_progress_guard]
+ tracks: { discovery: true, delivery: true }
# /ci/checks/packs_lint.yml
+ ensure_job_link: { require: "/jtbd/jobs_ledger.yml" }
+ ensure_job_metrics: { require: "/config/jtbd_kpis.yml" }
# /mechanism/congestion_pricing.yml
+ discount_for_non_consumption: 0.8
```

---

# 5) **Packs A13–A23 (conteúdo canônico completo)**
> Estrutura: **Tarefa YAML → Conteúdo → Evidence JSON → Probes (20) → QGen (20) → Hard‑negatives (10)**. IDs de vetores e `artifact_paths` apontam para esta página.

## A13 — Automação & Orquestração
### Tarefa YAML
```yaml
id: A13-AUTO-ALL
competency: Automação
priority: P2
why: pipelines previsíveis e KB viva
content_min: [ci_cd, orchestration, watchers_diffs]
deps: [A11, A12, A10]
license: MIT
```
### Conteúdo
- **CI/CD**: lint→test→package→deploy; **canary** com rollback; artefatos versionados (`build_id`, `git_sha`, `semver`).
- **Orquestração**: DAGs (Airflow/Prefect) para ingestão RAG, atualização de vetores, e verificação de **statusboards**.
- **Watchers diffs**: monitora RSS/API/Git; abre issue com `impact:jobs|mlops|compliance`.
- **Observabilidade**: `trace_id`, `job_id`; logs estruturados; SLIs de pipeline: **TTC p50** ≤ 15min.
### Evidence JSON
```json
{ "id": "A13-AUTO-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A13-—-Automação-&-Orquestração"],
  "vector_ids": ["a13-auto-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Descreva o estágio **canary** e o rollback.
2. Como versionar artefatos de build?
3. Como registrar `trace_id` e `job_id` no pipeline?
4. Qual SLI de **TTC p50** alvo?
5. Como o DAG trata falhas de ingestão?
6. Como watchers de **diffs** disparam issues?
7. Qual política para secrets em CI?
8. Como publicar vetores sem downtime?
9. Qual contrato de logs estruturados?
10. Como garantir reprodutibilidade da pipeline?
11. Como versionar DAGs?
12. Como medir sucesso de execução?
13. Como isolar ambientes (dev/stg/prod)?
14. Quais métricas vão ao painel?
15. Como lidar com APIs instáveis?
16. Como garantir idempotência em steps?
17. Como reconciliar estados parciais?
18. Como definir dependências entre jobs?
19. Como parametrizar janelas de ingestão?
20. Como controlar custo de execução?
### QGen (20)
- Especifique stages do pipeline.
- Defina critérios de promoção.
- Modele rollback de feature flag.
- Escreva checklist de secrets.
- Crie métrica de sucesso por job.
- Desenhe DAG de ingestão RAG.
- Proponha política de retries.
- Crie contrato de logs.
- Especifique SLA de pipelines.
- Descreva auditoria de mudanças.
- Crie plano de testes de DAGs.
- Defina política de releases.
- Elabore script de dry‑run.
- Modele shards por região.
- Proponha estratégia de canary.
- Crie runbook de incidentes.
- Defina alerta de regressão.
- Escreva política de retenção.
- Crie plano de custos.
- Modele estrutura de artefatos.
### Hard‑negatives (10)
- CI sem rollback é aceitável.
- Logs estruturados são opcionais.
- TTC p50 não importa.
- Versionar DAG é supérfluo.
- Canary atrasa releases sem benefício.
- Secrets no repositório são ok.
- Vetores podem ser publicados com downtime.
- Reprodutibilidade não é necessária.
- Painéis de pipeline são desnecessários.
- Retries infinitos resolvem tudo.

---

## A14 — DS Product Engineering
### Tarefa YAML
```yaml
id: A14-DS-PE
competency: DS Product Engineering
priority: P2
why: entregar modelos como produto com SLAs
content_min: [api_contracts, data_contracts, exp_framework]
deps: [A13, A15]
license: MIT
```
### Conteúdo
- **API contracts** (versão, schema, compatibilidade retroativa).
- **Data contracts** (owner, SLAs, qualidade: freshness/completeness/consistência).
- **Experimentação**: framework A/B com guardrails (mínimo N, p‑value bounds, efeitos mínimos detectáveis).
- **Doc**: READMEs com uso, limites, SLO e exemplos.
### Evidence JSON
```json
{ "id": "A14-DS-PE-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A14-—-DS-Product-Engineering"],
  "vector_ids": ["a14-dspe-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Quais campos mínimos do **API contract**?
2. Como versionar o schema de resposta?
3. O que é **retrocompatibilidade**?
4. Quais dimensões de qualidade de dados?
5. Quem é o **owner** do dataset?
6. Como medir **freshness**?
7. Qual política para breaking changes?
8. Qual N mínimo para teste A/B?
9. Como definir efeito mínimo detectável?
10. Qual política de p‑value?
11. Como guardar **feature flags**?
12. Como documentar limites do modelo?
13. Como descrever SLO por endpoint?
14. Como expor exemplos de uso?
15. Como lidar com drift de schema?
16. Como versionar dados de treino?
17. Como reproduzir experimentos?
18. Como aprovar experimentos?
19. Como auditar resultados?
20. Como desativar experimento?
### QGen (20)
- Escreva contrato de API.
- Crie template de data contract.
- Modele checklist de breaking change.
- Proponha desenho de experimento.
- Defina N mínimo.
- Especifique EMD.
- Crie política de p‑value.
- Escreva guia de flags.
- Crie doc de limites do modelo.
- Defina SLO por endpoint.
- Escreva exemplos de uso.
- Modele detecção de drift.
- Crie versão de treino.
- Elabore protocolo de reprodutibilidade.
- Faça plano de aprovação.
- Esboce auditoria.
- Defina rollback de experimento.
- Crie tabela de métricas.
- Especifique owner/SLAs.
- Crie runbook de incidentes.
### Hard‑negatives (10)
- API não precisa de contrato.
- Breaking change pode ir direto.
- Qualidade de dados não é problema.
- Experimentos dispensam tamanho amostral.
- EMD é supérfluo.
- Retrocompatibilidade é opcional.
- Flags não precisam de controle.
- Documentação é dispensável.
- Drift de schema não afeta.
- Reprodutibilidade é irrelevante.

---

## A15 — MLOps & Monitoramento
### Tarefa YAML
```yaml
id: A15-MLOPS
competency: MLOps
priority: P1
why: confiabilidade e ciclo contínuo
content_min: [monitoring, retraining, model_registry]
deps: [A14, A16]
license: MIT
```
### Conteúdo
- **Monitoramento**: performance on/offline, drift, integridade, latência, erro.
- **Retraining**: gatilhos (drift/volume/tempo), canary, rollback.
- **Registry**: versionamento de modelos/artefatos, lineage, promoção.
- **SLOs**: p95 latência ≤ 800ms; erro ≤ 1.5% (ajuste por caso).
### Evidence JSON
```json
{ "id": "A15-MLOPS-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A15-—-MLOps-&-Monitoramento"],
  "vector_ids": ["a15-mlops-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Quais métricas on/offline?
2. Como detectar **drift**?
3. Quais gatilhos de retraining?
4. Como fazer canary de modelo?
5. Como versionar artefatos?
6. O que é lineage?
7. Como promover modelo?
8. Quais SLOs padrão?
9. Como medir latência?
10. Como medir erro?
11. Como gerar alertas?
12. Como correlacionar métricas?
13. Como lidar com dados faltantes?
14. Como fazer rollback?
15. Como testar compatibilidade?
16. Como armazenar features?
17. Como monitorar fairness?
18. Como monitorar custo?
19. Como proteger PII?
20. Como auditar mudanças?
### QGen (20)
- Descreva pipeline de monitoramento.
- Crie regra de drift.
- Especifique gatilhos de retraining.
- Proponha canary.
- Escreva plano de rollback.
- Modele versionamento de modelos.
- Defina lineage mínimo.
- Crie checklist de promoção.
- Especifique SLOs.
- Modele alertas.
- Crie painel de métricas.
- Defina tratamento de faltantes.
- Modele compatibilidade.
- Crie plano de fairness.
- Defina coleta de custos.
- Escreva política de PII.
- Crie trilha de auditoria.
- Modele testes offline.
- Defina janelas de agregação.
- Escreva contrato de storage.
### Hard‑negatives (10)
- Drift não precisa ser medido.
- Canary é desnecessário.
- Registry é supérfluo.
- Lineage não importa.
- SLOs são opcionais.
- Rollback não é necessário.
- PII não precisa de política.
- Custo não é medido.
- Fairness é irrelevante.
- Auditoria é dispensável.

---

## A16 — Deep Learning
### Tarefa YAML
```yaml
id: A16-DL
competency: Deep Learning
priority: P2
why: basear decisões em modelos robustos
content_min: [arch_choices, training_policy, eval_suite]
deps: [A15]
license: MIT
```
### Conteúdo
- **Arquiteturas**: seleção guiada por dados; ablação; trade‑offs.
- **Treino**: seeds fixas; mixed precision; early stop; regularização.
- **Avaliação**: suites por tarefa; benchmarks; robustez; OOD checks.
- **Lançe**: compatibilidade com APIs e registries (A14/A15).
### Evidence JSON
```json
{ "id": "A16-DL-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A16-—-Deep-Learning"],
  "vector_ids": ["a16-dl-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Como escolher arquitetura?
2. Quais seeds usar?
3. Por que mixed precision?
4. Quando parar treino?
5. Como regularizar?
6. Como avaliar robustez?
7. O que é OOD check?
8. Como comparar benchmarks?
9. Como garantir reprodutibilidade?
10. Como documentar hiperparâmetros?
11. Como gerenciar datasets?
12. Como prevenir vazamento de dados?
13. Como medir incerteza?
14. Como calibrar probabilidades?
15. Como checar fairness?
16. Como reduzir custo?
17. Como empacotar modelo?
18. Como validar em canary?
19. Como versionar datasets?
20. Como lidar com drift de distribuição?
### QGen (20)
- Projete ablação.
- Crie plano de seeds.
- Especifique mixed precision.
- Defina early stop.
- Modele regularização.
- Elabore suite de robustez.
- Descreva OOD checks.
- Crie tabela de benchmarks.
- Defina protocolo de reprodução.
- Especifique hiperparâmetros.
- Modele gestão de datasets.
- Crie política anti‑vazamento.
- Defina métricas de incerteza.
- Modele calibração.
- Crie plano de fairness.
- Otimize custo.
- Empacote modelo.
- Valide canary.
- Versione datasets.
- Tratamento de drift.
### Hard‑negatives (10)
- Seeds não importam.
- OOD é irrelevante.
- Robustez é opcional.
- Vazamento é raro e ignora‑se.
- Documentar hiperparâmetros é desnecessário.
- Benchmarks são perfumaria.
- Fairness não se aplica.
- Calibração é inútil.
- Reprodutibilidade não interessa.
- Ablação não agrega.

---

## A17 — Growth & Gamificação
### Tarefa YAML
```yaml
id: A17-GROWTH
competency: Growth
priority: P2
why: aquisição/ativação/retorno com ética
content_min: [funnel, experiments, gamification]
deps: [A14]
license: MIT
```
### Conteúdo
- **Funil**: aquisição→ativação→retenção→receita; métricas definidas.
- **Experimentos**: backlog priorizado; efeitos mínimos; poder estatístico.
- **Gamificação**: mecânicas transparentes; sem exploração.
- **Governança**: comitê de ética para features de influência.
### Evidence JSON
```json
{ "id": "A17-GROWTH-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A17-—-Growth-&-Gamificação"],
  "vector_ids": ["a17-growth-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Quais métricas do funil?
2. Como priorizar backlog?
3. Qual EMD por estágio?
4. Como garantir ética?
5. Como evitar dark patterns?
6. Como medir retenção?
7. Como testar gamificação?
8. Como tratar sazonalidade?
9. Como medir LTV?
10. Como medir CAC?
11. Como avaliar churn?
12. Como segmentar usuários?
13. Como lidar com VAR alto?
14. Como evitar p‑hacking?
15. Como documentar experimentos?
16. Como desligar feature nociva?
17. Como comunicar mudanças?
18. Como medir impacto real?
19. Como traduzir para statusboard?
20. Como auditar decisões?
### QGen (20)
- Crie painel do funil.
- Proponha priorização.
- Defina EMD.
- Escreva guia de ética.
- Liste anti‑padrões.
- Modele retenção.
- Especifique testes de gamificação.
- Crie ajuste sazonal.
- Modele LTV.
- Calcule CAC.
- Meça churn.
- Defina segmentos.
- Mitigue VAR.
- Prevenção p‑hacking.
- Template de documentação.
- Plano de kill‑switch.
- Comunicação de release.
- Atribuição de impacto.
- Export para painel.
- Auditoria periódica.
### Hard‑negatives (10)
- Dark patterns são aceitáveis.
- Ética atrapalha crescimento.
- EMD não é necessário.
- P‑hacking é válido.
- Documentação é supérflua.
- Kill‑switch é perda de tempo.
- LTV/CAC são irrelevantes.
- Sazonalidade ignora‑se.
- Segmentação é inútil.
- Auditoria não agrega.

---

## A18 — Psicologia & UX ética
### Tarefa YAML
```yaml
id: A18-PSI-UX
competency: Psicologia/UX
priority: P2
why: reduzir fricção sem manipular
content_min: [ethics, explainability, consent]
deps: [A17]
license: MIT
```
### Conteúdo
- **Ética**: princípios explícitos; proibição de dark patterns.
- **Explainability**: tooltips, exemplos, incerteza comunicada.
- **Consentimento**: granular; revogável; logs públicos.
- **Acessibilidade**: WCAG; linguagens simples.
### Evidence JSON
```json
{ "id": "A18-PSI-UX-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A18-—-Psicologia-&-UX-ética"],
  "vector_ids": ["a18-psiux-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Quais princípios éticos?
2. O que é dark pattern?
3. Como explicar incerteza?
4. Como registrar consentimento?
5. Como permitir revogação?
6. Como atender WCAG?
7. Como evitar over‑nudging?
8. Como avaliar clareza?
9. Como tratar público vulnerável?
10. Como medir compreensão?
11. Como documentar decisões?
12. Como auditar UX?
13. Como lidar com vieses?
14. Como responder a denúncias?
15. Como comunicar riscos?
16. Como proteger privacidade?
17. Como versionar textos?
18. Como traduzir termos?
19. Como equilibrar objetivos?
20. Como treinar equipe?
### QGen (20)
- Escreva código de ética.
- Crie checklist anti‑padrões.
- Modele explicações.
- Especifique consentimento.
- Crie logs públicos.
- Defina critérios WCAG.
- Avalie nudges.
- Medição de clareza.
- Plano para vulneráveis.
- Métrica de compreensão.
- Template de decisões.
- Protocolo de auditoria.
- Plano anti‑viés.
- Fluxo de denúncias.
- Guia de riscos.
- Política de privacidade.
- Versionamento de cópia.
- Guia de tradução.
- Trade‑offs.
- Treinamento.
### Hard‑negatives (10)
- Dark patterns são eficientes e ok.
- Consentimento não precisa ser revogável.
- WCAG é opcional.
- Explicar incerteza confunde.
- Logs públicos não são necessários.
- Vieses não importam.
- Denúncias podem ser ignoradas.
- Privacidade é secundária.
- Clareza não precisa ser medida.
- Treinamento é desnecessário.

---

## A19 — Banking & Reconciliação
### Tarefa YAML
```yaml
id: A19-BANK-REC
competency: Banking
priority: P1
why: consistência de saldos e liquidações
content_min: [recon, settlement, reserves]
deps: [A01, A04]
license: MIT
```
### Conteúdo
- **Reconciliação** diária por moeda (Δ tolerado, D+1 às 12:00 BRT).
- **Reservas** segregadas; prova pública; pausas & reconciliação.
- **Settlement**: trilhas de auditoria; filas; prioridades.
- **Falhas**: incident playbook e comunicação.
### Evidence JSON
```json
{ "id": "A19-BANK-REC-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A19-—-Banking-&-Reconciliação"],
  "vector_ids": ["a19-bankrec-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Como reconciliar por moeda?
2. Qual o horário de corte?
3. Como provar reservas?
4. Como pausar em divergência?
5. Como priorizar filas?
6. Como auditar settlement?
7. Como lidar com estornos?
8. Como registrar exceções?
9. Como lidar com bancos múltiplos?
10. Como tratar FX?
11. Como segregar contas?
12. Como comunicar incidentes?
13. Como detectar fraude?
14. Como versionar políticas?
15. Como tratar chargebacks?
16. Como monitorar aging?
17. Como lidar com disputas?
18. Como controlar limites?
19. Como gerir credenciais?
20. Como integrar com painéis?
### QGen (20)
- Escreva plano de reconciliação.
- Defina SLA de corte.
- Crie prova de reservas.
- Modele pausa automática.
- Desenhe fila de settlement.
- Protocolo de auditoria.
- Fluxo de estorno.
- Registro de exceções.
- Multi‑banco.
- Política de FX.
- Segregação de contas.
- Comunicação.
- Detecção de fraude.
- Versão de políticas.
- Chargebacks.
- Aging.
- Disputas.
- Limites.
- Gestão de credenciais.
- Painéis.
### Hard‑negatives (10)
- Reconciliação pode ser semanal.
- Reservas não precisam de prova.
- Pausas são desnecessárias.
- Filas não precisam de prioridade.
- Auditoria é perfumaria.
- Estornos não precisam de processo.
- Multi‑banco é trivial e sem riscos.
- FX não precisa de política.
- Limites podem ser ignorados.
- Disputas se resolvem sozinhas.

---

## A20 — Compliance
### Tarefa YAML
```yaml
id: A20-COMPL
competency: Compliance
priority: P1
why: conformidade legal e operacional
content_min: [kyc_aml, policies, reporting]
deps: [A19]
license: MIT
```
### Conteúdo
- **KYC/KYB/AML**: políticas e SLAs; listas negativas.
- **Relatórios**: regulatórios por jurisdição; logs públicos mínimos.
- **Políticas**: pausas; resposta a autoridades; armazenamento WORM.
- **Auditoria**: externa periódica; trilhas de acesso.
### Evidence JSON
```json
{ "id": "A20-COMPL-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A20-—-Compliance"],
  "vector_ids": ["a20-compl-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Quais documentos de KYC/KYB?
2. Como operar AML?
3. Como lidar com listas negativas?
4. Como gerar relatórios?
5. Como armazenar WORM?
6. Como responder a ordens legais?
7. Como logar acessos?
8. Como versionar políticas?
9. Como medir SLAs?
10. Como tratar vazamento de dados?
11. Como auditar externamente?
12. Como lidar com consentimento?
13. Como tratar dados sensíveis?
14. Como reportar incidentes?
15. Como treinar equipe?
16. Como gerir provedores?
17. Como monitorar compliance?
18. Como integrar com banking?
19. Como publicar logs mínimos?
20. Como manter trilhas de auditoria?
### QGen (20)
- Template de KYC/KYB.
- Playbook AML.
- Política de listas negativas.
- Relatório regulatório.
- Procedimento WORM.
- Guia de ordens legais.
- Esquema de logs.
- Versionamento de políticas.
- KPIs de SLA.
- Plano anti‑vazamento.
- Auditoria externa.
- Consentimento.
- Dados sensíveis.
- Incidentes.
- Treinamento.
- Provedores.
- Monitoração.
- Integração.
- Logs públicos.
- Trilhas.
### Hard‑negatives (10)
- KYC/KYB é opcional.
- AML é burocracia sem valor.
- WORM é desnecessário.
- Logs de acesso são supérfluos.
- Vazamentos não precisam de resposta.
- Políticas sem versão são ok.
- SLAs não importam.
- Auditoria externa é dispensável.
- Consentimento não precisa de gestão.
- Incidentes não precisam de reporte.

---

## A21 — Prediction Markets
### Tarefa YAML
```yaml
id: A21-PMKT
competency: Prediction Markets
priority: P2
why: preços que refletem evidências
content_min: [market_design, scoring_rules, oracle_integration]
deps: [A10, A15]
license: MIT
```
### Conteúdo
- **Design**: leilões/AMMs; anti‑colusão; liquidez mínima.
- **Scoring rules**: Brier/log; calibração; market maker.
- **Oráculos**: atestações regionais; disputa/bonds/slashing.
- **Integração**: preço de leilão prevalece; score modula limites.
### Evidence JSON
```json
{ "id": "A21-PMKT-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A21-—-Prediction-Markets"],
  "vector_ids": ["a21-pmkt-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Como garantir liquidez mínima?
2. Quais regras de scoring?
3. Como calibrar probabilidades?
4. Como evitar colusão?
5. Como lidar com manipulação?
6. Como integrar oráculos?
7. Como resolver disputas?
8. Como medir acurácia?
9. Como reduzir variância?
10. Como precificar mercados finos?
11. Como definir fees?
12. Como lidar com choques?
13. Como tratar eventos ambíguos?
14. Como encerrar mercado?
15. Como punir má‑fé?
16. Como fazer KYC?
17. Como publicar histórico?
18. Como auditar oráculos?
19. Como limitar risco?
20. Como integrar com score?
### QGen (20)
- Desenhe AMM.
- Defina regras de scoring.
- Proponha calibração.
- Anti‑colusão.
- Mitigação de manipulação.
- Integração de oráculos.
- Procedimento de disputa.
- Métricas de acurácia.
- Redução de variância.
- Precificação de finos.
- Política de fees.
- Choques.
- Encerramento.
- Sanções.
- KYC.
- Histórico.
- Auditoria.
- Limites de risco.
- Integração com score.
- Painel de mercados.
### Hard‑negatives (10)
- Liquidez não importa.
- Colusão é rara e ignora‑se.
- Disputas não precisam de regra.
- Calibração é opcional.
- Oráculos não precisam de auditoria.
- Acurácia não se mede.
- Fees irrelevantes.
- Choques não exigem política.
- Risco sem limites é ok.
- Score não precisa integrar.

---

## A22 — Documentação & Governança
### Tarefa YAML
```yaml
id: A22-DOC-GOV
competency: Governança
priority: P1
why: reprodutibilidade e auditabilidade
content_min: [jobs_ledger, contracts, naming_units]
deps: [A01, A10]
license: MIT
```
### Conteúdo
- **Jobs Ledger**: promessa/resultado/medida; links para PRs.
- **Contratos**: Job Contract (frase‑promessa, outcomes, evidências, gates, fallback).
- **Naming/Units**: glossário; unidades; tabelas de abreviações.
- **Lint**: checks na CI para links/metas e métricas de job.
### Evidence JSON
```json
{ "id": "A22-DOC-GOV-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A22-—-Documentação-&-Governança"],
  "vector_ids": ["a22-docgov-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. O que é Jobs Ledger?
2. O que vai no Job Contract?
3. Como linkar PRs?
4. Como medir outcomes?
5. Quais gates aplicar?
6. Qual fallback?
7. Como padronizar nomes?
8. Como definir unidades?
9. Como validar glossário?
10. Como rodar lint?
11. Como punir violações?
12. Como versionar contratos?
13. Como expor publicamente?
14. Como auditar mudanças?
15. Como treinar autores?
16. Como detectar duplicatas?
17. Como resolver conflitos?
18. Como atualizar referências?
19. Como integrar com statusboards?
20. Como medir cobertura de docs?
### QGen (20)
- Modelo de Jobs Ledger.
- Template de Job Contract.
- Script de link de PRs.
- Métricas de outcomes.
- Gates por tipo.
- Plano de fallback.
- Guia de naming.
- Tabela de unidades.
- Validador de glossário.
- Lint na CI.
- Política disciplinar.
- Versionamento.
- Publicação.
- Auditoria.
- Treinamento.
- Deduplicação.
- Consolidação.
- Atualização cross‑refs.
- Export para painéis.
- Métrica de cobertura.
### Hard‑negatives (10)
- Ledger é opcional.
- Contratos não precisam de versão.
- PRs não devem linkar jobs.
- Outcomes não precisam de medida.
- Gates são burocracia.
- Fallback não é necessário.
- Naming não precisa padronizar.
- Unidades podem variar.
- Glossário é supérfluo.
- Lint na CI é exagero.

---

## A23 — Glossário & Naming
### Tarefa YAML
```yaml
id: A23-GLOSS-NAMING
competency: Documentação
priority: P2
why: reduzir ambiguidade
content_min: [glossary, units, abbreviations]
deps: [A22]
license: MIT
```
### Conteúdo
- **Glossário**: termos (HWM, CC, RC, LE Escrow, S‑Claims, ELO‑P/C, URI WORM...).
- **Unidades**: ms, %, ACT/365, R$·dia.
- **Abreviações**: tabela normativa.
- **Processo**: PRs exigem mapeamento; CI falha se ausente.
### Evidence JSON
```json
{ "id": "A23-GLOSS-01", "artifact_paths": ["/kb/blocos/bloco_03_a13_a23_final_v3_00.md#A23-—-Glossário-&-Naming"],
  "vector_ids": ["a23-gloss-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Quais termos nucleares?
2. Quais unidades padrão?
3. Como atualizar glossário?
4. Como validar termos?
5. Como tratar sinônimos?
6. Como padronizar abreviações?
7. Como exigir mapeamento em PR?
8. Como travar CI por ausência?
9. Como lidar com conflitos de termos?
10. Como versionar glossário?
11. Como traduzir termos?
12. Como medir cobertura?
13. Como integrar com docs?
14. Como tratar depreciações?
15. Como publicar?
16. Como referenciar?
17. Como detectar ambiguidade?
18. Como treinar autores?
19. Como auditar mudanças?
20. Como garantir consistência?
### QGen (20)
- Crie lista de termos.
- Tabela de unidades.
- Processo de atualização.
- Validador automático.
- Dicionário de sinônimos.
- Padrão de abreviações.
- Template de PR.
- Regra de CI.
- Política de conflitos.
- Versionamento.
- Guia de tradução.
- Métrica de cobertura.
- Integração com docs.
- Depreciações.
- Publicação.
- Citações.
- Detector de ambiguidade.
- Treinamento.
- Auditoria.
- Consistência.
### Hard‑negatives (10)
- Glossário é opcional.
- Unidades podem variar.
- Mapeamento em PR é supérfluo.
- CI não deve travar.
- Conflitos se resolvem sozinhos.
- Tradução é desnecessária.
- Cobertura não precisa ser medida.
- Depreciação não precisa de política.
- Auditoria é perfumaria.
- Consistência é irrelevante.

---

# 6) Evidence JSON — **agregado** (KPIs por pipeline)
```json
{
  "block_id": "B03-A13-A23",
  "packs": [
    "A13-AUTO-01","A14-DS-PE-01","A15-MLOPS-01","A16-DL-01",
    "A17-GROWTH-01","A18-PSI-UX-01","A19-BANK-REC-01","A20-COMPL-01",
    "A21-PMKT-01","A22-DOC-GOV-01","A23-GLOSS-01"
  ],
  "kpis": { "mrr": null, "ndcg": null, "coverage": null, "leakage": null },
  "timestamps": { "executed_at": null }
}
```

---

# 7) Runbook — Ingestão & Testes
```bash
# 1) Ingestão
make ingest BLOCK=A13-A23

# 2) Probes + QGen + Hard-negatives
actions/run_probes.sh --block A13-A23 --qgen 20 --hardneg 10

# 3) Evidence JSON (merge de resultados)
python ops/tests/merge_evidence.py --block A13-A23 --out ops/tests/evidence/A13-A23.json

# 4) Atualizar front-matter (rag_kpis) via script
actions/update_rag_kpis.py --evidence ops/tests/evidence/A13-A23.json --pack kb/blocos/bloco_03_a13_a23_final_v3_00.md
```

---

# 8) Regras de Maturidade (auto)
```yaml
maturity_rules:
  to_silver: { require: [evidence_json.pass, rag_kpis.filled], golden_notebook: false }
  to_gold:   { require: [watchers.extended_ok, conflicts.none, incident_playbook.if_applicable] }
```

---

# 9) Conflitos & Duplicidades
```yaml
conflicts_report:
  path: "/ops/reports/conflicts_A13-A23.md"
  policy: merge_or_issue
  overlaps: ["A1 Personas/JTBD", "A22 Naming/Units"]
```

---

# 10) Closeout — sintético/demonstrativo
```json
{
  "block_id": "B03-A13-A23",
  "packs": ["A13-AUTO-01","A14-DS-PE-01","A15-MLOPS-01","A16-DL-01","A17-GROWTH-01","A18-PSI-UX-01","A19-BANK-REC-01","A20-COMPL-01","A21-PMKT-01","A22-DOC-GOV-01","A23-GLOSS-01"],
  "kpis": {"mrr": 0.48, "ndcg": 0.70, "coverage": 0.86, "leakage": 0.00},
  "proof_coverage_ratio": 0.82,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "causal": {"gate_ok": ["C1","C2","C4"]},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```

---

# 11) Auditoria final v3.1
- Front‑matter com `rag_kpis=null` ✅  
- `snippet_budget_lines=200` ✅  
- Packs A13–A23 completos (conteúdo + Evidence + QGen/Probes/HN) ✅  
- Watchers catálogo+parâmetros ✅  
- Runbook de ingestão/testes ✅  
- Conflitos & duplicidades ✅  
- Closeout sintético ✅  
- **Sem placeholders** ✅

