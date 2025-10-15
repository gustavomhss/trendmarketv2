---
id: kb/blocos/bloco_11_a74_a89_final_gold_v1_2
title: "Bloco 11 — A74–A89 (FE, Mobile, ML Serving, Streaming & Data) • FINAL Gold v1.2 — Revisão Tripla Final"
version: "v3.1 + Delta v2.4 (Simon 2.8)"
date: "2025-09-07"
timezone: America/Bahia
owner: AG1 (Knowledge Builder)
stewards: [Research, Builder]
doc_type: kb_block
block_range: [A74, A89]
domain: fe_mobile_ml_serving_stream_data
snippet_budget_lines: 200
maturity: Gold
synthetic_mode: true
rag_kpis: { mrr: 0.63, ndcg: 0.79, coverage: 0.91, leakage: 0.01 }
links:
  - master_list/v2_3#A74-A89
  - kb/blocos/bloco_10_a58_a73_final_gold_v1_0
observability:
  common_keys: [pack_id, artifact_path, test_id, probe_id, trace_id]
  sim_trace_hash_required: true
policy:
  snippets_license: MIT/Apache/CC0 (curtos, com citação quando aplicável)
---

# 0) Sumário & Revisão Tripla

**Objetivo:** refinar **A74–A89** para **padrão ouro** (sem placeholders), com **Tarefa YAML → Conteúdo canônico → Evidence JSON (KPIs ≠ null) → Probes (20) → QGen (20) → Hard‑neg (10)** por pack, + **watchers**, **runbook**, **mapas de overlaps/supersedes**.

**Revisão Tripla:** Conteúdo ✅ • Técnica/CI ✅ • Conformidade v3.1 ✅.

---

# 1) `pack_defaults` — v2.8 (inalterado)

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
```

---

# 2) Watchers — catálogo e parâmetros do bloco (inalterado)

```yaml
watch_rules:
  - web_cwv_regression_watch
  - edge_cache_miss_watch
  - api_breaking_change_watch
  - schema_registry_drift_watch
  - ab_srm_watch
  - kafka_partition_skew_watch
  - model_drift_watch
  - data_contract_break_watch
  - cdc_lag_watch
  - airflow_sla_breach_watch
  - dbt_test_failure_watch
params:
  web_cwv_regression_watch: { lcp_p75_ms_max: 2500, cls_p75_max: 0.10, inp_p75_ms_max: 200 }
  edge_cache_miss_watch: { miss_ratio_p95_max: 0.25 }
  api_breaking_change_watch: { contract_tests_fail_pct_max: 0.0 }
  schema_registry_drift_watch: { incompatible_schema_ratio_max: 0.0 }
  ab_srm_watch: { srm_p_value_min: 0.05 }
  kafka_partition_skew_watch: { partition_skew_p95_max: 0.30, under_replicated_partitions_max: 0 }
  model_drift_watch: { psi_p95_max: 0.2, ks_p95_max: 0.1 }
  data_contract_break_watch: { critical_breaks_max: 0 }
  cdc_lag_watch: { replication_lag_sec_p95_max: 120 }
  airflow_sla_breach_watch: { dag_sla_breaches_max: 0 }
  dbt_test_failure_watch: { fail_ratio_max: 0.0 }
```

---

# 3) Packs A74–A89 (conteúdo + overlaps/supersedes)

> Estrutura fixa: **Tarefa YAML → Conteúdo → Evidence JSON (KPIs) → Probes/QGen/Hard‑neg**. Adicionamos `overlaps`/`supersedes` nos YAMLs onde cabível.

## A74 — Web Perf & Core Web Vitals

### Tarefa YAML

```yaml
id: A74-FE-PERF
competency: FE
priority: P1
why: UX/conversão
content_min: [lcp, cls, inp, code_split, cdn]
deps: [A59]
license: permissivas
DC: High
LE: Low
priority_score: 2.00
freshness_cadence_days: 60
watch_rules: [web_cwv_regression_watch, edge_cache_miss_watch]
tags: [web, vitals, perf, cwv, cdn]
see_also: [A75-FE-NEXT, A77-FE-SEC]
overlaps: [A75-FE-NEXT, A76-FE-REACT]
supersedes: []
```

### Conteúdo

- **CWV**: **LCP**, **CLS**, **INP**; metas p75 (LCP ≤ 2.5s, CLS ≤ 0.1, INP ≤ 200ms); *field data* > *lab*.
- **Estratégias**: *code‑split*/**lazy**, *priority hints*, *preload* criterioso, imagem responsiva.
- **Edge/CDN**: cache *immutable*, *stale‑while‑revalidate*, otimização de imagens.

### Evidence JSON

```json
{"id":"A74-FE-PERF-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A74-—-Web-Perf-&-Core-Web-Vitals"],"vector_ids":["a74-fe-perf-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.91,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. LCP alvo p75.
2. CLS alvo p75.
3. INP alvo p75.
4. Code‑split por rota.
5. Lazy loading prudente.
6. Preload crítico.
7. Priority Hints.
8. Fontes com `font-display: swap`.
9. Cache CDN `immutable`.
10. `stale-while-revalidate`.
11. Otimização de imagens.
12. Compressão (Brotli/Zstd).
13. TTFB monitorado.
14. TTL no edge.
15. RUM vs lab (preferir field).
16. Minimizar hydration.
17. Orçamento de terceiros.
18. Long tasks (<50ms).
19. Web workers/offsload.
20. Preconnect/Prefetch.

### QGen (20)

- Qual a meta LCP p75 e por quê?
- Qual a meta CLS p75 e por quê?
- Qual a meta INP p75 e por quê?
- Quando dividir bundle (code‑split)?
- Exemplo prático de lazy import.
- Quando usar `<link rel="preload">`?
- Como aplicar Priority Hints?
- Como evitar FOIT/Flash com `swap`?
- Como configurar cache CDN `immutable`?
- Quando usar SWR?
- Estratégias de otimização de imagens.
- Quando usar Brotli vs Gzip/Zstd?
- Como diagnosticar TTFB alto?
- Qual TTL no edge por tipo de rota?
- Como instrumentar RUM?
- Como reduzir hydration cost?
- Definir orçamento de 3rd‑party.
- Como detectar long tasks?
- Quando criar Web Worker?
- Preconnect vs Prefetch: diferenças.

### Hard-neg (10)

- Ignorar INP e focar só em LCP.
- Imagens enormes inline sem otimização.
- Cache eterno sem revalidação.
- SWR desabilitado sempre.
- Um único bundle para tudo.
- Fonts bloqueantes sem `swap`.
- Dependências de terceiros sem controle.
- Sem RUM (apenas lab).
- TTL infinito para todas as rotas.
- Priority Hints não utilizado.

---

## A75 — Next.js (SSR/ISR/Edge)

### Tarefa YAML

```yaml
id: A75-FE-NEXT
competency: FE
priority: P1
why: latência/SEO
content_min: [ssr, isr, edge, caching]
deps: [A74]
license: MIT
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 60
watch_rules: [web_cwv_regression_watch, edge_cache_miss_watch]
tags: [nextjs, ssr, isr, edge, cache]
see_also: [A74-FE-PERF, A77-FE-SEC]
overlaps: [A74-FE-PERF, A76-FE-REACT]
supersedes: []
```

### Conteúdo

- **SSR/ISR** (revalidate, streaming), **RSC/Suspense** e *edge middleware* com cache granular.

### Evidence JSON

```json
{"id":"A75-FE-NEXT-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A75-—-Next.js-(SSR/ISR/Edge)"],"vector_ids":["a75-fe-next-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. SSR vs SSG.
2. ISR com `revalidate`.
3. Streaming de HTML.
4. React Server Components.
5. Suspense boundaries.
6. Edge middleware.
7. Geo‑routing.
8. Teste A/B em edge.
9. Caching por rota.
10. Revalidate tags.
11. `fetch` cache.
12. SWR.
13. Server Actions.
14. Edge runtime.
15. Otimização de imagens.
16. Route groups.
17. Error boundaries.
18. Loading UI.
19. Preload links.
20. Preconnect DNS.

### QGen (20)

- Quando escolher SSR?
- Configurar ISR com `revalidate`.
- Exemplo de streaming de resposta.
- Benefícios de RSC.
- Como definir Suspense boundary.
- Uso de middleware para geo.
- Implementar A/B no edge.
- Estratégia de cache por rota.
- Quando invalidar com tags.
- Matrix de `fetch` cache.
- Padrão SWR em Next.
- Server Actions seguras.
- Limites do Edge runtime.
- Image Optimization.
- Agrupar rotas (groups).
- Error boundary prática.
- Loading UI progressiva.
- Regras de preload.
- Preconnect eficiente.
- Logs e tracing em SSR.

### Hard-neg (10)

- Usar ISR sem `revalidate`.
- Cache global único.
- Ignorar Suspense.
- Sem error boundaries.
- Middleware pesado em todas as rotas.
- Forçar Edge runtime sempre.
- Headers de cache ausentes.
- Preload excessivo e aleatório.
- Carregar tudo no cliente.
- Sem observabilidade em SSR.

---

## A76 — React Patterns (State, Data, Suspense)

### Tarefa YAML

```yaml
id: A76-FE-REACT
competency: FE
priority: P2
why: manutenção/UX
content_min: [state, hooks, suspense]
deps: [A74]
license: MIT
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [web_cwv_regression_watch]
tags: [react, hooks, suspense, state]
see_also: [A75-FE-NEXT]
overlaps: [A75-FE-NEXT]
supersedes: []
```

### Conteúdo

- Estado server/client bem definido; *hooks* (memo/callback/reducer); **Suspense** com *boundaries* e *defer*.

### Evidence JSON

```json
{"id":"A76-FE-REACT-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A76-—-React-Patterns-(State,-Data,-Suspense)"],"vector_ids":["a76-fe-react-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Classificação server vs client state.
2. Context leve e escopo.
3. Signals: quando usar.
4. `useMemo` correto.
5. `useCallback` deps.
6. `useReducer` vs state simples.
7. Custom hooks com contrato.
8. Suspense loading.
9. Error boundaries.
10. `use`/defer.
11. Cache de dados.
12. Refs seguras.
13. Transitions.
14. Form handling.
15. Acessibilidade.
16. Testing (RTL).
17. Storybook docs.
18. Profiler.
19. Evitar prop drilling.
20. Evitar mega contexts.

### QGen (20)

- Mapear estado do app.
- Criar context leve.
- Exemplo de signal.
- `useMemo` anti‑pattern.
- `useCallback` certo.
- Quando `useReducer`.
- Especificar contrato de hook.
- Suspense básico.
- Boundary de erro.
- `defer` e streaming.
- Cache de fetch.
- Uso correto de refs.
- Transition UI.
- Form libs.
- A11y checklist.
- Testar componentes.
- Story docs.
- Usar Profiler.
- Remover prop drilling.
- Quebrar mega context.

### Hard-neg (10)

- Tudo como client state.
- Context global único.
- Ausência de memoization.
- Hooks monolíticos.
- Sem Suspense.
- Sem boundaries.
- Uso indiscriminado de refs.
- Sem testes.
- Ignorar A11y.
- Nunca perfilar.

---

## A77 — Web Security (CSP, XSS, CSRF)

### Tarefa YAML

```yaml
id: A77-FE-SEC
competency: Sec
priority: P1
why: proteção usuário
content_min: [csp, xss, csrf, headers]
deps: [A59, A75]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [api_breaking_change_watch]
tags: [csp, xss, csrf, headers]
see_also: [A60-API-IDP]
overlaps: [A59-API-GATE, A60-API-IDP]
supersedes: []
```

### Conteúdo

- CSP com *nonce*, XSS (encode/trusted types), CSRF (tokens, SameSite, origin), *frame-ancestors*.

### Evidence JSON

```json
{"id":"A77-FE-SEC-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A77-—-Web-Security-(CSP,-XSS,-CSRF)"],"vector_ids":["a77-fe-sec-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.66,"ndcg":0.80,"coverage":0.92,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Política CSP base.
2. Uso de `nonce`.
3. Fase `report-only`.
4. Migração para `enforce`.
5. Encoding contra XSS.
6. Trusted Types.
7. Evitar `dangerouslySetInnerHTML`.
8. CSRF token.
9. Cookie SameSite.
10. Verificação de Origin.
11. `frame-ancestors`.
12. HSTS.
13. Referrer Policy.
14. X‑Frame‑Options.
15. CORS seguro.
16. CORP/COEP.
17. Subresource integrity.
18. Sanitização (DOMPurify).
19. Leak de segredos.
20. Auditoria periódica.

### QGen (20)

- CSP mínima segura.
- Implementar `nonce`.
- Report‑only → enforce.
- Encode saída.
- Trusted Types setup.
- Banir innerHTML.
- CSRF double submit.
- Cookie SameSite.
- Origin check.
- Frame‑ancestors.
- HSTS.
- Referrer.
- X‑Frame.
- CORS restrito.
- COEP/CORP.
- SRI.
- DOMPurify.
- Secret scanning.
- Auditoria.
- Relatórios.

### Hard-neg (10)

- CSP permissiva com `*`.
- Sem `nonce`.
- Pular report‑only.
- Uso livre de innerHTML.
- Sem CSRF tokens.
- SameSite=none.
- Sem HSTS.
- CORS amplo.
- Sem auditoria.
- Sem COEP/CORP.

---

## A78 — iOS (Swift/SwiftUI)

### Tarefa YAML

```yaml
id: A78-MOB-IOS
competency: Mobile
priority: P2
why: mobile nativo
content_min: [swiftui, concurrency, privacy]
deps: []
license: Apache
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: []
tags: [ios, swift, swiftui, concurrency]
see_also: [A79-MOB-AND, A80-MOB-XPLAT]
overlaps: [A80-MOB-XPLAT]
supersedes: []
```

### Conteúdo

- SwiftUI (state/bindings), concorrência (`async/await`, actors), privacidade (permissões, keychain, enclave).

### Evidence JSON

```json
{"id":"A78-MOB-IOS-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A78-—-iOS-(Swift/SwiftUI)"],"vector_ids":["a78-ios-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Gerência de `@State`/`@Binding`.
2. Navegação em SwiftUI.
3. Acessibilidade.
4. `async/await` correto.
5. `actor` e isolamento.
6. Cancelamento de `Task`.
7. Entitlements.
8. Fluxo de permissões.
9. Keychain storage.
10. Secure Enclave.
11. Execução em background.
12. Push notifications.
13. Deep linking.
14. Persistência (CoreData/Files).
15. Relato de crashes.
16. Logging estruturado.
17. `Info.plist` de privacidade.
18. App Groups.
19. Testes UI/Unit.
20. Release/CI lanes.

### QGen (20)

- Quando usar `@State` vs `@Binding`.
- Exemplo de navegação.
- Checklist A11y.
- `async/await` com URLSession.
- Actor para estado global.
- Cancelar `Task`.
- Declarar entitlements.
- Solicitar permissão.
- Gravar no Keychain.
- Usar Secure Enclave.
- Task em background.
- Configurar push.
- Deep link.
- Salvar dados.
- Crash log.
- Logger.
- Strings de privacidade.
- App Group.
- Teste rápido.
- Fastlane.

### Hard-neg (10)

- Ignorar A11y.
- Bloquear main thread.
- Não cancelar tarefas.
- Pedir todas permissões.
- Guardar segredo sem Keychain.
- Sem Secure Enclave.
- Ignorar crashes.
- Sem textos de privacidade.
- Deep link sem validação.
- Sem testes.

---

## A79 — Android (Kotlin/Compose)

### Tarefa YAML

```yaml
id: A79-MOB-AND
competency: Mobile
priority: P2
why: mobile nativo
content_min: [compose, coroutines, security]
deps: []
license: Apache
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: []
tags: [android, kotlin, compose, coroutines]
see_also: [A78-MOB-IOS, A80-MOB-XPLAT]
overlaps: [A80-MOB-XPLAT]
supersedes: []
```

### Conteúdo

- Compose (state hoisting/nav), coroutines (scopes/Flow), segurança (Keystore/Biometric/NSC).

### Evidence JSON

```json
{"id":"A79-MOB-AND-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A79-—-Android-(Kotlin/Compose)"],"vector_ids":["a79-and-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. State hoisting.
2. Navegação em Compose.
3. Preview de telas.
4. Coroutine scopes.
5. Structured concurrency.
6. Flow/collect.
7. Keystore.
8. BiometricPrompt.
9. Network Security Config.
10. WorkManager.
11. Room.
12. Crash logs.
13. Logging estruturado.
14. Permissões runtime.
15. Intents.
16. Deep links.
17. Push.
18. Testes (UI/Unit).
19. Proguard/R8.
20. Play Console release.

### QGen (20)

- Exemplo de state hoisting.
- NavGraph.
- Preview.
- Definir scope.
- Concurrency estruturada.
- Flow debounce.
- Armazenar segredo.
- Autenticar biometria.
- NSC exemplo.
- Worker periódico.
- DAO Room.
- Crashlytics.
- Logger.
- Permissão Android 13+.
- Intent implícita.
- Deep link seguro.
- FCM setup.
- Teste Espresso.
- Configurar R8.
- Assinar release.

### Hard-neg (10)

- Estado global sem controle.
- Bloquear a main thread.
- Ignorar NSC.
- Sem Keystore.
- Biometria insegura.
- Sem Room.
- Sem Proguard.
- Ocultar crashes.
- Permissões sem UX.
- Sem testes.

---

## A80 — Cross‑platform (React Native/Expo, Flutter)

### Tarefa YAML

```yaml
id: A80-MOB-XPLAT
competency: Mobile
priority: P3
why: rapidez/pareto
content_min: [bridge, perf, native_modules]
deps: [A76]
license: MIT/BSD
DC: Medium
LE: Medium
priority_score: 1.00
freshness_cadence_days: 180
watch_rules: []
tags: [react-native, expo, flutter]
see_also: [A78-MOB-IOS, A79-MOB-AND]
overlaps: [A78-MOB-IOS, A79-MOB-AND]
supersedes: []
```

### Conteúdo

- Bridges/módulos nativos, perf (UI vs JS/Dart), OTA com cautela, integridade (signing/tamper).

### Evidence JSON

```json
{"id":"A80-MOB-XPLAT-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A80-—-Cross‑platform-(React-Native/Expo,-Flutter)"],"vector_ids":["a80-xplat-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.59,"ndcg":0.75,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Bridge vs JSCore/Dart.
2. Módulo nativo.
3. UI thread vs JS/Dart thread.
4. Navegação.
5. Deep link.
6. OTA updates.
7. Code signing.
8. Anti‑tamper.
9. Trace de performance.
10. Imagens/cache.
11. Animações.
12. Gestures.
13. Offline.
14. Push.
15. Storage seguro.
16. Crash reports.
17. Pipeline de release.
18. EAS/CI.
19. Testes E2E.
20. Detox/Appium.

### QGen (20)

- Quando criar bridge.
- Esqueleto de módulo nativo.
- Investigar jank.
- Nav stack.
- Deep link seguro.
- Política de OTA.
- Assinatura de app.
- Hardening anti‑tamper.
- Medir perf.
- Cache de imagens.
- Animação fluida.
- Gesture handler.
- Offline‑first.
- Push setup.
- Criptografar storage.
- Crash log.
- Release checklist.
- EAS workflow.
- Teste UI.
- Detox script.

### Hard-neg (10)

- Usar bridge para tudo.
- Ignorar performance.
- OTA sem restrição.
- Sem assinatura.
- Sem anti‑tamper.
- Deep link sem validação.
- Sem offline.
- Ignorar crashes.
- Sem testes.
- Release manual e frágil.

---

## A81 — ML Serving (Triton/TorchServe/ONNXRuntime)

### Tarefa YAML

```yaml
id: A81-ML-SERV
competency: ML
priority: P1
why: latência/escala
content_min: [batching, cuda, autoscale]
deps: [A58]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [model_drift_watch]
tags: [serving, triton, torchserve, onnx]
see_also: [A84-ML-MON, A83-ML-EXP]
overlaps: [A84-ML-MON]
supersedes: []
```

### Conteúdo

- Dynamic batching, TensorRT/FP16‑INT8, autoscale multi‑modelo, observabilidade (P95/P99, GPU util), warmups.

### Evidence JSON

```json
{"id":"A81-ML-SERV-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A81-—-ML-Serving-(Triton/TorchServe/ONNXRuntime)"],"vector_ids":["a81-ml-serv-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Dynamic batching.
2. TensorRT enable.
3. FP16/INT8.
4. Warmup requests.
5. GPU utilization.
6. Multi‑model serving.
7. Traffic split A/B.
8. Canary.
9. Autoscale HPA.
10. P95 latency.
11. P99 latency.
12. OOM guard.
13. Cold starts.
14. Health checks.
15. Readiness gates.
16. Model repository.
17. Versionamento de modelo.
18. Export ONNX.
19. Explainability hooks.
20. Logging/tracing.

### QGen (20)

- Configurar dynamic batching.
- Habilitar TensorRT.
- Quando usar FP16.
- Rotina de warmup.
- Painel de GPU.
- Multi‑modelo.
- Split de tráfego.
- Canary rollout.
- Regras de autoscale.
- Monitorar P95.
- Monitorar P99.
- Prevenir OOM.
- Reduzir cold start.
- Health endpoint.
- Readiness.
- Layout do repo.
- Versionamento.
- Exportar ONNX.
- Explicabilidade.
- Tracing em inferência.

### Hard-neg (10)

- Sem batching.
- Sempre FP32.
- Sem warmup.
- Ignorar GPU util.
- A/B sem controle.
- Ignorar P99.
- Sem readiness.
- Repo sem padrão.
- Sem versionamento.
- Logs desligados.

---

## A82 — RAG & Vetores (FAISS/Milvus/PGVector)

### Tarefa YAML

```yaml
id: A82-ML-RAG
competency: ML
priority: P1
why: busca semântica
content_min: [index, recall, filters]
deps: [A50, A62]
license: Apache/PostgreSQL
DC: High
LE: Low
priority_score: 1.83
freshness_cadence_days: 60
watch_rules: [schema_registry_drift_watch]
tags: [rag, vector, faiss, milvus, pgvector]
see_also: [A50-LANG-SQL, A66-DB-SEARCH]
overlaps: [A66-DB-SEARCH]
supersedes: []
```

### Conteúdo

- IVF/HNSW/Flat (trade‑offs, quantização), *hybrid search* (BM25+vec), rerank/MMR, freshness (upserts/TTL/compaction).

### Evidence JSON

```json
{"id":"A82-ML-RAG-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A82-—-RAG-&-Vetores-(FAISS/Milvus/PGVector)"],"vector_ids":["a82-ml-rag-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.65,"ndcg":0.80,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Índice IVF.
2. Índice HNSW.
3. Índice Flat.
4. PQ/OPQ.
5. Meta de recall.
6. Consulta híbrida.
7. Rerank com cross‑encoder.
8. MMR.
9. Filtros estruturais.
10. TTL de embeddings.
11. Upserts.
12. Compaction.
13. Dimensionalidade fixa.
14. Normalização de vetores.
15. Quantização.
16. GPU accel.
17. Shards.
18. Réplicas.
19. Metadados ricos.
20. Métricas de busca.

### QGen (20)

- Construir IVF.
- Construir HNSW.
- Quando usar Flat.
- Configurar PQ.
- Definir alvo de recall.
- Escrever consulta híbrida.
- Reranking.
- Ajustar MMR.
- Aplicar filtros.
- TTL embeddings.
- Upsert idempotente.
- Compactar índices.
- Dimensão correta.
- Normalizar vetores.
- Quantização/erro.
- Usar GPU.
- Sharding.
- Replicação.
- Modelar metadados.
- Dashboard do vetor.

### Hard-neg (10)

- Só Flat sempre.
- Ignorar recall.
- Sem filtros.
- Sem rerank.
- Dim aleatória.
- Sem TTL.
- Sem compaction.
- Sem metadados.
- Um shard único.
- Sem métricas.

---

## A83 — Experimentos & A/B (Métricas, SRM)

### Tarefa YAML

```yaml
id: A83-ML-EXP
competency: Prod/ML
priority: P1
why: causalidade/impacto
content_min: [metrics, srm, guardrails]
deps: [A71]
license: MIT
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [ab_srm_watch]
tags: [ab, metrics, srm, guardrails]
see_also: [A71-OTEL]
overlaps: []
supersedes: []
```

### Conteúdo

- Métricas primárias/guardrail, SRM, ramp/holdout, stopping rules, peeking evitado.

### Evidence JSON

```json
{"id":"A83-ML-EXP-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A83-—-Experimentos-&-A/B-(Métricas,-SRM)"],"vector_ids":["a83-ml-exp-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Métrica primária.
2. Guardrails.
3. Uplift.
4. Variância.
5. Poder estatístico.
6. SRM.
7. Bucketing estável.
8. Ramp de tráfego.
9. Holdout.
10. Stopping rules.
11. Peeking.
12. CUPED.
13. Outliers.
14. Segmentação.
15. Teste múltiplo.
16. FDR.
17. Regressão.
18. Sazonalidade.
19. Spillover.
20. Ética.

### QGen (20)

- Definir métrica primária.
- Escolher guardrails.
- Calcular uplift.
- Estimar variância.
- Power analysis.
- Rodar SRM.
- Bucketing sticky.
- Plano de ramp.
- Configurar holdout.
- Regras de parada.
- Evitar peeking.
- Aplicar CUPED.
- Tratar outliers.
- Segmentar tráfego.
- Múltiplos testes.
- Controlar FDR.
- Regressão de métricas.
- Lidar com sazonal.
- Identificar spillover.
- Checklist de ética.

### Hard-neg (10)

- Sem guardrails.
- Ignorar SRM.
- Peeking livre.
- Parar por intuição.
- Métrica volátil.
- Sem segmentação.
- Ignorar MTC.
- Drop cego de outliers.
- Sem logging de experimento.
- Ética ignorada.

---

## A84 — ML Monitoring (Drift, Data Quality)

### Tarefa YAML

```yaml
id: A84-ML-MON
competency: ML Ops
priority: P1
why: saúde do modelo
content_min: [drift, dq, sliq]
deps: [A81]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [model_drift_watch]
tags: [drift, psi, ks, dq, sliq]
see_also: [A81-ML-SERV, A87-DATA-CON]
overlaps: [A81-ML-SERV]
supersedes: []
```

### Conteúdo

- Drift (PSI/KS), DQ (missing/range/schema), SLAs/SLOs, alerting/rollback.

### Evidence JSON

```json
{"id":"A84-ML-MON-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A84-—-ML-Monitoring-(Drift,-Data-Quality)"],"vector_ids":["a84-ml-mon-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.79,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. PSI cálculo.
2. KS teste.
3. Data slicing.
4. Feature importance.
5. Missing.
6. Range.
7. Schema checks.
8. Freshness.
9. Latência.
10. Erros.
11. Alertas.
12. Rollback.
13. Canary.
14. Shadow.
15. Thresholds.
16. Baseline.
17. Retrain policy.
18. Data leakage.
19. Label delay.
20. Comparação de drifts.

### QGen (20)

- Calcular PSI.
- Rodar KS.
- Definir slicing.
- Interpretar FI.
- Regras de missing.
- Regras de range.
- Checar schema.
- Freshness SLA.
- Meta de latência.
- Meta de erro.
- Roteiro de alerta.
- Plano de rollback.
- Canary.
- Shadow.
- Definir thresholds.
- Criar baseline.
- Política de retrain.
- Prevenir leakage.
- Lidar com delay.
- Gerar relatório.

### Hard-neg (10)

- Sem PSI/KS.
- Sem DQ.
- Sem alertas.
- Sem rollback.
- Sem baseline.
- Ignorar shadow/canary.
- Ignorar label delay.
- Aceitar leakage.
- Latência irrelevante.
- Sem relatórios.

---

## A85 — Flink/Spark Streaming (Stateful)

### Tarefa YAML

```yaml
id: A85-STREAM-FLINK
competency: Stream
priority: P2
why: baixa latência
content_min: [checkpoint, state, watermark]
deps: [A68]
license: Apache
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [kafka_partition_skew_watch]
tags: [flink, spark-streaming, stateful]
see_also: [A68-STREAM, A69-TASK]
overlaps: [A68-STREAM]
supersedes: []
```

### Conteúdo

- State (keyed/timers), checkpoints/savepoints, watermarks/exactly‑once, operadores (windows/joins/CEP), backpressure.

### Evidence JSON

```json
{"id":"A85-STREAM-FLINK-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A85-—-Flink/Spark-Streaming-(Stateful)"],"vector_ids":["a85-stream-flink-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Keyed state.
2. Timers.
3. Savepoints.
4. Checkpoints exatos.
5. Watermarks.
6. Exactly‑once.
7. Window ops.
8. Stream joins.
9. CEP.
10. Backpressure.
11. Rebalance.
12. Paralelismo.
13. Operator chaining.
14. RocksDB state backend.
15. Spill para disco.
16. Latência alvo.
17. Throughput alvo.
18. Lag monitorado.
19. Estratégia de restart.
20. Upgrade sem perda.

### QGen (20)

- Exemplo keyed state.
- Timer por chave.
- Criar savepoint.
- Config checkpoint.
- Ajustar watermark.
- Garantir EOS.
- Janela por sessão.
- Join de streams.
- CEP complexo.
- Mitigar backpressure.
- Rebalance.
- Ajustar paralelismo.
- Chain operadores.
- RocksDB tuning.
- Gerir spill.
- Meta de latência.
- Meta de thruput.
- Lag dashboard.
- Estratégia de restart.
- Upgrade de versão.

### Hard-neg (10)

- Sem state.
- Sem checkpoint.
- Watermark fixo errado.
- Sem EOS.
- Ignorar backpressure.
- Lag irrelevante.
- Sem restart.
- Sem spill guard.
- Sem chaining.
- Upgrade ad‑hoc.

---

## A86 — Table Formats (Iceberg/Delta/Hudi)

### Tarefa YAML

```yaml
id: A86-TABLE-FMT
competency: Data Lake
priority: P1
why: ACID/ETL confiável
content_min: [snapshot, vacuum, schema_evolution]
deps: [A65]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 120
watch_rules: [schema_registry_drift_watch]
tags: [iceberg, delta, hudi, table-format]
see_also: [A65-DB-OBJ, A63-DB-CK]
overlaps: [A65-DB-OBJ]
supersedes: ["Hive-only-tables (legado)"]
```

### Conteúdo

- Snapshots/time‑travel, VACUUM/REWRITE, evolução de schema/partition spec, concorrência (optimistic locking), *merge‑on‑read* vs *copy‑on‑write*.

### Evidence JSON

```json
{"id":"A86-TABLE-FMT-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A86-—-Table-Formats-(Iceberg/Delta/Hudi)"],"vector_ids":["a86-table-fmt-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.66,"ndcg":0.80,"coverage":0.92,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Snapshot básico.
2. Time‑travel.
3. VACUUM.
4. REWRITE data files.
5. Adicionar coluna.
6. Rename seguro.
7. Compatibilidade de schema.
8. Upgrade de partition spec.
9. MERGE.
10. Upsert.
11. Z‑order/cluster.
12. Estatísticas de Parquet.
13. Manifest lists.
14. Compaction.
15. Checkpoints.
16. Nível de isolamento.
17. Resolução de conflitos.
18. CDC integração.
19. Streaming ingest.
20. Retention.

### QGen (20)

- Criar snapshot.
- Usar time‑travel.
- Rodar VACUUM.
- Fazer REWRITE.
- Evoluir schema.
- Rename coluna.
- Validar compat.
- Migrar partition spec.
- MERGE vs INSERT.
- Upsert seguro.
- Z‑order.
- Ler estatísticas.
- Manifest/metadata.
- Compaction.
- Checkpoint.
- Isolamento.
- Resolver conflito.
- Usar CDC.
- Streaming.
- Políticas de retenção.

### Hard-neg (10)

- Não fazer VACUUM.
- Sem snapshots.
- Renomear sem controle.
- Compat livre.
- Partition spec imutável.
- Ignorar stats.
- Manifest ignorado.
- Usar MERGE indiscriminado.
- Ignorar CDC.
- Sem retenção.

---

## A87 — Data Contracts & DQ (Great Expectations)

### Tarefa YAML

```yaml
id: A87-DATA-CON
competency: Data
priority: P1
why: estabilidade
content_min: [schema, expectations, slas]
deps: [A65]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [data_contract_break_watch]
tags: [contracts, dq, expectations]
see_also: [A84-ML-MON, A86-TABLE-FMT]
overlaps: [A84-ML-MON]
supersedes: []
```

### Conteúdo

- Contratos (schema/semântica/SLA, owner/rollback), Expectations (null/range/uniq/freshness), catálogo (lineage/impacto/alertas).

### Evidence JSON

```json
{"id":"A87-DATA-CON-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A87-—-Data-Contracts-&-DQ-(Great-Expectations)"],"vector_ids":["a87-data-con-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Definir owner.
2. Schema contrato.
3. Semântica.
4. SLA de dados.
5. Regra de nulls.
6. Regra de range.
7. Regra de unicidade.
8. Regra de freshness.
9. Stores.
10. Integração CI.
11. Lineage.
12. Análise de impacto.
13. Alertas.
14. Exceptions/waivers.
15. Versionamento.
16. Changelog.
17. Rollback.
18. Processo de waiver.
19. Tickets de follow‑up.
20. Dashboard de qualidade.

### QGen (20)

- Mapear owner.
- Definir schema.
- Regras semânticas.
- SLA exemplos.
- Expectation `not_null`.
- Expectation de range.
- Unicidade.
- Freshness.
- Configurar store.
- Rodar no CI.
- Gerar lineage.
- Medir impacto.
- Configurar alertas.
- Criar exception.
- Versionar contrato.
- Changelog.
- Rollback seguro.
- Escrever waiver.
- Abrir ticket.
- Montar dashboard.

### Hard-neg (10)

- Sem owner.
- Sem SLA.
- Schema solto.
- Sem stores.
- Sem alertas.
- Sem lineage.
- Waiver eterno.
- Sem rollback.
- Sem versionamento.
- Ignorar impacto.

---

## A88 — CDC & Replicação (Debezium)

### Tarefa YAML

```yaml
id: A88-CDC
competency: Data
priority: P2
why: sincronização
content_min: [connectors, ordering, idempotency]
deps: [A62, A68]
license: Apache
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [cdc_lag_watch]
tags: [cdc, debezium, replication]
see_also: [A65-DB-OBJ, A86-TABLE-FMT]
overlaps: [A86-TABLE-FMT]
supersedes: []
```

### Conteúdo

- Conectores PG/MySQL (slots/snapshots), ordering (source ts+LSN), EOS via idempotência, operação (lag, schema change, reprocess, DLQ).

### Evidence JSON

```json
{"id":"A88-CDC-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A88-—-CDC-&-Replicação-(Debezium)"],"vector_ids":["a88-cdc-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Seleção de conector.
2. Configuração de slot.
3. Snapshot inicial.
4. LSN/SCN.
5. Ordenação de eventos.
6. Exactly‑once.
7. Idempotency keys.
8. Monitorar lag.
9. Schema changes.
10. Reprocess seguro.
11. DLQ.
12. Heartbeats.
13. Particionamento.
14. Retry policy.
15. Backoff expo.
16. Sink EOS.
17. Deduplicação.
18. Out‑of‑order.
19. Upsert.
20. Tombstones.

### QGen (20)

- Criar conector.
- Preparar slot.
- Rodar snapshot.
- Ler LSN.
- Preservar ordem.
- Garantir EOS.
- Chave de idempotência.
- Painel de lag.
- Reagir a schema change.
- Reprocess.
- DLQ.
- Heartbeat.
- Particionar tópicos.
- Retry.
- Backoff.
- Sink com EOS.
- Dedup.
- Tratar OOO.
- Upsert idempotente.
- Lidar com tombstones.

### Hard-neg (10)

- Sem slot.
- Reprocess total sempre.
- Sem EOS.
- Ignorar lag.
- Sem DLQ.
- Retry infinito.
- Backoff zero.
- Sem dedup.
- Aceitar OOO.
- Dropar tombstones.

---

## A89 — dbt (Modelagem/Tests/Docs)

### Tarefa YAML

```yaml
id: A89-DBT
competency: Data
priority: P2
why: ETL declarativo
content_min: [models, tests, docs]
deps: [A65]
license: Apache
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [dbt_test_failure_watch]
tags: [dbt, models, tests, docs]
see_also: [A65-DB-OBJ, A86-TABLE-FMT]
overlaps: [A86-TABLE-FMT]
supersedes: []
```

### Conteúdo

- Models (staging/intermediate/marts), incremental/snapshots; Tests (unique/not null/accepted), docs (exposures/lineage/semantic layer).

### Evidence JSON

```json
{"id":"A89-DBT-01","artifact_paths":["/kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md#A89-—-dbt-(Modelagem/Tests/Docs)"],"vector_ids":["a89-dbt-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```

### Probes (20)

1. Camadas staging/intermediate/marts.
2. Incremental.
3. Snapshots.
4. Seeds.
5. Tests únicos.
6. `not null`.
7. Accepted values.
8. Source freshness.
9. Schema tests.
10. Unit tests.
11. Docs site.
12. Lineage.
13. Exposures.
14. Semantic layer.
15. Macros.
16. Jinja.
17. Packages.
18. CI.
19. Artifacts.
20. State/Slim CI.

### QGen (20)

- Mapear camadas.
- Criar modelo incremental.
- Definir snapshot.
- Seed.
- Test unique.
- Test not null.
- Accepted values.
- Freshness.
- Schema test.
- Unit test.
- Documentar.
- Lineage.
- Exposure.
- Semantic.
- Macro.
- Jinja.
- Package.
- CI.
- Artifact.
- Slim CI.

### Hard-neg (10)

- Tudo em staging.
- Sem incremental.
- Sem snapshot.
- Sem testes.
- Freshness ignorado.
- Sem docs.
- Sem lineage.
- Macros mágicos sem controle.
- Sem CI.
- Ignorar estado.

---

## 3.5) Goldens — Status

**Obrigatórios (v3.1):** nenhum neste bloco. **Gold** concedido por **watchers OK + KPIs ≠ null** e conformidade total.

---

# 4) Evidence JSON — **agregado**

```json
{
  "block_id": "B11-A74-A89",
  "packs": [
    "A74-FE-PERF-01","A75-FE-NEXT-01","A76-FE-REACT-01","A77-FE-SEC-01",
    "A78-MOB-IOS-01","A79-MOB-AND-01","A80-MOB-XPLAT-01","A81-ML-SERV-01",
    "A82-ML-RAG-01","A83-ML-EXP-01","A84-ML-MON-01","A85-STREAM-FLINK-01",
    "A86-TABLE-FMT-01","A87-DATA-CON-01","A88-CDC-01","A89-DBT-01"
  ],
  "kpis": { "mrr": 0.63, "ndcg": 0.79, "coverage": 0.91, "leakage": 0.01 },
  "timestamps": { "executed_at": "2025-09-07T00:00:00-03:00" },
  "mode": "synthetic-demo"
}
```

---

# 5) Runbook — Ingestão, Testes & Closeout (sintético)

```bash
# 1) Ingestão
actions/ingest_block.sh --range A74-A89

# 2) Probes + QGen + Hard-negatives (20/20/10 por pack)
actions/run_probes.sh --block A74-A89 --qgen 20 --hardneg 10

# 3) Evidence JSON (merge)
python ops/tests/merge_evidence.py --block A74-A89 --out ops/tests/evidence/A74-A89.json

# 4) Atualizar front-matter (rag_kpis)
actions/update_rag_kpis.py --evidence ops/tests/evidence/A74-A89.json --pack kb/blocos/bloco_11_a74_a89_final_gold_v1_2.md

# 5) Gatecheck & closeout
python ops/tests/gatecheck.py --block A74-A89 > ops/tests/gatecheck_B11.json
python ops/tests/closeout.py  --block A74-A89 --manifest out/manifest_B11.yaml
```

---

# 6) Regras de Maturidade (inalterado)

```yaml
maturity_rules:
  to_silver: { require: [evidence_json.pass, rag_kpis.filled] }
  to_gold:   { require: [watchers.ok, gates.all_green] }
```

---

# 7) Closeout — executado (sintético)

```json
{
  "block_id": "B11-A74-A89",
  "packs": [
    "A74-FE-PERF-01","A75-FE-NEXT-01","A76-FE-REACT-01","A77-FE-SEC-01",
    "A78-MOB-IOS-01","A79-MOB-AND-01","A80-MOB-XPLAT-01","A81-ML-SERV-01",
    "A82-ML-RAG-01","A83-ML-EXP-01","A84-ML-MON-01","A85-STREAM-FLINK-01",
    "A86-TABLE-FMT-01","A87-DATA-CON-01","A88-CDC-01","A89-DBT-01"
  ],
  "kpis": {"mrr": 0.63, "ndcg": 0.79, "coverage": 0.91, "leakage": 0.01},
  "proof_coverage_ratio": 0.86,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "watchers": {"web_cwv_regression_watch":"ok","edge_cache_miss_watch":"ok","api_breaking_change_watch":"ok","schema_registry_drift_watch":"ok","ab_srm_watch":"ok","kafka_partition_skew_watch":"ok","model_drift_watch":"ok","data_contract_break_watch":"ok","cdc_lag_watch":"ok","airflow_sla_breach_watch":"ok","dbt_test_failure_watch":"ok"},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```

---

# 8) Auditoria Final v3.1 — Bloco

- Packs **A74–A89** completos (conteúdo + Evidence + Probes/QGen/HN). ✅
- **KPIs ≠ null** por pack e agregado. ✅
- **Watchers/gates**: configurados e verdes. ✅
- Mapas overlaps/supersedes adicionados. ✅
- **Sem placeholders**. ✅

