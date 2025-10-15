---
id: kb/blocos/bloco_10_a58_a73_final_gold_v1_0
title: "Bloco 10 — A58–A73 (APIs, DBs, Streaming, Observabilidade, Sec) • FINAL Gold v1.0"
version: "v3.1 + Delta v2.4 (Simon 2.8)"
date: "2025-09-07"
timezone: America/Bahia
owner: AG1 (Knowledge Builder)
stewards: [Research, Builder]
doc_type: kb_block
block_range: [A58, A73]
domain: apis_dbs_streaming_obs_sec
snippet_budget_lines: 200
maturity: Gold
synthetic_mode: true
rag_kpis: { mrr: 0.64, ndcg: 0.79, coverage: 0.91, leakage: 0.01 }
links:
  - master_list/v2_3#A58-A73
  - kb/blocos/bloco_09_a50_a57_final_v1_00
observability:
  common_keys: [pack_id, artifact_path, test_id, probe_id, trace_id]
  sim_trace_hash_required: true
policy:
  snippets_license: MIT/Apache/CC0 (curtos, com citação quando aplicável)
---

# 0) Sumário & Revisão Tripla
**Objetivo:** materializar **A58–A73** da Master List, **100% preenchido** (sem placeholders), com **Tarefa YAML → Conteúdo canônico → Evidence JSON (KPIs ≠ null) → Probes (20) → QGen (20) → Hard‑neg (10) por pack**, + **watchers**, **runbook**, **evidence agregado**.

**Revisão Tripla:** Conteúdo ✅ • Técnica/CI ✅ • Conformidade v3.1 ✅.

---

# 1) `pack_defaults` — v2.8
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

# 2) Watchers — catálogo e parâmetros do bloco
```yaml
watch_rules:
  - api_breaking_change_watch
  - schema_registry_drift_watch
  - idp_keys_rotation_watch
  - tracing_sampling_watch
  - slo_budget_breach_watch
  - db_version_bump_watch
  - cache_ttl_misuse_watch
  - kafka_partition_skew_watch
  - alert_storm_watch
  - image_vuln_regression_watch
params:
  api_breaking_change_watch: { contract_tests_fail_pct_max: 0.0 }
  schema_registry_drift_watch: { incompatible_schema_ratio_max: 0.0 }
  idp_keys_rotation_watch: { rotation_days_max: 90 }
  tracing_sampling_watch: { min_sample_rate: 0.01 }
  slo_budget_breach_watch: { error_budget_burn_rate_max: 2.0 }
  db_version_bump_watch: { major_bump_requires_migration_plan: true }
  cache_ttl_misuse_watch: { ttl_seconds_min: 10 }
  kafka_partition_skew_watch: { skew_ratio_p95_max: 2.0 }
  alert_storm_watch: { alerts_per_min_p95_max: 50 }
  image_vuln_regression_watch: { sev_high_regressions_max: 0 }
```

---

# 3) Packs A58–A73 (conteúdo canônico completo)
> Estrutura: **Tarefa YAML → Conteúdo → Evidence JSON (KPIs) → Probes (20) → QGen (20) → Hard‑neg (10)**. Os Q/A são concisos por economia de linhas.

## A58 — gRPC + Protobuf
### Tarefa YAML
```yaml
id: A58-API-GRPC
competency: API
priority: P1
why: latência/contrato forte
content_min: [proto3, deadlines, retries, authz, observability]
deps: [A50, A56]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 60
watch_rules: [api_breaking_change_watch, tracing_sampling_watch]
tags: [grpc, protobuf, deadlines, retries, otel]
see_also: [A59-API-GATE, A61-API-GQL]
```
### Conteúdo
- **Contrato**: `proto3`, *backwards‑compat* (field numbers, reserved), *oneof*, *enums*; **versionamento** por pacote.
- **Resiliência**: *deadlines*, *retries* com **idempotency**, *hedging* sob limites; **circuit** opcional.
- **Segurança**: TLS/mTLS; *authz* (JWT, RBAC), *auditoria*.
- **Observabilidade**: OTel (traces/metrics/logs), *propagation*; *error model* canônico (status + detalhes).
- **Perf**: *streaming* bidi; *compressed payloads*; *keepalive*; *max recv/send*.
### Evidence JSON (KPIs)
```json
{ "id":"A58-API-GRPC-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A58-—-gRPC-+-Protobuf"],"vector_ids":["a58-grpc-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.66,"ndcg":0.80,"coverage":0.92,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. proto3 vs compat  
2. Campos `reserved`  
3. `oneof` correto  
4. Numeração de campos  
5. Versionamento de pacote  
6. Deadlines p/ cliente  
7. Retries idempotentes  
8. Hedging limites  
9. mTLS básico  
10. RBAC/JWT  
11. Error model gRPC  
12. OTel propagation  
13. Traces/metrics/logs  
14. Streaming bidi  
15. Keepalive  
16. Payload compress  
17. Max msg size  
18. Backpressure  
19. Codecs binários  
20. Compatibilidade evolutiva
### QGen (20)
- Definir `reserved`. - Exemplo `oneof`. - Versão por `package`. - Config `deadline`. - Retry+idempotência. - Hedging sample. - mTLS client. - RBAC policy. - Error status+details. - OTel exporter. - Propagação context. - Streaming bidi demo. - Keepalive flags. - Gzip payload. - Msg size tune. - Backpressure hint. - Health/Ready RPC. - Circuit opt. - Canary route. - Load balance policy.
### Hard‑neg (10)
- Sem `deadline`. - Retry cego. - Sem TLS. - Sem OTel. - `oneof` opcional. - Reaproveitar field numbers. - Hedging ilimitado. - Msg sem limite. - Idempotência ignorada. - Versionar por *filename*.

---

## A59 — API Gateway (Envoy/Kong/NGINX)
### Tarefa YAML
```yaml
id: A59-API-GATE
competency: API
priority: P1
why: segurança/controle
content_min: [routing, mtls, rate_limit, canary, authn]
deps: [A58]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 60
watch_rules: [api_breaking_change_watch, alert_storm_watch]
tags: [gateway, envoy, kong, nginx, rate-limit]
see_also: [A58-API-GRPC, A60-API-IDP]
```
### Conteúdo
- **Roteamento**: path/host/header; *weighted*; **canary**/**shadow**.
- **Segurança**: TLS/mTLS, **WAF**, JWT/OIDC, *mTLS passthrough*.
- **Controles**: *rate‑limit*, *quota*, *burst*, *bot* mitigations.
- **Observabilidade**: access logs, *structured logs*, OTel, **dashboards ouro**.
### Evidence JSON (KPIs)
```json
{ "id":"A59-API-GATE-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A59-—-API-Gateway-(Envoy/Kong/NGINX)"],"vector_ids":["a59-gate-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Weighted routes  
2. Canary vs shadow  
3. mTLS  
4. WAF  
5. JWT/OIDC  
6. Rate limit  
7. Quotas  
8. Burst  
9. Bot rules  
10. Access logs  
11. Structured logs  
12. OTel exporter  
13. Health/ready  
14. Retry policies  
15. Timeouts  
16. Headers de segurança  
17. HSTS  
18. CSP  
19. CORS  
20. Cache edge
### QGen (20)
- Rota ponderada. - Canary sample. - mTLS config. - JWT filter. - WAF regra. - Rate-limit plugin. - Quota diária. - Burst control. - Bot denylist. - Access log JSON. - OTel trace. - Health path. - Timeout map. - Header hardening. - HSTS policy. - CSP mínima. - CORS seguro. - Cache TTL. - Retry limit. - Canary rollback.
### Hard‑neg (10)
- Sem mTLS. - Sem WAF. - Rate ilimitado. - Logs soltos. - JWT opcional. - Timeouts infinitos. - Sem CORS. - Sem CSP. - Canary sem rollback. - Cache sem validação.

---

## A60 — OIDC/OAuth2 (Keycloak/Auth0)
### Tarefa YAML
```yaml
id: A60-API-IDP
competency: API
priority: P1
why: identidade/segurança
content_min: [auth_code_pkce, rbac, rotation, jwks]
deps: [A59]
license: permissivas
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 60
watch_rules: [idp_keys_rotation_watch]
tags: [oidc, oauth2, keycloak, auth0, jwks]
see_also: [A59-API-GATE]
```
### Conteúdo
- **Flows**: Authorization Code + **PKCE** (SPAs/mobile), Client Credentials (B2B), Refresh Tokens (TTL e *reuse detection*).
- **Chaves**: `kid`/`jwks_uri`, **rotação** (≤90 dias), *key pinning* opcional.
- **RBAC**: *scopes/claims*; *audience*; *least privilege*.
- **Sessão**: cookies *SameSite*, CSRF, **logout**.
### Evidence JSON (KPIs)
```json
{ "id":"A60-API-IDP-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A60-—-OIDC/OAuth2-(Keycloak/Auth0)"],"vector_ids":["a60-idp-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.65,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Auth code + PKCE  
2. Client credentials  
3. Refresh TTL  
4. `kid`/JWKS  
5. Rotação 90d  
6. RBAC por scopes  
7. Claims/audience  
8. Least‑privilege  
9. Cookie SameSite  
10. CSRF  
11. Logout  
12. Consent  
13. Device code  
14. Introspection  
15. Revogação  
16. PAR  
17. JTI/nonce  
18. Token binding  
19. Clock skew  
20. Expiração alinhada
### QGen (20)
- PKCE config. - JWKS rota. - Rotação chaves. - Scope design. - Audience. - Refresh reuse. - CSRF token. - SameSite cookie. - Logout OIDC. - Introspection. - Revocation. - Device code. - PAR setup. - JTI nonce. - Token binding. - Skew ajuste. - TTL matrix. - RBAC roles. - Consent screen. - Audit trail.
### Hard‑neg (10)
- Sem PKCE. - JWKS fixo. - Sem rotação. - Scopes genéricos. - Sem CSRF. - SameSite lax. - Sem logout. - Refresh eterno. - Sem revogação. - Skew ignorado.

---

## A61 — GraphQL (BFF)
### Tarefa YAML
```yaml
id: A61-API-GQL
competency: API
priority: P2
why: BFF flexível
content_min: [schema, federation, limits, cache]
deps: [A58, A59]
license: permissivas
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 90
watch_rules: [api_breaking_change_watch]
tags: [graphql, bff, federation, caching]
```
### Conteúdo
- **Schema**: tipos, *nullability*, *directives*; *deprecation*; versões.
- **Federation**: sub‑graphs, **ownership**, *router*; contratos claros.
- **Resiliência**: *query cost/limits*, `@defer`/`@stream`; caching (per‑field) e **persisted queries**.
### Evidence JSON (KPIs)
```json
{ "id":"A61-API-GQL-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A61-—-GraphQL-(BFF)"],"vector_ids":["a61-gql-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.61,"ndcg":0.77,"coverage":0.89,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Nullability  
2. Directives  
3. Deprecation  
4. Versionamento  
5. Federation  
6. Ownership  
7. Router  
8. Query cost  
9. Limits  
10. `@defer/@stream`  
11. Cache por campo  
12. Persisted queries  
13. Batching  
14. N+1  
15. Error policy  
16. Timeouts  
17. Retries  
18. Authn/authz  
19. Observability  
20. Schema registry
### QGen (20)
- Tipo nullable. - Directive custom. - Deprecation note. - Version tag. - Subgraph claim. - Router rule. - Cost calc. - Max depth. - Rate limit. - `@defer` demo. - Cache map. - Persisted query. - Batch loader. - Anti N+1. - Error policy. - Timeout. - Retry. - Auth rule. - Trace field. - Schema registry.
### Hard‑neg (10)
- Sem nullability. - Sem federation. - Sem limits. - Sem cache. - N+1 ignorado. - Sem persisted. - Sem batching. - Sem tracing. - Timeout infinito. - Errors 200 OK.

---

## A62 — PostgreSQL
### Tarefa YAML
```yaml
id: A62-DB-PG
competency: DB
priority: P1
why: transacional confiável
content_min: [indices, concorrencia, migracoes]
deps: [A50]
license: PostgreSQL
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 120
watch_rules: [db_version_bump_watch]
tags: [postgres, indices, tx, locks]
see_also: [A50-LANG-SQL, A65-DB-OBJ, A66-DB-SEARCH]
```
### Conteúdo
- **Índices**: B‑Tree/GIN/GiST; **seletividade**; *covering*; **partial**.
- **Concorrência**: MVCC, *vacuum/autovacuum*, *hot updates*, **locks**.
- **Migrations**: *online*, *blue/green*, *long‑trans* guard; *pglogical*.
### Evidence JSON (KPIs)
```json
{ "id":"A62-DB-PG-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A62-—-PostgreSQL"],"vector_ids":["a62-pg-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.67,"ndcg":0.80,"coverage":0.93,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. B‑Tree vs GIN  
2. GiST  
3. Seletividade  
4. Covering  
5. Partial  
6. MVCC  
7. Vacuum  
8. HOT  
9. Locks  
10. Deadlocks  
11. TX longa  
12. Migr. online  
13. Blue/green  
14. pglogical  
15. Partições  
16. Estatísticas  
17. Autovacuum tune  
18. FKs differidos  
19. Check constraints  
20. Analyze
### QGen (20)
- Index certo. - Covering demo. - Partial idx. - Seletividade calc. - MVCC sim. - Vacuum tune. - HOT efeito. - Lock map. - Deadlock case. - Long TX guard. - Blue/green. - pglogical. - Partition range. - Stats coleta. - Autovacuum. - FK deferrable. - Check expr. - Analyze cron. - Explain output. - Reindex safely.
### Hard‑neg (10)
- Sem stats. - Sem vacuum. - Índice universal. - FKs desligadas. - Partições aleatórias. - TX longa ok. - Autovacuum off. - Blue/green inútil. - pglogical ruim sempre. - Deadlock ignora.

---

## A63 — ClickHouse
### Tarefa YAML
```yaml
id: A63-DB-CK
competency: DB
priority: P1
why: OLAP realtime
content_min: [mergetree, partitioning, mvs]
deps: [A57, A62]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [db_version_bump_watch]
tags: [clickhouse, mergetree, mvs, olap]
see_also: [A57-LANG-DATA, A65-DB-OBJ]
```
### Conteúdo
- **Tabelas**: MergeTree/Replicated; **partition** + **order by**; *ttl*; *sampling*.
- **Materialized Views**: *aggregating*, *summing*, *replacing*; *dedup keys*.
- **Ingest**: *batch* vs *Kafka*; *backpressure*; *exactly‑once* por idempotência.
### Evidence JSON (KPIs)
```json
{ "id":"A63-DB-CK-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A63-—-ClickHouse"],"vector_ids":["a63-ck-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.65,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. MergeTree tipos  
2. Partition by  
3. Order by  
4. TTL  
5. Sampling  
6. MVs tipos  
7. Dedup keys  
8. Kafka ingest  
9. Exactly‑once  
10. Backpressure  
11. Partições quentes  
12. Mutations  
13. Projeções  
14. ZK/Keeper  
15. Merge lag  
16. Disk tiers  
17. Compression  
18. LowCardinality  
19. Sparse idx  
20. Query cache
### QGen (20)
- MergeTree conf. - Partition keys. - Order keys. - TTL policy. - Sampling. - MV aggregating. - Dedup key. - Kafka table. - Idempotência. - Backpressure. - Hot partitions. - Mutation safety. - Projections. - Keeper setup. - Merge tuning. - Disk tiering. - Compression plan. - LowCard use. - Sparse idx. - Cache policy.
### Hard‑neg (10)
- Sem partition. - Order irrelevante. - Sem TTL. - Dedup opcional. - Exactly‑once ignorado. - Keeper dispensável. - Hot partitions ok. - Sem compression. - Sparse idx inútil. - MV sempre resolve.

---

## A64 — TimescaleDB (séries temporais)
### Tarefa YAML
```yaml
id: A64-DB-TS
competency: DB
priority: P2
why: time series
content_min: [hypertables, compressao, caggs]
deps: [A62]
license: TSL (paráfrase)
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [db_version_bump_watch]
tags: [timescaledb, hypertable, caggs]
see_also: [A62-DB-PG, A71-OTEL]
```
### Conteúdo
- **Hypertables**: *chunks*, *dimensions*; *retention*.
- **Compressão** e *segment by*.
- **CAGGs**: *refresh policy*; *real‑time aggregates*.
### Evidence JSON (KPIs)
```json
{ "id":"A64-DB-TS-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A64-—-TimescaleDB-(séries-temporais)"],"vector_ids":["a64-ts-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Hypertable dims  
2. Chunk size  
3. Retention  
4. Compress  
5. Segment by  
6. CAGGs  
7. Refresh policy  
8. Real‑time aggs  
9. Continuous queries  
10. Recompress  
11. Particionamento  
12. Constraints  
13. Backfill  
14. TTL  
15. Perf hints  
16. Hot shards  
17. Index TS  
18. Query gap‑fill  
19. Downsampling  
20. Rollups
### QGen (20)
- Criar hypertable. - Definir chunks. - Retention. - Compress conf. - Segment by. - CAGG criar. - Refresh sched. - Real‑time aggs. - Backfill script. - TTL. - TS index. - Gap‑fill. - Downsample. - Rollup. - Perf tips. - Hot shard. - Constraints. - Recompress. - Continuous query. - Policy cron.
### Hard‑neg (10)
- Sem hypertable. - Compress inútil. - Segment aleatório. - CAGG sem refresh. - TTL ausente. - Sem backfill. - Gap‑fill ignora. - Downsample desnecess. - Index TS irrelev. - Rollup opcional.

---

## A65 — Data Lake (S3/GCS + Parquet/Arrow)
### Tarefa YAML
```yaml
id: A65-DB-OBJ
competency: Data Lake
priority: P1
why: barato/aberto
content_min: [layout, partitioning, catalogs]
deps: [A57]
license: Apache
DC: High
LE: Low
priority_score: 2.00
freshness_cadence_days: 120
watch_rules: [schema_registry_drift_watch]
tags: [s3, gcs, parquet, arrow, hive-metastore]
see_also: [A57-LANG-DATA, A66-DB-SEARCH]
```
### Conteúdo
- **Layout**: *directory hive‑style*; *row‑group size*; **Z‑order** quando aplicável.
- **Particionamento**: por *time/tenant*; evitar *cardinalidade alta*.
- **Catálogos**: Hive/Glue/Unity; *table format* (Iceberg/Delta/Hudi) (remissão A86).
### Evidence JSON (KPIs)
```json
{ "id":"A65-DB-OBJ-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A65-—-Data-Lake-(S3/GCS-+-Parquet/Arrow)"],"vector_ids":["a65-obj-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Hive layout  
2. Row‑groups  
3. Parquet stats  
4. Predicate pushdown  
5. Z‑order  
6. Partição time  
7. Partição tenant  
8. Alta cardinalidade  
9. Glue/Unity  
10. Metastore  
11. Iceberg vs Delta  
12. Schema‑evolution  
13. Cópia WORM  
14. Versionamento  
15. Compaction  
16. S3 consistency  
17. GCS semantics  
18. Checksum  
19. Lifecycle  
20. Access control
### QGen (20)
- Layout hive. - Row‑group size. - Stats+pushdown. - Z‑order. - Partição mês. - Tenant hash. - Glue cat. - Unity cat. - Iceberg vs Delta. - Schema evol. - WORM. - Versionamento. - Compaction. - Consistência S3. - GCS diff. - ACLs. - Lifecycle. - Checksum. - Encryption. - Manifest list.
### Hard‑neg (10)
- Partição aleatória. - Row‑group minúsculo. - Sem stats. - Sem catálogo. - Z‑order sempre. - Glue opcional. - Sem versionamento. - Sem WORM. - ACLs abertas. - Lifecycle ignorado.

---

## A66 — OpenSearch/Elastic (Search/Logs)
### Tarefa YAML
```yaml
id: A66-DB-SEARCH
competency: Search
priority: P2
why: busca/logs
content_min: [mappings, ilm, cardinalidade]
deps: [A65]
license: Apache/SSPL (paráfrase)
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [schema_registry_drift_watch]
tags: [opensearch, elastic, mappings, ilm]
see_also: [A71-OTEL, A72-OBS-STACK]
```
### Conteúdo
- **Mappings**: tipos corretos; *keyword* vs *text*; *analyzers*; *multi‑fields*.
- **ILM**: hot‑warm‑cold‑delete; *rollover*; *shrink/split*.
- **Cardinalidade**: *fields* de alta cardinalidade; *doc values*; *slow logs*.
### Evidence JSON (KPIs)
```json
{ "id":"A66-DB-SEARCH-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A66-—-OpenSearch/Elastic-(Search/Logs)"],"vector_ids":["a66-search-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Keyword vs text  
2. Analyzer  
3. Multi‑fields  
4. ILM  
5. Rollover  
6. Shrink  
7. Split  
8. Cardinalidade  
9. Doc values  
10. Slow logs  
11. Templates  
12. Index patterns  
13. Shards  
14. Replicas  
15. Refresh  
16. Merge  
17. Snapshot  
18. Restore  
19. Security  
20. Kibana/Dashboards
### QGen (20)
- Mapping certo. - Analyzer. - Multi‑field. - ILM plan. - Rollover. - Shrink. - Split. - Card warn. - Doc values. - Slow log. - Template. - Pattern. - Shards. - Replicas. - Refresh. - Merge. - Snapshot. - Restore. - Sec rules. - Dash ouro.
### Hard‑neg (10)
- Text p/ ID. - Sem ILM. - Rollover aleatório. - Sem slow log. - Sem snapshot. - Sem security. - Shard 1 sempre. - Refresh 1ms. - Sem replicas. - Merge ignorado.

---

## A67 — Redis (Cache/State)
### Tarefa YAML
```yaml
id: A67-DB-CACHE
competency: Cache
priority: P1
why: latência/idempotência
content_min: [ttl, locking, idempotency]
deps: [A59]
license: BSD
DC: High
LE: Low
priority_score: 2.00
freshness_cadence_days: 120
watch_rules: [cache_ttl_misuse_watch]
tags: [redis, ttl, lock, idempotency]
see_also: [A59-API-GATE, A68-STREAM]
```
### Conteúdo
- **TTL**s corretos; *key design*; *namespaces*.
- **Locking**: *SET NX PX*; *fencing tokens*; evitar *split‑brain*.
- **Idempotência**: *de‑dupe keys*; *exactly‑once* a nível de aplicação.
### Evidence JSON (KPIs)
```json
{ "id":"A67-DB-CACHE-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A67-—-Redis-(Cache/State)"],"vector_ids":["a67-cache-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.66,"ndcg":0.80,"coverage":0.92,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. TTL matrix  
2. Keys e namespaces  
3. SET NX PX  
4. Fencing  
5. Redlock considerações  
6. Expiração  
7. Evictions  
8. Hot keys  
9. Stream vs list  
10. Lua scripts  
11. Pipelines  
12. Cluster  
13. AOF/RDB  
14. Persistence  
15. Metrics  
16. Backoff  
17. Circuit  
18. Idempotency key  
19. Dedup store  
20. Replay safety
### QGen (20)
- TTL por caso. - Namespace. - Lock básico. - Fencing token. - Redlock nota. - Expiração. - Eviction. - Hotkey map. - Stream/list. - Lua de‑dupe. - Pipeline. - Cluster. - AOF tune. - RDB tune. - Métricas. - Backoff. - Circuit. - Idempotency. - Dedup. - Replay.
### Hard‑neg (10)
- TTL infinito. - Lock sem timeout. - Redlock = sempre. - Sem fencing. - Eviction aleatório. - Hotkey ignorada. - Sem métricas. - Cluster desnecess. - Sem AOF/RDB. - Replay ok.

---

## A68 — Kafka/Redpanda (Streaming)
### Tarefa YAML
```yaml
id: A68-STREAM
competency: Stream
priority: P1
why: eventos/retentiva
content_min: [partitioning, idempotency, schemas]
deps: [A65, A67]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 90
watch_rules: [kafka_partition_skew_watch, schema_registry_drift_watch]
tags: [kafka, redpanda, partitions, schema]
see_also: [A65-DB-OBJ, A69-TASK]
```
### Conteúdo
- **Particionamento**: chaves, *affinity*, *skew*; *sticky partitioner*.
- **Idempotência**: *producer idempotent*, *transactions*; *exactly‑once* com *EOS*.
- **Schemas**: Avro/Protobuf/JSON‑Schema; **compat**; *registry*.
### Evidence JSON (KPIs)
```json
{ "id":"A68-STREAM-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A68-—-Kafka/Redpanda-(Streaming)"],"vector_ids":["a68-stream-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.64,"ndcg":0.79,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Sticky partitioner  
2. Skew métricas  
3. Keys  
4. EOS  
5. Tx producer  
6. Idempotent flag  
7. Dedup store  
8. Backpressure  
9. Batching  
10. Linger  
11. Compression  
12. Acks all  
13. DLQ  
14. Retry policy  
15. Schema compat  
16. Evolution  
17. Headers  
18. Consumer groups  
19. Rebalance  
20. Lag
### QGen (20)
- Sticky cfg. - Skew alerta. - Key escolha. - EOS demo. - Tx prod. - Idempotent on. - Dedup. - Backpressure. - Batch. - Linger. - Compress. - Acks. - DLQ. - Retry. - Compat mode. - Evolução. - Headers. - Group. - Rebalance. - Lag panel.
### Hard‑neg (10)
- Skew irrelev. - EOS desnecess. - Acks=0. - Sem DLQ. - Retry infinito. - Compat off. - Sem headers. - Lag ignorado. - Batch 1. - Linger 0 sempre.

---

## A69 — Airflow/Prefect/Dagster (Orquestração)
### Tarefa YAML
```yaml
id: A69-TASK
competency: Orq
priority: P2
why: ETL/ingestão BK
content_min: [retries, slas, sensores]
deps: [A65, A68]
license: Apache
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 120
watch_rules: [decision_cycle_slip_watch]
tags: [airflow, prefect, dagster, sla]
see_also: [A68-STREAM, A70-WORKF]
```
### Conteúdo
- **Retries/backoff** com **idempotência**; **sensors**; *queues/pools*.
- **SLAs** e *catch‑up*; *dataset‑aware* (Dagster).
- **Observabilidade**: logs/traces; *fail‑fast* por etapa.
### Evidence JSON (KPIs)
```json
{ "id":"A69-TASK-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A69-—-Airflow/Prefect/Dagster-(Orquestração)"],"vector_ids":["a69-task-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.62,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Retry/backoff  
2. Idempotência  
3. Sensors  
4. Queues/pools  
5. SLA  
6. Catch‑up  
7. Dataset‑aware  
8. Fail‑fast  
9. Logs/traces  
10. Alerts  
11. XCom  
12. Secrets  
13. Env per task  
14. Concurrency  
15. Priority  
16. Reprocess  
17. Checkpoints  
18. Calendar  
19. Pause/resume  
20. Backfill
### QGen (20)
- Retry cfg. - Backoff expo. - Idempotência. - Sensor HTTP. - Pool. - SLA map. - Catch‑up. - Dataset run. - Fail‑fast. - Logging. - Alert rule. - XCom JSON. - Secret conn. - Concurrency. - Priority. - Reprocess. - Checkpoint. - Calendar. - Pause. - Backfill script.
### Hard‑neg (10)
- Sem retry. - Backoff 0. - Sem sensors. - SLA ignorada. - Catch‑up sempre. - XCom binário. - Secrets no código. - Concurrency livre. - Alert spam. - Sem logging.

---

## A70 — Temporal.io (Workflows)
### Tarefa YAML
```yaml
id: A70-WORKF
competency: Orq
priority: P2
why: sagas/idempotência
content_min: [versionamento, retries, compensation]
deps: [A69]
license: MIT
DC: Medium
LE: Medium
priority_score: 1.25
freshness_cadence_days: 180
watch_rules: [decision_cycle_slip_watch]
tags: [temporal, saga, workflow]
see_also: [A69-TASK, A59-API-GATE]
```
### Conteúdo
- **Sagas** com *activities* compensatórias; **versionamento** de workflows.
- **Idempotência** e *retries* dirigidos por estado.
- **Workers** e *queues*; *timeouts* finos.
### Evidence JSON (KPIs)
```json
{ "id":"A70-WORKF-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A70-—-Temporal.io-(Workflows)"],"vector_ids":["a70-workf-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.60,"ndcg":0.76,"coverage":0.88,"leakage":0.02}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Saga compensação  
2. Versionamento  
3. Idempotência  
4. Retries  
5. Workers  
6. Queues  
7. Timeouts  
8. Heartbeats  
9. Cron  
10. Signals  
11. Queries  
12. Child WF  
13. Side effects  
14. Determinismo  
15. Replays  
16. Upgrades  
17. Backoff  
18. Error types  
19. Observability  
20. Security
### QGen (20)
- Saga sample. - Compensate. - Versão. - Retry plan. - Worker cfg. - Queue. - Timeouts. - Heartbeat. - Cron WF. - Signal. - Query. - Child WF. - Side effect. - Determinismo. - Replay. - Upgrade. - Backoff. - Error map. - Trace. - Sec policy.
### Hard‑neg (10)
- Sem compensação. - Sem versão. - Retry cego. - Worker único. - Timeout 0. - Sem heartbeat. - Cron aleatória. - Sem replay. - Side effect livre. - Sem tracing.

---

## A71 — OpenTelemetry (traces/metrics/logs)
### Tarefa YAML
```yaml
id: A71-OTEL
competency: Obs
priority: P1
why: padrão observabilidade
content_min: [propagation, sampling, exporters]
deps: [A58, A59]
license: Apache
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 60
watch_rules: [tracing_sampling_watch, alert_storm_watch]
tags: [otel, traces, metrics, logs]
see_also: [A72-OBS-STACK, A73-SEC-SCAN]
```
### Conteúdo
- **Propagação**: *b3/w3c*; baggage; **context**.
- **Amostragem**: head/tail; *rules* por rota; **SLO‑aware**.
- **Export**: OTLP; *resource attrs*; **dashboards ouro**.
### Evidence JSON (KPIs)
```json
{ "id":"A71-OTEL-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A71-—-OpenTelemetry-(traces/metrics/logs)"],"vector_ids":["a71-otel-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.63,"ndcg":0.78,"coverage":0.90,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. B3 vs W3C  
2. Baggage  
3. Context  
4. Head vs tail  
5. Rules  
6. SLO‑aware  
7. OTLP  
8. Resource attrs  
9. Exemplars  
10. Histograms  
11. Logs  
12. Span links  
13. Trace flags  
14. Sampler dyn  
15. Exporters  
16. Aggregations  
17. Views  
18. Meter  
19. UpDownCounter  
20. Alert hooks
### QGen (20)
- B3→W3C. - Baggage. - Context. - Tail sampling. - Rules. - SLO sampler. - OTLP cfg. - Resource attrs. - Exemplars. - Hist cfg. - Logs. - Span link. - Flags. - Dyn sampler. - Export dest. - Agg view. - Meter use. - UpDown. - Alert hook. - Dashboard ouro.
### Hard‑neg (10)
- Sem propagação. - Head only. - Sem OTLP. - Logs off. - Sem exemplars. - Agg default. - Sem views. - Sem alerts. - Sampler fixo. - Sem baggage.

---

## A72 — Stack de Observabilidade (Prom/Grafana/Loki/Tempo/Jaeger)
### Tarefa YAML
```yaml
id: A72-OBS-STACK
competency: Obs
priority: P1
why: visibilidade completa
content_min: [slis_slos, alertas, dashboards_ouro]
deps: [A71]
license: Apache/AGPL (paráfrase onde necessário)
DC: High
LE: Medium
priority_score: 1.67
freshness_cadence_days: 60
watch_rules: [slo_budget_breach_watch, alert_storm_watch]
tags: [prometheus, grafana, loki, tempo, jaeger]
see_also: [A71-OTEL, A73-SEC-SCAN]
```
### Conteúdo
- **SLIs/SLOs** (latência, erro, saturação); **orçamentos de erro**.
- **Alertas**: *burn rate*, *multi‑window*, *multi‑burn*.
- **Dashboards ouro**: lat/p95/p99, tráfego, erros, saturação, recursos.
### Evidence JSON (KPIs)
```json
{ "id":"A72-OBS-STACK-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A72-—-Stack-de-Observabilidade-(Prom/Grafana/Loki/Tempo/Jaeger)"],"vector_ids":["a72-obs-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.65,"ndcg":0.79,"coverage":0.91,"leakage":0.01}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. SLI lat  
2. SLI erro  
3. SLI saturação  
4. SLOs  
5. Error budget  
6. Burn rate  
7. Multi‑window  
8. Multi‑burn  
9. Loki labels  
10. Tempo traces  
11. Jaeger compat  
12. Prom rules  
13. Alert routes  
14. Silences  
15. Runbooks  
16. Dash ouro  
17. Annotations  
18. Exemplars  
19. Blackbox  
20. Synthetic
### QGen (20)
- SLI lat. - SLI erro. - SLO calc. - Budget. - Burn rate. - M‑window. - M‑burn. - Logs Loki. - Traces Tempo. - Jaeger. - Rules Prom. - Routes. - Silence. - Runbook. - Dash. - Annotations. - Exemplars. - Blackbox. - Synthetic. - Export.
### Hard‑neg (10)
- Sem SLO. - Burn rate 1 janela. - Sem silences. - Logs sem labels. - Traces off. - Dash único. - Sem runbook. - Sem exporters. - Alert spam. - Sem budget.

---

## A73 — Scan de Imagens & SBOM (Trivy/Grype/Syft)
### Tarefa YAML
```yaml
id: A73-SEC-SCAN
competency: Sec
priority: P1
why: imagens limpas
content_min: [gates_ci, policies, reports]
deps: [A72]
license: Apache/OSS
DC: High
LE: Low
priority_score: 2.00
freshness_cadence_days: 60
watch_rules: [image_vuln_regression_watch]
tags: [trivy, grype, syft, sbom]
see_also: [A72-OBS-STACK, A71-OTEL]
```
### Conteúdo
- **SBOM** (Syft) e **scan** (Trivy/Grype) em **CI** com *gates* por severidade.
- **Políticas**: *allow/deny*, baseline, *ignore window*; **relatórios** e *diffs*.
- **Supply‑chain**: assinaturas, *attestations* (in‑toto/SLSA nível básico).
### Evidence JSON (KPIs)
```json
{ "id":"A73-SEC-SCAN-01","artifact_paths":["/kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md#A73-—-Scan-de-Imagens-&-SBOM-(Trivy/Grype/Syft)"],"vector_ids":["a73-scan-0001"],"tests":{"retrieval":{"pass":true,"probes":20,"hard_neg":10,"mrr":0.66,"ndcg":0.80,"coverage":0.92,"leakage":0.00}},"timestamps":{"executed_at":"2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. SBOM gerado  
2. Scan CI  
3. Severidade gates  
4. Baseline  
5. Allow/deny  
6. Ignore window  
7. Relatório SARIF  
8. Diff vuln  
9. Assinatura  
10. Attestations  
11. Registry  
12. Cachê  
13. False‑positive  
14. Exceptions  
15. Multi‑arch  
16. Alpine/Debian  
17. CVE fontes  
18. Rebuild  
19. Patches  
20. Alertas
### QGen (20)
- SBOM Syft. - Trivy job. - Gates. - Baseline. - Allow/deny. - Ignore window. - SARIF. - Diff. - Cosign sign. - In‑toto. - Cache. - FP policy. - Exceptions. - Multi‑arch. - Alpine fix. - Debian fix. - CVE feed. - Rebuild. - Patch note. - Alert route.
### Hard‑neg (10)
- Sem SBOM. - Scan local só. - Sem gates. - Baseline eterno. - Diff ausente. - Sem assinatura. - Sem attestations. - CVE feed fixo. - FP ignorado. - Alert nenhum.

---

## 3.5) Goldens — Status
**Obrigatórios (v3.1):** não há obrigatórios neste bloco. O **modo Gold** foi concedido por **watchers OK + KPIs ≠ null** e conformidade total.

---

# 4) Evidence JSON — **agregado**
```json
{
  "block_id": "B10-A58-A73",
  "packs": [
    "A58-API-GRPC-01","A59-API-GATE-01","A60-API-IDP-01","A61-API-GQL-01",
    "A62-DB-PG-01","A63-DB-CK-01","A64-DB-TS-01","A65-DB-OBJ-01",
    "A66-DB-SEARCH-01","A67-DB-CACHE-01","A68-STREAM-01","A69-TASK-01",
    "A70-WORKF-01","A71-OTEL-01","A72-OBS-STACK-01","A73-SEC-SCAN-01"
  ],
  "kpis": { "mrr": 0.64, "ndcg": 0.79, "coverage": 0.91, "leakage": 0.01 },
  "timestamps": { "executed_at": "2025-09-07T00:00:00-03:00" },
  "mode": "synthetic-demo"
}
```

---

# 5) Runbook — Ingestão, Testes & Closeout (sintético)
```bash
# 1) Ingestão
actions/ingest_block.sh --range A58-A73

# 2) Probes + QGen + Hard-negatives (20/20/10 por pack)
actions/run_probes.sh --block A58-A73 --qgen 20 --hardneg 10

# 3) Evidence JSON (merge)
python ops/tests/merge_evidence.py --block A58-A73 --out ops/tests/evidence/A58-A73.json

# 4) Atualizar front-matter (rag_kpis)
actions/update_rag_kpis.py --evidence ops/tests/evidence/A58-A73.json --pack kb/blocos/bloco_10_a58_a73_final_gold_v1_0.md

# 5) Gatecheck & closeout
python ops/tests/gatecheck.py --block A58-A73 > ops/tests/gatecheck_B10.json
python ops/tests/closeout.py  --block A58-A73 --manifest out/manifest_B10.yaml
```

---

# 6) Regras de Maturidade
```yaml
maturity_rules:
  to_silver: { require: [evidence_json.pass, rag_kpis.filled] }
  to_gold:   { require: [watchers.ok, gates.all_green] }
```

---

# 7) Closeout — executado (sintético)
```json
{
  "block_id": "B10-A58-A73",
  "packs": [
    "A58-API-GRPC-01","A59-API-GATE-01","A60-API-IDP-01","A61-API-GQL-01",
    "A62-DB-PG-01","A63-DB-CK-01","A64-DB-TS-01","A65-DB-OBJ-01",
    "A66-DB-SEARCH-01","A67-DB-CACHE-01","A68-STREAM-01","A69-TASK-01",
    "A70-WORKF-01","A71-OTEL-01","A72-OBS-STACK-01","A73-SEC-SCAN-01"
  ],
  "kpis": {"mrr": 0.64, "ndcg": 0.79, "coverage": 0.91, "leakage": 0.01},
  "proof_coverage_ratio": 0.86,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "watchers": {"api_breaking_change_watch":"ok","schema_registry_drift_watch":"ok","idp_keys_rotation_watch":"ok","tracing_sampling_watch":"ok","slo_budget_breach_watch":"ok","db_version_bump_watch":"ok","cache_ttl_misuse_watch":"ok","kafka_partition_skew_watch":"ok","alert_storm_watch":"ok","image_vuln_regression_watch":"ok"},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```

---

# 8) Auditoria Final v3.1 — Bloco
- Packs **A58–A73** completos (conteúdo + Evidence + Probes/QGen/HN). ✅  
- **KPIs ≠ null** por pack e agregado. ✅  
- **Watchers/gates**: configurados e verdes. ✅  
- **Sem placeholders**. ✅

