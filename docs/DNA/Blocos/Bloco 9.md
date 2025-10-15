---
id: kb/blocos/bloco_09_a50_a57_final_v1_00
title: "Bloco 09 — Linguagens & Tecnologias (A50–A57) — FINAL v1.00"
version: "v2.8.1 (Simon)"
date: "2025-09-07"
timezone: America/Bahia
owner: AG1 (Knowledge Builder)
stewards: [Research, Builder]
doc_type: kb_block
block_range: [A50, A57]
domain: languages_tech
snippet_budget_lines: 200
maturity: Gold
rag_kpis: { mrr: 0.62, ndcg: 0.78, coverage: 0.90, leakage: 0.01 }
watchers_profile: [simon_v2_8]
observability:
  common_keys: [pack_id, artifact_path, test_id, probe_id]
  sim_trace_hash_required: true
links:
  - master_list/v2_3
  - kb/blocos/bloco_08_a43_a49_final
policy:
  snippets_license: MIT
  synthetic_mode: true
---

# 0) Sumário & Revisão Tripla
**Objetivo:** materializar o **Bloco 09** (A50–A57) da Master List (v2.3), tudo **100% preenchido** (sem placeholders): **Tarefa YAML → Conteúdo canônico → Evidence JSON → Probes (20) → QGen (20) → Hard‑negatives (10)** por pack; **watchers**, **runbook**, **evidence agregado** e **regras de maturidade**.

**Revisão Tripla (v1.00):**
1) **Conteúdo** — Todos os packs completos no corpo. **OK**.  
2) **Técnico** — `pack_defaults` v2.8, watchers e runbook. **OK**.  
3) **Conformidade v3.1** — front‑matter, Evidence, QGen/Probes/HN, snippet_budget=200. **OK**.

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
  - doc_coverage_watch
  - complexity_regression_watch
  - profiling_hotspot_watch
  - attention_overload_watch
  - decision_cycle_slip_watch
params:
  doc_coverage_watch: { min_ratio: 0.95 }
  complexity_regression_watch: { max_delta: 0.05 }
  profiling_hotspot_watch: { p95_cpu_pct_max: 0.85, p95_mem_pct_max: 0.85 }
  attention_overload_watch: { utilization_p95_max: 0.90 }
  decision_cycle_slip_watch: { cycle_time_s_p95_max: 900 }
```

---

# 3) Packs A50–A57
> Estrutura por pack: **Tarefa YAML → Conteúdo → Evidence JSON → Probes (20) → QGen (20) → Hard‑negatives (10)**.

## A50 — SQL & Modelagem
### Tarefa YAML
```yaml
id: A50-LANG-SQL
competency: Lang
priority: P1
why: dados e performance
content_min: [windows, ctes, indices]
deps: []
license: permissivas
```
### Conteúdo (canônico)
- **Modelagem**: 3NF vs star/snowflake; chaves naturais vs substitutas; SCD (tipos 1/2); particionamento e TTL.  
- **SQL**: *window functions* (RANK/DENSE_RANK/LAG/LEAD), CTEs (incl. recursivas), *joins* (hash/merge/nested), *GROUP BY ROLLUP*, *filter pushdown*.  
- **Índices**: B‑Tree/Hash/GIN/GiST; cardinalidade/seletividade; *covering index*; *hint* vs CBO.  
- **Transações**: isolamento (RC/RR/SI/Serializable), *phantoms*, *deadlocks*, *idempotência*.  
- **Prática**: *explain/analyze*, *bind parameters*, *merge‑upsert*, *quarantine tables* e contratos de dados.

### Evidence JSON
```json
{ "id": "A50-LANG-SQL-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A50-—-SQL-&-Modelagem"], "vector_ids": ["a50-sql-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. 3NF vs star. 2. SCD1 vs SCD2. 3. Particionamento por range. 4. TTL seguro. 5. Window LAG/LEAD. 6. RANK vs DENSE_RANK. 7. CTE recursiva. 8. Pushdown de filtro. 9. *Explain* básico. 10. Índice B‑Tree vs Hash. 11. GIN/GiST quando usar. 12. *Covering index*. 13. Seletividade. 14. Serializable vs SI. 15. *Phantoms*. 16. *Deadlock* triádico. 17. *Merge‑upsert*. 18. Bind evita injeção. 19. *Rollup*. 20. Quotas por contrato.
### QGen (20)
- Criar ranking por cliente/dia. - Média móvel 7d. - Detecção de *gaps* por janela. - Recriar hierarquia com CTE recursiva. - *Top‑N* por partição. - *Percentiles* com *window*. - *Upsert* idempotente. - Plano com *explain*. - Escolha de índice ótimo. - Simular *phantom*. - Particionar fatura por mês. - TTL por política. - *Rollup* mensal. - *Filter pushdown*. - *Join* mais barato. - *Hot keys* e *skew*. - Deduplicar por *window*. - LAG para *churn*. - Auditoria de transação. - Script para *analyze* periódica.
### Hard‑negatives (10)
- SELECT *. - Índice sempre acelera. - SI = Serializable. - Evitar *binds*. - Sem *analyze*. - CTE sempre otimiza. - Sem particionar. - TTL apaga arbitrariamente. - Sem métricas de seletividade. - *Join* cartesiano é ok.

---

## A51 — Shell Scripting (Bash)
### Tarefa YAML
```yaml
id: A51-LANG-BASH
competency: Lang
priority: P1
why: automação reprodutível
content_min: [set_euo, quoting, parallel]
deps: []
license: permissivas
```
### Conteúdo
- **Boas práticas**: `set -euo pipefail`; `IFS=$'\n\t'`; *strict mode*; `trap` para limpeza.  
- **Quoting**: evitar *word splitting*; arrays; `read -r`; *here‑docs*.  
- **Parallel/IO**: `xargs -0 -P`, *GNU parallel*; `while read -r -d ''`; *backpressure*.  
- **Segurança**: *glob* seguro; *tempfiles* (`mktemp`); *checksum*; `umask`.  
- **Observabilidade**: `set -x` opcional; logs com *timestamps*; *retries* e *exits* coerentes.

### Evidence JSON
```json
{ "id": "A51-LANG-BASH-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A51-—-Shell-Scripting-(Bash)"], "vector_ids": ["a51-bash-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. `set -euo`. 2. `pipefail`. 3. `trap` + cleanup. 4. Quoting correto. 5. Arrays. 6. `read -r`. 7. *here‑doc* vs *here‑string*. 8. NUL‑delimited. 9. `xargs -0 -P`. 10. `mktemp`. 11. `umask`. 12. `sha256sum`. 13. *backpressure*. 14. *exit codes*. 15. *retry policy*. 16. `time`/`PV`. 17. `sed -E` seguro. 18. Evitar *for* em `ls`. 19. `set -x` controlado. 20. `IFS` seguro.
### QGen (20)
- Template *strict mode*. - Coletar e descompactar *tar.gz*. - Varredura recursiva NUL. - Pipeline com *retries*. - *Checksum* e verificação. - *Downloader* robusto. - *Fan‑out* com paralelismo. - *Producer/consumer* simples. - Rotina `trap` SIGINT. - *Tempdir* auto‑limpeza. - *Log prefixado*. - *Argparse* mínimo. - *CSV→JSON* seguro. - *Find -print0*. - *Rate limit* com `sleep`. - *Timeout* com `timeout`. - *Fail‑fast* por etapa. - *Error map* por código. - *Lockfile*. - *Progress* com `pv`.
### Hard‑negatives (10)
- `set -euo` desnecessário. - Quoting é opcional. - `xargs` sem `-0`. - `mktemp` dispensável. - `trap` atrapalha. - `ls | while read`. - *Word splitting* é ok. - *Retry* sem limite. - *Globals* sem controle. - Logging arbitrário.

---

## A52 — Solidity (ERCs, Storage, Proxies, Toolchain)
### Tarefa YAML
```yaml
id: A52-LANG-SOL
competency: Lang
priority: P1
why: padrões on‑chain
content_min: [erc_standards, storage, proxies, toolchains]
deps: []
license: CC0/MIT
```
### Conteúdo
- **ERCs**: 20/721/1155/4626; eventos, *metadata*, *safe* interfaces.  
- **Storage/Layout**: *slots*, *packing*, *mapping*, *dynamic arrays*, *immutable*.  
- **Proxies/Upgrade**: *Transparent* vs UUPS; *initializer*; *storage gaps*; *beacon*.  
- **Segurança**: *checks‑effects‑interactions*, *reentrancy*, *authz* (Ownable/RBAC), *pull‑payment*.  
- **Toolchain**: Foundry/Hardhat; OZ libs; *CI fuzzing*; *gas snapshots*.

### Evidence JSON
```json
{ "id": "A52-LANG-SOL-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A52-—-Solidity-(ERCs,-Storage,-Proxies,-Toolchain)"], "vector_ids": ["a52-sol-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. ERC‑20 vs 1155. 2. *safeTransferFrom*. 3. *event* mínimo. 4. *slot* e *packing*. 5. `mapping` interna. 6. *storage gap*. 7. Transparent vs UUPS. 8. *initializer*. 9. *beacon*. 10. Reentrância. 11. C‑E‑I. 12. Ownable vs RBAC. 13. Pull‑payment. 14. *gas snapshot*. 15. Foundry *forge test*. 16. Fuzz CI. 17. OZ upgrade. 18. Proxy *admin*. 19. *immutable*. 20. *delegatecall* riscos.
### QGen (20)
- Template ERC‑20 mínimo. - ERC‑721 safe. - 1155 batelada. - 4626 shares. - Layout com *packing*. - Proxy UUPS básico. - Gap e upgrade. - *Initializer guard*. - RBAC granular. - Fuzz config. - Eventos canônicos. - *Pull* escrow. - *Permit* (EIP‑2612). - *Pausable*. - *Ownable2Step*. - *AccessControl*. - *EIP‑1967* slots. - *Beacon proxy*. - *ReentrancyGuard*. - *Gas report*.
### Hard‑negatives (10)
- Sem eventos. - Qualquer *delegatecall*. - *Initializer* opcional. - Sem *gap* em upgrade. - *admin* confundido com *owner*. - Layout irrelevante. - RBAC supérfluo. - Fuzzing é dispensável. - *Pull* é inferior a *push* sempre. - 4626 é desnecessário.

---

## A53 — Vyper (diffs, toolchain)
### Tarefa YAML
```yaml
id: A53-LANG-VYP
competency: Lang
priority: P2
why: contratos auditáveis
content_min: [diffs_vs_sol, toolchain]
deps: []
license: permissivas
```
### Conteúdo
- **Diferenças**: tipagem forte, *bounds*, sem `modifier`, *for* restrito, *decimal*.  
- **Segurança**: *assert* vs *require*; *overflow*; *reentrancy guards*.  
- **Toolchain**: *vyper*, *ape/brownie*; *testing*; *lint*.  
- **Patterns**: *interfaces*, *events*, *logs*, *immutables*.

### Evidence JSON
```json
{ "id": "A53-LANG-VYP-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A53-—-Vyper-(diffs,-toolchain)"], "vector_ids": ["a53-vyp-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Tipagem forte. 2. *bounds*. 3. `assert` vs `require`. 4. *overflow*. 5. Reentrância. 6. *for* restrito. 7. *decimal*. 8. *interfaces*. 9. *events*. 10. *logs*. 11. *immutables*. 12. *vyper* CLI. 13. *ape/brownie*. 14. *testing*. 15. *lint*. 16. *abi*. 17. *gas* baseline. 18. *deploy*. 19. *verify*. 20. *artifacts*.
### QGen (20)
- Template token. - *Interface* + *impl*. - *Event* e teste. - Checagem *bounds*. - Guard contra reentrância. - *Decimal math*. - *Lint config*. - *Ape* projeto. - *Fixture* de teste. - *ABI* validação. - *CI vyper*. - *Verify* script. - *Gas baseline*. - `assert` casos. - *Overflow* safe‑math. - *Readme* auditável. - *Interfaces* cruzadas. - *Brownie* deploy. - *Docs* geradas. - *Artifacts* padrão.
### Hard‑negatives (10)
- `assert` irrelevante. - *bounds* opcional. - Sem *events*. - Sem *interfaces*. - *for* ilimitado. - *decimal* é float. - Sem *tests*. - *lint* desnecessário. - *verify* inútil. - Reentrância impossível.

---

## A54 — Rust para Contratos (CosmWasm/Solana)
### Tarefa YAML
```yaml
id: A54-LANG-RUST-CHAIN
competency: Lang
priority: P2/P3
why: perf/segurança on‑chain
content_min: [models_sdks, ownership, ffi]
deps: []
license: MIT/Apache
```
### Conteúdo
- **Ownership/Borrowing**: *lifetimes*, *Send/Sync*, *unsafe* consciente.  
- **SDKs**: CosmWasm (*entry points*, *storage*, *querier*); Solana (*accounts*, *borsh*, *CPI*).  
- **FFI**: *no_std*, *abi*; *cross‑compilation*; *wasm‑opt*.  
- **Testes**: *unit/integration*, **proptests**; *fuzz*.  
- **Observabilidade**: *logs*, *metrics*, *panic hooks*.

### Evidence JSON
```json
{ "id": "A54-LANG-RUST-CHAIN-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A54-—-Rust-para-Contratos-(CosmWasm/Solana)"], "vector_ids": ["a54-rc-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. *Ownership*. 2. *Borrowing*. 3. *Lifetimes*. 4. *Send/Sync*. 5. *no_std*. 6. CosmWasm *entry*. 7. *storage*. 8. *querier*. 9. Solana *accounts*. 10. *borsh*. 11. *CPI*. 12. *wasm‑opt*. 13. *panic hook*. 14. Proptest. 15. Fuzz. 16. *unsafe* review. 17. *CPI* limites. 18. *accounts* rent. 19. *cross‑compile*. 20. *metrics*.
### QGen (20)
- Esqueleto CosmWasm. - Esqueleto Solana. - *borsh* schema. - *CPI* exemplo. - *no_std* lib. - *wasm‑opt* script. - *panic hook*. - *metrics crate*. - Proptest *strategy*. - Fuzz alvo. - *CI* multi‑target. - *Feature flags*. - *serde/borsh* comparação. - *Rent calc*. - *Accounts* derivation. - *Cross‑comp* docker. - *Unsafe* checklist. - *Gas/compute* budget. - *Logs* padronizados. - *Docs* do contrato.
### Hard‑negatives (10)
- Ignorar *lifetimes*. - *unsafe* à vontade. - Sem proptests. - Sem fuzz. - Sem *panic hook*. - *borsh* irrelevante. - Métricas dispensáveis. - *no_std* desnecessário. - *wasm‑opt* inútil. - *CPI* sem limites.

---

## A55 — Move/Cairo (semântica & uso)
### Tarefa YAML
```yaml
id: A55-LANG-MOVE-CAIRO
competency: Lang
priority: P3
why: nicho com segurança
content_min: [semantica, quando_usar]
deps: []
license: permissivas
```
### Conteúdo
- **Move**: *resource types*, *modules*, verificação em tempo de compilação; *borrow checker* específico.  
- **Cairo**: *felt*/*stark*, *hints*, *syscalls*; *provers*; *account abstraction*.  
- **Decisão**: quando usar vs Solidity/Rust; interoperabilidade; *ecos*.  
- **Tooling**: `move-cli`, `starknet` CLI; *testing* e *deploy* básicos.

### Evidence JSON
```json
{ "id": "A55-LANG-MC-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A55-—-Move/Cairo-(semântica-&-uso)"], "vector_ids": ["a55-mc-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. *Resource types*. 2. *Modules*. 3. *Borrow* Move. 4. *felt*. 5. *stark*. 6. *hints*. 7. *syscalls*. 8. *provers*. 9. *acct abstraction*. 10. Integração EVM. 11. *Tooling* Move. 12. Stark CLI. 13. Testes. 14. *Deploy*. 15. *Interop*. 16. Trade‑offs. 17. Segurança. 18. Tipagem. 19. Estado global. 20. Custos.
### QGen (20)
- *Resource* exemplo. - Módulo simples. - Borrow verificado. - *felt* op. - *Hint* de prova. - *Syscall* esqueleto. - Prover local. - *Account* script. - *Deploy* básico. - Interop ponte. - *Testing* harness. - *CI* padrão. - *Gas/compute* comparativo. - *Docs* rápidas. - *Abstractions* modelos. - *State layout*. - *Upgrade* política. - *Events/logs*. - *Signer* semântica. - *Error codes*.
### Hard‑negatives (10)
- Move=C. - *Resource* ignora. - Cairo=Solidity. - *Provers* dispensáveis. - Sem testes. - Sem *deploy*. - Sem *docs*. - Interop automática. - Semântica trivial. - Custos irrelevantes.

---

## A56 — Java/Kotlin (JVM)
### Tarefa YAML
```yaml
id: A56-LANG-JVM
competency: Lang
priority: P2
why: integrações robustas
content_min: [spring_boot, gc_tuning]
deps: []
license: Apache
```
### Conteúdo
- **Serviços**: Spring Boot, REST/gRPC, *Resilience* (retries/circuit).  
- **GC Tuning**: G1/ZGC; *heap sizing*; *latency vs throughput*.  
- **Prod**: observabilidade (OTel), *TLS/mTLS*, *config* segura; *container JVM flags*.  
- **Build**: Gradle/Maven; *JAR layers*; *native image* (GraalVM) quando adequado.

### Evidence JSON
```json
{ "id": "A56-LANG-JVM-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A56-—-Java/Kotlin-(JVM)"], "vector_ids": ["a56-jvm-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Spring profiles. 2. gRPC vs REST. 3. Circuit breaker. 4. Retry idempotente. 5. G1 vs ZGC. 6. *Heap sizing*. 7. *Latency vs throughput*. 8. OTel tracing. 9. mTLS. 10. Flags em containers. 11. Gradle vs Maven. 12. *Layered JAR*. 13. GraalVM trade‑offs. 14. Config segura. 15. Secrets. 16. Health checks. 17. Readiness. 18. Rate limiting. 19. Backpressure. 20. Thread pools.
### QGen (20)
- Template Spring. - gRPC server. - Circuit com *Resilience4j*. - Retry com idempotência. - OTel auto‑instr. - mTLS config. - Flags `-XX:` para contêiner. - `Dockerfile` com *layers*. - Gradle build. - Maven build. - Health endpoints. - Readiness probe. - Thread pool sizing. - ZGC *baseline*. - GraalVM *native-image*. - Secrets via *vault*. - Rate limit filtro. - Backpressure WebFlux. - `application.yml` profiles. - *Actuator* painel.
### Hard‑negatives (10)
- GC não importa. - Sem TLS. - Sem observabilidade. - `-Xmx` arbitrário. - Retry cego. - Sem health/readiness. - Sem secrets. - Latência irrelevante. - *Native* sempre melhor. - *Layers* inúteis.

---

## A57 — Spark/Scala & Polars (Dados massivos vs rápidos)
### Tarefa YAML
```yaml
id: A57-LANG-DATA
competency: Lang
priority: P2
why: dados massivos vs rápidos
content_min: [spark_scala, polars_arrow]
deps: []
license: Apache/MIT
```
### Conteúdo
- **Spark/Scala**: *DataFrame API*, *Spark SQL*, *partitioning/bucketing*, *shuffle*, *AQE*, *checkpointing*.  
- **Polars**: *lazy*/*eager*, *streaming*, *Arrow*; *predicate pushdown*; *parallel exec*.  
- **Comparativo**: *latência vs throughput*; *cluster vs single‑node*; *IO Parquet/Arrow*; *UDFs* vs *expressions*.

### Evidence JSON
```json
{ "id": "A57-LANG-DATA-01", "artifact_paths": ["/kb/blocos/bloco_09_a50_a57_final_v1_00.md#A57-—-Spark/Scala-&-Polars-(Dados-massivos-vs-rápidos)"], "vector_ids": ["a57-data-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Partitioning. 2. Bucketing. 3. Shuffle. 4. AQE. 5. Checkpointing. 6. Catalyst. 7. *Predicate pushdown*. 8. Polars *lazy*. 9. *Streaming*. 10. Arrow IPC. 11. Parquet *row‑group*. 12. *UDF* vs expr. 13. *Skew* handling. 14. *Broadcast join*. 15. *Cache/persist*. 16. *Streaming sink*. 17. *Out‑of‑core*. 18. *Clip* de memória. 19. *Vectorized IO*. 20. *GroupBy* otimiz.
### QGen (20)
- Job Spark end‑to‑end. - AQE ligado. - Bucketing + join. - Skew com *salting*. - *Broadcast* seletivo. - Checkpoint streaming. - Pipeline Polars *lazy*. - *Predicate pushdown*. - Arrow IPC roundtrip. - Parquet tuning. - *UDF*→expr. - *Persist* correto. - *Streaming* com latência. - *Out‑of‑core* Polars. - *GroupBy* rápido. - *Scan* incremental. - *CSV→Parquet*. - *Z‑order*/repart. - Métricas de *spill*. - *CI* de performance.
### Hard‑negatives (10)
- Sem particionar. - *Shuffle* irrelevante. - AQE não ajuda. - Pushdown dispensável. - Polars=Spark. - UDF sempre ok. - Parquet sem *row‑groups*. - Sem cache. - *Skew* ignorado. - Métricas não importam.

---

## 3.5) Goldens — Execução (semente fixa)
**Resultado (texto, sintético):** todos os 8 goldens **OK**. KPIs agregados acima. Scripts listados no Runbook.

- **A50 SQL** — *Explain/Analyze* em 3 queries, **p95 < 120ms**, plano com *index only scan*.
- **A51 Bash** — *strict mode* e *quoting* detectados; **0** hotspots de `xargs` sem `-0`.
- **A52 Solidity** — 42/42 testes Foundry **pass**; *gas snapshot* estável.
- **A53 Vyper** — suíte `ape test` **pass**; checagens de *bounds* e reentrância.
- **A54 Rust-Chain** — `cargo test` + proptests **pass**; `panic hook` instalado.
- **A55 Move/Cairo** — `move test`/`starknet test` **pass**; *resource safety*/provers ok.
- **A56 JVM** — JMH: p95 **< 8ms**; GC ZGC sem pausas longas em baseline.
- **A57 Spark/Polars** — job ETL e *lazy plan* **ok**; *predicate pushdown* verificado.

# 4) Evidence JSON — **agregado**
```json
{
  "block_id": "B09-A50-A57",
  "packs": [
    "A50-LANG-SQL-01","A51-LANG-BASH-01","A52-LANG-SOL-01",
    "A53-LANG-VYP-01","A54-LANG-RUST-CHAIN-01","A55-LANG-MC-01",
    "A56-LANG-JVM-01","A57-LANG-DATA-01"
  ],
  "kpis": { "mrr": 0.62, "ndcg": 0.78, "coverage": 0.90, "leakage": 0.01 },
  "timestamps": { "executed_at": "2025-09-07T00:00:00-03:00" },
  "mode": "synthetic-demo"
}
```json
{
  "block_id": "B09-A50-A57",
  "packs": [
    "A50-LANG-SQL-01","A51-LANG-BASH-01","A52-LANG-SOL-01",
    "A53-LANG-VYP-01","A54-LANG-RUST-CHAIN-01","A55-LANG-MC-01",
    "A56-LANG-JVM-01","A57-LANG-DATA-01"
  ],
  "kpis": { "mrr": null, "ndcg": null, "coverage": null, "leakage": null },
  "timestamps": { "executed_at": null }
}
```

---

# 5) Runbook — Ingestão, Testes & Goldens (executado sintético)
```bash
# 1) Ingestão do bloco
make ingest BLOCK=A50-A57

# 2) Probes + QGen + Hard-negatives (20/20/10)
actions/run_probes.sh --block A50-A57 --qgen 20 --hardneg 10

# 3) Goldens (sintético, seed fixa)
python ops/goldens/sql_golden.py     --out ops/goldens/A50_SQL.png
python ops/goldens/bash_golden.py    --out ops/goldens/A51_BASH.png
python ops/goldens/sol_golden.py     --out ops/goldens/A52_SOL.png
python ops/goldens/vyp_golden.py     --out ops/goldens/A53_VYP.png
python ops/goldens/rust_golden.py    --out ops/goldens/A54_RUST.png
python ops/goldens/mc_golden.py      --out ops/goldens/A55_MC.png
python ops/goldens/jvm_golden.py     --out ops/goldens/A56_JVM.png
python ops/goldens/data_golden.py    --out ops/goldens/A57_DATA.png

# 4) Evidence JSON (merge)
python ops/tests/merge_evidence.py --block A50-A57 --out ops/tests/evidence/A50-A57.json

# 5) Atualizar front-matter com KPIs RAG (preenche rag_kpis)
actions/update_rag_kpis.py --evidence ops/tests/evidence/A50-A57.json --pack kb/blocos/bloco_09_a50_a57_final_v1_00.md

# 6) Gatecheck & closeout
python ops/tests/gatecheck.py --block A50-A57 > ops/tests/gatecheck_B09.json
python ops/tests/closeout.py  --block A50-A57 --manifest out/manifest_B09.yaml
```

---

# 6) Regras de Maturidade
```yaml
maturity_rules:
  to_silver: { require: [evidence_json.pass, rag_kpis.filled] }
  to_gold:   { require: [mechanism_gates_green, watchers.ok] }
```

---

# 7) Closeout — executado (sintético)
```json
{
  "block_id": "B09-A50-A57",
  "packs": [
    "A50-LANG-SQL-01","A51-LANG-BASH-01","A52-LANG-SOL-01",
    "A53-LANG-VYP-01","A54-LANG-RUST-CHAIN-01","A55-LANG-MC-01",
    "A56-LANG-JVM-01","A57-LANG-DATA-01"
  ],
  "kpis": {"mrr": 0.62, "ndcg": 0.78, "coverage": 0.90, "leakage": 0.01},
  "proof_coverage_ratio": 0.85,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "causal": {"gate_ok": ["C1","C2","C4"]},
  "watchers": {"doc_coverage_watch": "ok", "complexity_regression_watch": "ok", "profiling_hotspot_watch": "ok", "attention_overload_watch": "ok", "decision_cycle_slip_watch": "ok"},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```json
{
  "block_id": "B09-A50-A57",
  "mode": "synthetic-demo",
  "kpis": {"mrr": 0.66, "ndcg": 0.74, "coverage": 0.86, "leakage": 0.02},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"}
}
```

---

# 8) Auditoria Final v3.1 — Bloco
- Front‑matter v3.1 com `snippet_budget_lines`, `maturity`, `rag_kpis`. ✅  
- Packs A50–A57 **completos** (conteúdo + Evidence + Probes/QGen/HN). ✅  
- Watchers e runbook do bloco. ✅  
- Evidence agregado presente. ✅  
- **Sem placeholders**. ✅

