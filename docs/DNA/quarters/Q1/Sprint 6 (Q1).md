# Sprint 6 (Q1) — Especificação vMasterpiece‑Final (Bertrand‑led, 100/10)

## 1. Sumário Executivo

Esta especificação define, sem ambiguidade, a Sprint 6 (Q1) do projeto CE. O objetivo é entregar scorecards operacionais determinísticos com guard de CI que bloqueia PRs fora do alvo e, adicionalmente, o pipeline "Boss Final Q1" (validação integral S1→S6). O documento adota **Design by Contract (DbC)**, aritmética **Decimal + epsilon**, schemas JSON versionados e práticas de reprodutibilidade que garantem que **funcione no primeiro teste**.

* **Líder técnico:** Vitalik Buterin (simplicidade, correção, economia de design).
* **Stakeholder com veto/decisão final:** Bertrand Meyer (DbC). Este documento foi escrito “à maneira dele”: contratos explícitos, pré/pós‑condições, invariantes e testes cobrindo casos normais e de erro.

## 2. Escopo e Não‑Objetivos

**Escopo:**

1. Scorecards S6 com guard em CI, bundle estático versionado, watcher/hook mínimo, painel Grafana exportável e documentação curta.
2. UX de PR: badge e comentário automatizado com fallback para summary do job.
3. Reprodutibilidade forte: determinismo byte‑a‑byte (exceto timestamp), hash canônico do bundle, UTF‑8 + newline, ordenação estável.
4. **Boss Final Q1**: workflow único que consolida S1…S6 (100% offline/determinístico) e aplica gate global.
5. **Schemas formais** para todos os reports (S6 e Boss) e política de migração de schema.
6. **Governança de actions** via `actions.lock` com SHAs pinados e política de rotação.

**Não‑objetivos:** integrações com nuvem/segredos, consultas externas em rede, ou métricas ao vivo. Esta sprint usa **bundle estático** como golden‑source para S6; o Boss valida S1…S6 em modo estático/determinístico.

## 3. Métricas, Unidades e Metas (DNA)

* `quorum_ratio` ∈ [0,1] → **alvo:** `≥ 0.6667` (formatação de saída: 4 casas decimais)
* `failover_time_p95_s` ∈ [0,+∞) s → **alvo:** `≤ 60.0` (saída: 3 casas decimais)
* `staleness_p95_s` ∈ [0,+∞) s → **alvo:** `≤ 30.0` (saída: 3 casas decimais)
* `cdc_lag_p95_s` ∈ [0,+∞) s → **alvo:** `≤ 120.0` (saída: 3 casas decimais)
* `divergence_pct` ∈ [0,+∞) % → **alvo:** `≤ 1.0` (saída: 1 casa decimal, com sufixo `%` apenas em `report.md`)

## 4. Contratos (DbC por Bertrand)

**Pré‑condições (inputs válidos):**

* Existem `s6_validation/thresholds.json` e `s6_validation/metrics_static.json`, em **UTF‑8** com **newline** final.
* Ambos os JSONs são válidos contra seus **schemas Draft‑07** e respeitam os domínios (sem chaves extras; números finitos; percentuais em %).

**Pós‑condições (saídas S6):**

* Gerar, em `out/s6_scorecards/`: `report.json` (`schema_version=1`, conforme `data/cdc/schemas/report.schema.json`), `report.md` (tabela ordenada, formatos fixos), `guard_status.txt` (`PASS`/`FAIL`), `bundle.sha256`, `scorecard.svg`, `badge.svg`, `pr_comment.md`.
* Reexecução 2× com mesma entrada ⇒ `bundle.sha256` e `report.md` **idênticos** (exceto `timestamp` em `report.json`).

**Invariantes:**

* `PASS` sse todas as 5 metas são satisfeitas (após normalização Decimal+epsilon).
* Ausência/invalidade de inputs ⇒ `FAIL` **determinístico** com mensagem objetiva apontando arquivo/campo.

**Pós‑condições (Boss Final Q1):**

* Gerar, em `out/q1_boss_final/`: `report.json` (`schema_version=1`, conforme `data/cdc/schemas/q1_boss_report.schema.json`), `report.md`, `guard_status.txt`, `bundle.sha256`, `badge.svg`, `pr_comment.md`, `dag.svg`.
* `PASS` global sse `s1..s6` estão `PASS` e artefatos válidos.

**Liveness:**

* Inputs válidos ⇒ cada job decide em tempo finito. Definir `timeout-minutes` no workflow: `s6-scorecards` (20) e `q1-boss-final` (60). Nenhum step sem limite.

## 5. Manifests e Estrutura de Arquivos

```
.github/workflows/s6-scorecards.yml
.github/workflows/q1-boss-final.yml
actions.lock
scripts/scorecards/s6_scorecards.py
scripts/watchers/s6_scorecard_guard.sh
scripts/boss_final/sprint_guard.py
scripts/boss_final/aggregate_q1.py
data/cdc/schemas/thresholds.schema.json
data/cdc/schemas/metrics.schema.json
data/cdc/schemas/report.schema.json
data/cdc/schemas/q1_boss_report.schema.json
s6_validation/thresholds.json
s6_validation/metrics_static.json
s6_validation/README.md
dashboards/grafana/scorecards_quorum_failover_staleness.json
docs/scorecards/S6_SCORECARDS.md
Makefile (alvos: s6-scorecards, q1-boss-final)
out/s6_scorecards/ (gerado)
out/q1_boss_final/ (gerado)
```

## 6. Aritmética e Avaliação

* **Decimal** com precisão 28 e modo `ROUND_HALF_EVEN`.
* **Epsilon**: `EPS = 1e-12` aplicado às comparações (≥ e ≤).
* Predicados:

  * `ok_q: quorum_ratio + EPS ≥ quorum_ratio_min`
  * `ok_f: failover_time_p95_s ≤ failover_time_p95_s_max + EPS`
  * `ok_s: staleness_p95_s ≤ staleness_p95_s_max + EPS`
  * `ok_c: cdc_lag_p95_s ≤ cdc_lag_p95_s_max + EPS`
  * `ok_d: divergence_pct ≤ divergence_pct_max + EPS`
* `status = PASS` iff `ok_q ∧ ok_f ∧ ok_s ∧ ok_c ∧ ok_d`.
* Ordenação fixa das métricas em todos os artefatos: `[quorum_ratio, failover_time_p95_s, staleness_p95_s, cdc_lag_p95_s, divergence_pct]`.
* Formatação estável: ratio 4d; tempos 3d; percentuais 1d (md com `%`).

## 7. Schemas JSON (Draft‑07)

**`data/cdc/schemas/thresholds.schema.json`**

```json
{"$id":"https://ce.local/schemas/thresholds.schema.json","$schema":"http://json-schema.org/draft-07/schema#","title":"S6 Thresholds","type":"object","additionalProperties":false,"required":["version","quorum_ratio_min","failover_time_p95_s_max","staleness_p95_s_max","cdc_lag_p95_s_max","divergence_pct_max"],"properties":{"version":{"type":"integer","minimum":1},"quorum_ratio_min":{"type":"number","minimum":0.0,"maximum":1.0},"failover_time_p95_s_max":{"type":"number","minimum":0.0},"staleness_p95_s_max":{"type":"number","minimum":0.0},"cdc_lag_p95_s_max":{"type":"number","minimum":0.0},"divergence_pct_max":{"type":"number","minimum":0.0}}}
```

**`data/cdc/schemas/metrics.schema.json`**

```json
{"$id":"https://ce.local/schemas/metrics.schema.json","$schema":"http://json-schema.org/draft-07/schema#","title":"S6 Metrics Static","type":"object","additionalProperties":false,"required":["version","quorum_ratio","failover_time_p95_s","staleness_p95_s","cdc_lag_p95_s","divergence_pct"],"properties":{"version":{"type":"integer","minimum":1},"quorum_ratio":{"type":"number","minimum":0.0,"maximum":1.0},"failover_time_p95_s":{"type":"number","minimum":0.0},"staleness_p95_s":{"type":"number","minimum":0.0},"cdc_lag_p95_s":{"type":"number","minimum":0.0},"divergence_pct":{"type":"number","minimum":0.0}}}
```

**`data/cdc/schemas/report.schema.json`** (S6)

```json
{"$id":"https://ce.local/schemas/report.schema.json","$schema":"http://json-schema.org/draft-07/schema#","title":"S6 Report","type":"object","additionalProperties":false,"required":["schema_version","timestamp_utc","metrics","status"],"properties":{"schema_version":{"type":"integer","const":1},"timestamp_utc":{"type":"string","format":"date-time"},"metrics":{"type":"object","additionalProperties":false,"required":["quorum_ratio","failover_time_p95_s","staleness_p95_s","cdc_lag_p95_s","divergence_pct"],"properties":{"quorum_ratio":{"type":"object","required":["observed","target","ok"],"additionalProperties":false,"properties":{"observed":{"type":"number"},"target":{"type":"number"},"ok":{"type":"boolean"}}},"failover_time_p95_s":{"type":"object","required":["observed","target","ok"],"additionalProperties":false,"properties":{"observed":{"type":"number"},"target":{"type":"number"},"ok":{"type":"boolean"}}},"staleness_p95_s":{"type":"object","required":["observed","target","ok"],"additionalProperties":false,"properties":{"observed":{"type":"number"},"target":{"type":"number"},"ok":{"type":"boolean"}}},"cdc_lag_p95_s":{"type":"object","required":["observed","target","ok"],"additionalProperties":false,"properties":{"observed":{"type":"number"},"target":{"type":"number"},"ok":{"type":"boolean"}}},"divergence_pct":{"type":"object","required":["observed","target","ok"],"additionalProperties":false,"properties":{"observed":{"type":"number"},"target":{"type":"number"},"ok":{"type":"boolean"}}}}},"status":{"type":"string","enum":["PASS","FAIL"]}}}
```

**`data/cdc/schemas/q1_boss_report.schema.json`**

```json
{"$id":"https://ce.local/schemas/q1_boss_report.schema.json","$schema":"http://json-schema.org/draft-07/schema#","title":"Q1 Boss Final Report","type":"object","additionalProperties":false,"required":["schema_version","timestamp_utc","sprints","status"],"properties":{"schema_version":{"type":"integer","const":1},"timestamp_utc":{"type":"string","format":"date-time"},"sprints":{"type":"object","additionalProperties":false,"required":["s1","s2","s3","s4","s5","s6"],"properties":{"s1":{"type":"object","required":["status","notes"],"additionalProperties":false,"properties":{"status":{"type":"string","enum":["PASS","FAIL"]},"notes":{"type":"string"}}},"s2":{"type":"object","required":["status","notes"],"additionalProperties":false,"properties":{"status":{"type":"string","enum":["PASS","FAIL"]},"notes":{"type":"string"}}},"s3":{"type":"object","required":["status","notes"],"additionalProperties":false,"properties":{"status":{"type":"string","enum":["PASS","FAIL"]},"notes":{"type":"string"}}},"s4":{"type":"object","required":["status","notes"],"additionalProperties":false,"properties":{"status":{"type":"string","enum":["PASS","FAIL"]},"notes":{"type":"string"}}},"s5":{"type":"object","required":["status","notes"],"additionalProperties":false,"properties":{"status":{"type":"string","enum":["PASS","FAIL"]},"notes":{"type":"string"}}},"s6":{"type":"object","required":["status","notes"],"additionalProperties":false,"properties":{"status":{"type":"string","enum":["PASS","FAIL"]},"notes":{"type":"string"}}}}},"status":{"type":"string","enum":["PASS","FAIL"]}}}
```

## 8. Conteúdos dos Bundles (S6)

**`s6_validation/thresholds.json`** (exemplo inicial — editável sob controle de versão)

```json
{"version":1,"quorum_ratio_min":0.6667,"failover_time_p95_s_max":60.0,"staleness_p95_s_max":30.0,"cdc_lag_p95_s_max":120.0,"divergence_pct_max":1.0}
```

**`s6_validation/metrics_static.json`** (exemplo inicial — editável)

```json
{"version":1,"quorum_ratio":0.92,"failover_time_p95_s":7.8,"staleness_p95_s":12.0,"cdc_lag_p95_s":45.0,"divergence_pct":0.4}
```

## 9. Regras de Reprodutibilidade

* **UTF‑8** e newline em todos os arquivos de entrada/saída.
* `bundle.sha256`: SHA‑256 sobre concatenação canônica de `thresholds.json` (primeiro) e `metrics_static.json` (depois), ambos serializados com `sort_keys=true`, `separators=(",",":")`, `ensure_ascii=false` e newline final.
* `report.md` com ordenação e formatação estáveis (sem timestamps e sem valores dependentes de locale).

## 10. Workflows de CI (política)

### 10.1 `s6-scorecards.yml`

* **Triggers:** `schedule` 06:00 UTC, `workflow_dispatch`, `pull_request` filtrando `s6_validation/**`, `scripts/scorecards/**`, `dashboards/grafana/**`, o próprio workflow.
* **Concurrency:** `s6-scorecards-${{ github.ref }}`, `cancel-in-progress: true`.
* **Ambiente:** `LC_ALL=C.UTF-8`, `LANG=C.UTF-8`.
* **Actions:** usar `actions/checkout`, `actions/setup-python`, `actions/github-script`, `actions/upload-artifact` **pinadas por SHA** e registradas em `actions.lock` (com data/autor/justificativa). Política de rotação: revisão mensal e bump controlado via PR dedicado.
* **Steps (ordem):** checkout → setup‑python 3.11 (cache pip) → instalar `ruff==0.6.8`, `yamllint==1.35.1`, `pytest==8.3.3`, `hypothesis==6.103.0` → instalar `jq` → `yamllint .` → `ruff scripts/` → `pytest -q` → validar painel Grafana via `jq` → validar higiene UTF‑8/EOL dos JSONs → `python scripts/scorecards/s6_scorecards.py` → upload artefatos `out/s6_scorecards/` → ler `guard_status.txt` e `exit 1` em `FAIL` → se PR, comentar via `github-script`; **fallback** para `GITHUB_STEP_SUMMARY` com badge e resumo 1‑linha.
* **Timeouts:** `timeout-minutes: 20` no job; nenhum step sem limite.

### 10.2 `q1-boss-final.yml`

* **Triggers:** `workflow_dispatch` (input opcional `release_tag`), `pull_request` (filtros amplos `.github/workflows/**`, `scripts/**`, `s*/**`, `docs/**`, `dashboards/**`), opcional `schedule` 07:00 UTC.
* **DAG:** jobs paralelos `s1..s6` + agregador `boss` com `needs` em todos.
* **Sprints (escopo mínimo determinístico):**

  * S1: lint/format + teste base + healthcheck SUT fake/offline.
  * S2: build estático + testes de módulo + microbench determinístico.
  * S3: observabilidade “smoke” offline (regras/labels, evidências em `out/obs_gatecheck/*`).
  * S4: ORR “lite” offline (validar YAMLs/workflows; TLA só se presente; nunca falhar por ausência do `.tla`).
  * S5: validação de dashboards (estrutura/labels via `jq`).
  * S6: executar scorecards desta sprint.
* **Agregação (`boss`):** ler `guard_status.txt` de cada sprint → compor `report.json/md` global conforme schema → gerar badge e `dag.svg` → comentar no PR (fallback para summary) → gate final por `guard_status.txt` global.
* **Timeouts:** `timeout-minutes: 60` no job agregador; `s1..s6`: 15 cada.

## 11. Painel Grafana (S6)

* Arquivo: `dashboards/grafana/scorecards_quorum_failover_staleness.json`.
* Conteúdo: 5 cards `stat` (quorum_ratio, failover_time_p95_s, staleness_p95_s, cdc_lag_p95_s, divergence_pct), `schemaVersion` recente, time range `now-24h`→`now`, templating vazio.

## 12. Documentação

* `docs/scorecards/S6_SCORECARDS.md`: objetivo, execução local, leitura do report, semântica do guard, troubleshooting (schema/UTF‑8/EOL), política de migração (`schema_version` e `version`), governança de `actions.lock` e rotação.

## 13. Testes (matriz)

**Unidade e property‑based:**

* Avaliação PASS/FAIL por métrica individual e combinações.
* Fronteiras (igual ao limite; ±epsilon). Formatação numérica (casas por métrica).
* Metamórfico: relaxar thresholds não cria regressão; piorar métricas além do limite ⇒ FAIL.
* Idempotência: 2× execuções com mesmo input ⇒ `bundle.sha256` e `report.md` idênticos (byte a byte).
* Erros: arquivo ausente; JSON inválido; chaves extras; domínio violado; encoding incorreto; métrica ausente ⇒ FAIL.
* Liveness: jobs encerram antes dos timeouts definidos.

**Boss Final:**

* Combinações de `s1..s6` PASS/FAIL; prova de que qualquer FAIL ⇒ FAIL global.
* Geração válida de `badge.svg` e `dag.svg`.
* Fallback de PR comment (summary) ao simular falha controlada do `github-script`.
* Reprodutibilidade em runner limpo adicional (job matrix `clean_runner: [true,false]`).

## 14. Critérios de Aceite (DoD)

* Workflows `s6-scorecards` e `q1-boss-final` executam localmente (smoke) e no CI Ubuntu 22.04 sem segredos.
* `guard_status.txt` contém apenas `PASS`/`FAIL` com newline final; gates falham PRs corretamente.
* Artefatos completos nas pastas `out/` especificadas; hashes determinísticos; reports válidos contra schemas.
* Painel Grafana importável; docs presentes.
* Testes cobrindo todos os itens da matriz; idempotência e liveness comprovadas; matrix com runner limpo passa.
* `actions.lock` presente e citado no workflow; rotação documentada.

## 15. Riscos e Mitigações

* Falha na instalação de deps: fixar versões; retry leve; logs claros.
* Variação de locale: fixar `LC_ALL/LANG`.
* Não determinismo de filesystem: ordenar listas/keys explicitamente.
* Falha de comentário em PR: fallback para `GITHUB_STEP_SUMMARY` com badge e links.
* Divergência de schema: validar contra schemas versionados e documentar migração.

## 16. Versão, Migração e Manutenção

* `schema_version` dos reports inicia em 1; evolução por bump semântico e migrações no doc.
* `version` em `thresholds.json` e `metrics_static.json` inicia em 1; alterações compatíveis exigem doc de migração.
* `actions.lock`: mapa `{action → sha, date, author, rationale}`; revisões mensais.

## 17. Procedimento de Entrega

1. Abrir branch `wave-1/s6-scorecards`.
2. Adicionar arquivos conforme manifest desta spec.
3. Executar smoke local: `make s6-scorecards || true` e `make q1-boss-final || true`.
4. Abrir PR “S6: scorecards + Boss Final Q1 (determinístico)”.
5. Merge após CI verde e checklist DoD atendido.

## 18. Checklist de Veto (Bertrand)

* [ ] Schemas presentes e aplicados (incl. reports); mensagens contratuais objetivas.
* [ ] Decimal + epsilon aplicado; ordenação estável; UTF‑8 + newline; formatos numéricos exigidos.
* [ ] Actions pinadas por SHA; `LC_ALL=C.UTF-8`; concurrency e timeouts configurados; `actions.lock` incluído.
* [ ] Artefatos S6 completos; `bundle.sha256` e `report.md` determinísticos.
* [ ] Workflow Boss: DAG, agregação, badge e dag SVGs; PR comment com fallback; gate global.
* [ ] Testes de fronteira, metamórficos, idempotência, liveness e erros de schema/higiene; matrix com runner limpo.

---

> Esta é a **especificação oficial e final** da Sprint 6 (Q1). Qualquer implementação deve obedecer integralmente a este documento. Em caso de conflito, prevalecem os contratos e limites definidos aqui.
