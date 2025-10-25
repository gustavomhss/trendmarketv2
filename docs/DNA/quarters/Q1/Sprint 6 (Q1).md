# Q1 • Sprint 6 — **Especificação Completa** (GA Interno • 30 dias verdes) — **vFinal+ (gap‑free)**

**Marcador:** #201293 · **Trimestre:** Q1 (Sprint **final** S1–S6)
**Status:** **vFinal+** (revisão tripla + deep‑dive de gaps, conflitos e lacunas **feita**; correções **aplicadas**)
**Liderança executiva:** Steve Jobs (foco)
**Conselho técnico:** Donald Knuth (precisão), Leslie Lamport (tempo/invariantes), Alan Kay (contratos/arquitetura), Fernando Pérez (reprodutibilidade), Vitalik Buterin (governança)

> **O que fechamos nesta vFinal+:** definimos **unidades e fórmulas canônicas**, **janelas temporais** (rolling/UTC), **política de dados faltantes**, **RACI com MTTA/MTTR**, **guardas no CI** (artifact + schema), **matriz de verificação** requisito→query→evidência→owner, **runbooks/playbooks com rollback**, **política de flags** e **retenção/privacidade**. Corrigimos ambiguidade de métricas (labels), adicionamos **tolerâncias e backfill**, e previmos **degradação segura**.

---

## 0) Objetivo (imutável)

Encerrar Q1 com **GA Interno** comprovado por **30 dias verdes** (sem P1, uptime ≥ 99,90%, burn < 1×/30d), sustentado por **scorecards automatizados**, **observabilidade** e **evidências versionadas**. Entrega final: **readout** aprovado + **handoff** para Q2.

---

## 1) Escopo e entregáveis (executivo)

1. **Operação (30d)**: `P1=0`, `uptime ≥ 99.90%`, `error_budget_burn < 1×/30d`.
2. **Preço & Oráculos**: `staleness_p95_ms ≤ 30000`, `twap_divergence_pct ≤ 1.0` (5m), `failover_time_s < 60`.
3. **Auto‑resolução & Fees**: `cooldown_s == 300`, `|Δfee|_5m_pct ≤ 20`, `bounds_ok = true`, trilha auditável.
4. **Moderação**: `MTTD ≤ 300 s`, `MTTM ≤ 900 s`, `audit_coverage ≥ 99%`.
5. **Dados & CDC/DQ**: `dbt_tests_pass_rate = 100%`, `cdc_lag_p95_s ≤ 120`, `schema_drift = 0`.
6. **Observabilidade & Scorecards**: rules Prometheus + Grafana; **scorecards diários/semanais** versionados (artifact).
7. **Segurança & LGPD**: SAST/Secrets/SBOM verdes; amostra **sem PII**.
8. **Readout & Handoff**: `s6_validation/` completo + CAPAs/ADRs + assinaturas multi‑área.

---

## 2) Critérios de aceite (Definition of Awesome)

**Janelas temporais & base de tempo**

* **Rolling**: 24h, 7d, 30d, ancoradas em **UTC** (sem TZ locais).
* **Buckets**: 1m (coleta), 5m (agregação de p95), 1h/24h/30d (scorecards).
* **Dados faltantes**: até **3%** de pontos podem ser **carregados por forward‑fill** (FF) limitado a 10 min; acima disso, marcar `data_gap=true` (degradação controlada) e abrir CAPA.

**Aceites formais**

* **Confiabilidade**: `incidents.P1 == 0`; `uptime_ratio ≥ 0.9990`; `error_budget_burn_30d < 1.0`.
* **Preço/Oráculos**: `p95(staleness_ms) ≤ 30000`; `p95(twap_divergence_pct) ≤ 1.0`; `p95(failover_time_s) < 60`.
* **Fees**: `cooldown_s == 300`; `max_over_time(delta_fee_5m_pct[30d]) ≤ 20`; `min_over_time(bounds_ok[30d]) == 1`.
* **Moderação**: `p95(MTTD) ≤ 300s`; `p95(MTTM) ≤ 900s`; `audit_coverage ≥ 99%`.
* **Dados**: `dbt_pass_rate == 100%`; `p95(cdc_lag_s) ≤ 120`; `schema_drift == 0`.
* **Observabilidade**: dashboards exportados (JSON) versionados; watchers/hooks ativos.
* **Segurança**: segredos=0; amostra de logs=0 PII (evidência).
* **Readout**: publicado e assinado (PO/Eng/Data/SRE/Sec/PM).

---

## 3) Dicionário KPI (fonte → query → evidência)

| KPI               | Série/Métrica                     | Query/Regra (canônica)                            | Unidade | Limite  | **Evidência**               | Owner    |
| ----------------- | --------------------------------- | ------------------------------------------------- | ------- | ------- | --------------------------- | -------- |
| Uptime (30d)      | `ops:uptime_ratio{service="mbp"}` | SLO calc (rolling 30d)                            | %       | ≥ 99.90 | `kpi_timeseries.json`       | SRE      |
| Burn (30d)        | `ops:error_budget_burn_30d`       | **burn = max(0,1−uptime_ratio)×(30d/SLO_window)** | ×       | < 1.0   | scorecard + `findings.json` | SRE      |
| Staleness p95     | `mbp:oracle:staleness_ms`         | `quantile_over_time(0.95, …[5m])`                 | ms      | ≤ 30000 | dashboard/scorecard         | PM/BC    |
| TWAP diverg p95   | `mbp:twap:diverg_pct`             | p95 5m                                            | %       | ≤ 1.0   | dashboard/scorecard         | PM       |
| Failover time p95 | `mbp:oracle:failover_time_s`      | drill timer                                       | s       | < 60    | `out/drills/*.md`           | PM/BC    |
| Δ fee 5m (max)    | `mbp:fees:delta_fee_5m_pct`       | `max_over_time(…[30d])`                           | %       | ≤ 20    | scorecard                   | PM/Eng   |
| Cooldown viol     | `mbp:fees:cooldown_s_violation`   | count                                             | flag    | 0       | scorecard                   | Eng      |
| DBT pass          | `dbt:tests:pass_rate`             | `sum(passed)/sum(total)`                          | %       | 100     | `target/run_results.json`   | Data     |
| CDC lag p95       | `cdc:lag_p95_s`                   | p95                                               | s       | ≤ 120   | scorecard                   | Data/SRE |
| Schema drift      | `cdc:schema_drift`                | count                                             | #       | 0       | scorecard                   | Data     |
| MTTD p95          | `mbp:mod:mttd_s`                  | p95                                               | s       | ≤ 300   | scorecard/logs              | PM/SRE   |
| MTTM p95          | `mbp:mod:mttm_s`                  | p95                                               | s       | ≤ 900   | scorecard/logs              | PM/SRE   |
| Audit coverage    | `mbp:mod:audit_coverage`          | `% eventos com JSONL`                             | %       | ≥ 99    | scorecard                   | Sec/PM   |

**Notas canônicas**: Unidades fixas; nomes/labels **imexíveis**; timezone **UTC**.

---

## 4) Governança (RACI, MTTA/MTTR, flags)

**RACI por domínio**
Ops/SRE (uptime/burn/CDC), PM/BC (oráculos/preço/failover), PM/Eng (fees), Data (DBT/DQ/CDC), Sec (SAST/Secrets/PII).
**Severidade (P1/P2)**: P1 = unavailability/violação de red line por >5 min; P2 = risco alto/violação transitória <5 min.
**MTTA/MTTR**: P1 **MTTA ≤ 5 min**, **MTTR ≤ 60 min**; P2 **MTTA ≤ 15 min**, **MTTR ≤ 4 h**.
**Escalonamento:** NOC → SRE (5m) → Eng/PM (15m) → Leadership (30m).
**Política de flags (freeze):** alterações de comportamento somente via Change Control (PR + aprovação dupla); **auto‑rollback** quando red line cruzada.

---

## 5) Workflows & Guards (CI/CD)

### 5.1 `s6-scorecards.yml` (cron diário, read‑only)

* Gera `out/scorecards/**` (MD/JSON) e publica artifact **`s6-scorecards`**.
* **Timeouts:** fonte ≤ 30s, total ≤ 5m; **sem executáveis externos**.

### 5.2 Guard de Scorecards (PR‑release)

* Job `s6-scorecards-guard`: falha o PR se **não houver artifact** nas últimas 24h **ou** se `kpi_timeseries.json`/`alerts_summary.json` não passarem no **schema** previsto (§11).
* Verifica que os KPIs obrigatórios estão presentes e **dentro das unidades** corretas.

### 5.3 `s4_orr_exec` (auxiliar)

* Mantido para checks técnicos S4+S5; **não gateia** S6; agrega evidências sob demanda.

---

## 6) Observabilidade (métricas & painéis)

**Registro de métricas (naming):** `namespace:domain:metric{service="mbp",…}`.
**Métricas canônicas:** oracles (`staleness_ms`,`diverg_pct`,`quorum_ratio`,`failover_time_s`), twap (`window_s`,`diverg_pct`), fees (`cooldown_s_violation`,`delta_fee_5m_pct`,`bounds_ok`), moderação (`mttd_s`,`mttm_s`,`audit_coverage`), dados (`dbt_pass_rate`,`cdc_lag_p95_s`,`schema_drift`), operação (`uptime_ratio`,`error_budget_burn_30d`).
**Painéis Grafana (export JSON no repo):** cards p95/p99, tendência 30d, limites SLO; garantir **`quorum_ratio`** e **`failover_time_p95_s`**.

**Tolerância & backfill:** dados atrasados até 10 min entram no ciclo; acima disso, marcar `data_gap=true` e sinalizar no card.

---

## 7) Watchers → Hooks (contratos executáveis)

**Regras exemplo (código):**

* `pm.oracle_staleness`: se `staleness_ms > 30000` por 2 janelas, aciona **`twap_failover`** (troca fonte em < 60 s) e grava **audit JSON**.
* `mbp_price_spike_divergence`: se `diverg_pct > 1.0`, aciona **`freeze_fees`** (trava Δ; mantém clamp; notifica).
* `cdc_lag_guard`: se `cdc_lag_p95_s > 120`, aciona **`scale_ingest`** (mais paralelismo) + alerta Data/SRE.

**Contrato de hook (JSON):**

```json
{
  "hook": "twap_failover",
  "reason": "staleness_ms>60000",
  "ts_utc": "2025-03-10T09:00:01Z",
  "actor": "watcher:pm.oracle_staleness",
  "action": {"from": "source_primary", "to": "source_backup"},
  "result": "ok",
  "evidence": "out/drills/twap_failover_2025-03-10.md"
}
```

---

## 8) Playbooks & Drills (com rollback)

* **TWAP failover**: simular primária com `staleness>60000ms`; comprovar `failover_time_s<60`; rollback para primária quando `staleness<30000ms`.
* **CDC delay**: induzir atraso; comprovar `cdc_lag_p95_s≤120`; rollback com replay.
* **Fee guard**: forçar spikes; comprovar `Δ≤20%/5m` + cooldown; rollback para `baseline_fee`.
* **Moderation burst**: 50–100 eventos; comprovar `MTTD/MTTM`; rollback drena fila.

**Template de relatório (MD):** objetivo, setup, passos, métricas medidas, evidências (links/prints), **assinatura** (owner) e timestamp UTC.

---

## 9) Dados, Privacidade & Retenção

* **DBT**: `dbt_pass_rate == 100%` (versionar `run_results.json`).
* **CDC**: painel `cdc_lag_p95_s`; alarme `cdc_lag_guard`.
* **PII**: amostra de logs (>10k linhas) com detector; **0 matches**; se houver, mascarar + **CAPA** com prazo e owner.
* **Retenção de evidências**: `s6-scorecards` (artifacts) por **90 dias**; `s6_validation/` no repo (permanente).
* **Minimização**: logs e artifacts **somente texto**; sem dumps binários.

---

## 10) Validação, Rubrica & Red lines

**Rubrica**

* **GO**: Coverage ≥ 85; red_lines=0; KPIs centrais OK em 7d+30d.
* **CONDITIONAL**: 70–84.9 ou 1 gap não‑crítico com CAPA aberta.
* **NO‑GO**: qualquer red line.

**Red lines**

1. `P1>0` ou `error_budget_burn_30d ≥ 1×`.
2. `uptime_ratio < 0.9990`.
3. `staleness_p95_ms > 30000` ou `twap_divergence_pct > 1.0` ou `failover_time_s ≥ 60`.
4. `cooldown_s != 300` ou `delta_fee_5m_pct > 20` ou `bounds_ok == false`.
5. `dbt_pass_rate < 100%` ou `cdc_lag_p95_s > 120` ou `schema_drift > 0`.
6. `hook_coverage < 98%` ou `audit_coverage < 99%`.
7. Segredos vazando ou PII detectada.

**Decisão final**: exige **assinaturas** (PO/Eng/Data/SRE/Sec/PM) e publicação de readout.

---

## 11) Estrutura de artefatos & Schemas

```
artifacts/
  s6-scorecards/
    out/scorecards/scorecards_daily.md
    out/scorecards/scorecards_weekly.md
    out/scorecards/kpi_timeseries.json
    out/scorecards/alerts_summary.json

repo/
  s6_validation/
    decision.txt
    summary.md
    checks_table.md
    findings.json
    scorecards_findings.json
    drills_findings.json
    obs_findings.json
    governance_findings.json
    security_findings.json
    manifest.json
```

**Schemas (resumo)**

* `kpi_timeseries.json`: `{ kpi, unit, window:"24h|7d|30d", points:[{ts_utc, value}] }[]`
* `alerts_summary.json`: `{ kpi, total, p1, p2, last_24h }[]`
* `findings.json`: `{ coverage:{…}, red_lines:[], risks:[], gaps:[], recommendations:[], data_gap: boolean }`

**Reprodutibilidade**: UTF‑8, LF, newline final; ordenação estável; `manifest.json` com **SHA‑256** de tudo.

---

## 12) Matriz de verificação (requisito → query → evidência → owner)

| Requisito           | Query/Escala         | Evidência                          | Owner    |
| ------------------- | -------------------- | ---------------------------------- | -------- |
| Uptime ≥ 99.90%     | `uptime_ratio` (30d) | scorecards + `kpi_timeseries.json` | SRE      |
| Burn < 1×/30d       | fórmula burn         | `scorecards_weekly.md`             | SRE      |
| Staleness p95 ≤ 30s | p95 5m               | dashboard + scorecard              | PM/BC    |
| TWAP diverg ≤ 1%    | p95 5m               | dashboard                          | PM       |
| Failover < 60s      | drill                | `out/drills/*.md`                  | PM/BC    |
| Δ fee ≤ 20%/5m      | max 30d              | scorecard                          | PM/Eng   |
| Cooldown = 300s     | violações=0          | scorecard                          | Eng      |
| DBT 100%            | run_results          | `target/run_results.json`          | Data     |
| CDC p95 ≤ 120s      | p95                  | scorecard                          | Data/SRE |
| Schema drift = 0    | contador             | scorecard                          | Data     |
| MTTD/MTTM           | p95                  | scorecard/logs                     | PM/SRE   |
| Audit ≥ 99%         | % eventos com JSONL  | scorecard                          | Sec/PM   |

---

## 13) Riscos & mitigação

* **Alert fatigue** → deduplicação por janela; limiares com histerese; revisão semanal.
* **Relógio/TZ** → NTP forçado; tudo em **UTC**; tolerância ±5%.
* **Dados faltantes** → FF limitado (≤10 min) + `data_gap=true`; CAPA se >3%.
* **Dependência de dashboard** → export JSON versionado + print semanal no repo.
* **CDC instável** → autoscale/backpressure + `cdc_lag_guard`.
* **Regressões de labels** → linter/guard no CI para nomes de métricas e steps.

---

## 14) Readout & Handoff (Q1 → Q2)

Sumário executivo; KPIs 30d (timeseries); incidentes/casos; CAPAs (owner+prazos); ADRs; riscos abertos; marcos Q2; links para artifacts/dashboards/bundles; **assinaturas** (PO/Eng/Data/SRE/Sec/PM).

---

## 15) Check‑list de encerramento S6 (GO)

* 30d de **scorecards** publicados + `s6_validation/` atualizado.
* Rubrica aplicada (§10) e **red lines = 0**.
* Readout publicado e assinado.
* Release criada com links + **SHA‑256**.

---

## 16) Changelog (v3 → vFinal+)

* **Unidades/tempo** padronizados (UTC, p95 5m, FF≤10m, data_gap).
* **RACI + MTTA/MTTR** e severidades P1/P2 formalizadas.
* **Guarda no CI** para artifact e schema (scorecards).
* **Matriz de verificação** completa.
* **Retenção/privacidade** e política de minimização de dados.
* **Backfill/tolerâncias** e modo de degradação segura.

> **Estado:** especificação **gap‑free** e pronta para execução/validação. Guia a criação de workflows, scorecards e pacotes de evidência com **decisão GO/NO‑GO objetiva**.
