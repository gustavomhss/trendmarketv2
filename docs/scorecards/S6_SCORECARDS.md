# Sprint 6 Scorecards — Runbook

Este runbook consolida as instruções finais da Sprint 6 (Q1) conforme a SPEC vMasterpiece-Final.

## Objetivo

Gerar scorecards determinísticos com contratos DbC explícitos, validação por schema e publicação automática via GitHub Actions.

## Fluxo operacional

1. `python scripts/scorecards/s6_scorecards.py`
2. Validar `out/s6_scorecards/report.json` contra `schemas/report.schema.json`.
3. Rodar `scripts/watchers/s6_scorecard_guard.sh` para garantir `guard_status.txt == PASS`.
4. Executar `python scripts/boss_final/aggregate_q1.py` para consolidar no Boss Final.

## Contratos e formatos

- **Decimal**: contexto `prec=28`, `ROUND_HALF_EVEN`, epsilon `1e-12` aplicado nas comparações.
- **Formatação**:
  - Percentuais: uma casa decimal e sufixo `%` (ex.: `99.7%`).
  - Razões: quatro casas decimais (ex.: `0.1935`).
  - Tempos: três casas decimais + `s` (ex.: `2.103s`).
- **Ordenação**: métricas sempre avaliadas na ordem fixa `quorum_ratio`, `failover_time_p95_s`, `staleness_p95_s`, `cdc_lag_p95_s`, `divergence_pct`.
- **Entradas**:
  - `thresholds.json`: objeto plano com `version`, `timestamp_utc` e chaves de limite (`*_min`/`*_max`) para cada métrica mandatória.
  - `metrics_static.json`: objeto plano com `version`, `timestamp_utc` e valores observados para as cinco métricas mandatórias.
- **Saída (`report.json`)**: contém `timestamp_utc`, `status` em maiúsculas e bloco `metrics.<metric>.{observed,target,ok}` para cada métrica.
- **DbC**: entradas ausentes ou inválidas geram erros `S6-E-*` ou `BOSS-E-*` e encerram com `guard_status=FAIL`.

## Governança de Actions

As ações GitHub devem ser fixadas por SHA em `.github/workflows/*.yml` e documentadas em `actions.lock`. Cada slug mapeia para um objeto com as chaves `sha`, `date`, `author` e `rationale`. Rotacionar SHAs a cada 30 dias ou quando surgir CVE crítico. Procedimento:

1. Abrir PR dedicado com atualização das versões.
2. Validar hash/assinatura do commit da action.
3. Atualizar a entrada `actions.<slug>` em `actions.lock` garantindo o objeto `{sha, date, author, rationale}`.

O arquivo `actions.lock` deve mapear cada slug de action em `actions:` para um objeto com os campos `sha`, `pinned_at`, `author`
e `rationale`, garantindo leitura determinística por ferramentas automatizadas.

## Troubleshooting

| Sintoma | Ação |
| --- | --- |
| `UTF8:path` ao rodar pipeline | Converter arquivo para UTF-8 puro e remover BOM. |
| `CRLF:path` | Aplicar `dos2unix` ou regravar o arquivo com finais de linha `\n`. |
| `S6-E-SCHEMA` ou `BOSS-E-STAGE-SCHEMA` | Validar JSONs com `python -m jsonschema --instance ... --schema ...`. |
| `guard_status.txt` = `FAIL` | Consultar `report.md` e executar plano de ação da métrica descrito na seção “O que fazer agora”. |

## Geração de relatórios

Os relatórios devem ficar em `out/s6_scorecards/` e `out/q1_boss_final/`. Ambos contêm `report.json`, `report.md`, `badge.svg`, `pr_comment.md`, `bundle.sha256` e `guard_status.txt`. Nunca editar manualmente estes arquivos — execute os scripts correspondentes.

### Exemplos de bundles

- `s6_validation/thresholds.json`

  ```json
  {"version":1,"timestamp_utc":"2024-09-01T06:00:00Z","quorum_ratio_min":0.6667,"failover_time_p95_s_max":60.0,"staleness_p95_s_max":30.0,"cdc_lag_p95_s_max":120.0,"divergence_pct_max":1.0}
  ```

- `s6_validation/metrics_static.json`

  ```json
  {"version":1,"timestamp_utc":"2024-09-01T05:55:00Z","quorum_ratio":0.92,"failover_time_p95_s":7.8,"staleness_p95_s":12.0,"cdc_lag_p95_s":45.0,"divergence_pct":0.4}
  ```

## Rotação e fallback

- Scorecards diários às 06:00 UTC (workflow `s6-scorecards`).
- Boss Final às 07:00 UTC com agregação das etapas `s1..s6` (workflow `q1-boss-final`).
- Comentários de PR sempre acompanham badge; fallback escreve no `GITHUB_STEP_SUMMARY`.

## Referências adicionais

- Schemas: `schemas/thresholds.schema.json`, `schemas/metrics.schema.json`, `schemas/report.schema.json`, `schemas/q1_boss_report.schema.json`.
- Dados de validação: `s6_validation/thresholds.json`, `s6_validation/metrics_static.json`.
- Dashboards: `dashboards/grafana/scorecards_quorum_failover_staleness.json` (janela `now-24h → now`).

