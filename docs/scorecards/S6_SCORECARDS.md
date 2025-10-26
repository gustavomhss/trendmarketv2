Este runbook consolida as instruções finais da Sprint 6 (Q1) conforme a SPEC vMasterpiece-Final.

## Objetivo

Gerar scorecards determinísticos com contratos DbC explícitos, validação por schema e publicação automática via GitHub Actions.

## Fluxo operacional

1. `python scripts/scorecards/s6_scorecards.py`
2. Validar `out/s6_scorecards/report.json` contra `schemas/report.schema.json`.
3. Rodar `scripts/watchers/s6_scorecard_guard.sh` para garantir `guard_status.txt == PASS`.
4. Executar `python scripts/boss_final/aggregate_q1.py` para consolidar no Boss Final.

## Contratos e formatos

- **Metricas fixas**: `quorum_ratio`, `failover_time_p95_s`, `staleness_p95_s`, `cdc_lag_p95_s`, `divergence_pct`.
- **Schemas**: objetos planos com `version`/`metrics` (thresholds e observações) e `report.json` com `status` em caixa alta, bloco `metrics.{id}` e `bundle_sha256` calculado a partir de `thresholds.json` + `metrics_static.json` (JSON canônico, chaves ordenadas, separadores `,`/`:`, newline final).
- **Decimal**: contexto `prec=28`, `ROUND_HALF_EVEN`, epsilon `1e-12` aplicado nas comparações `gte`/`lte`.
- **Formatação**:
  - Percentuais: uma casa decimal e sufixo `%` (ex.: `99.7%`).
  - Razões: quatro casas decimais (ex.: `0.1935`).
  - Tempos: três casas decimais + `s` (ex.: `2.103s`).
- **Ordenação**: sempre iterar `metrics` na ordem fixa acima em Markdown, SVG, comentários e testes.
- **DbC**: entradas ausentes ou inválidas geram erros `S6-E-*` ou `BOSS-E-*` e encerram com `guard_status=FAIL`.

## Governança de Actions

As ações GitHub devem ser fixadas por SHA em `.github/workflows/*.yml` e documentadas em `actions.lock`. Rotacionar SHAs a cada 30 dias ou quando surgir CVE crítico. Procedimento:

1. Abrir PR dedicado com atualização das versões.
2. Validar hash/assinatura do commit da action.
3. Atualizar registro correspondente em `actions.lock` com data, autor e racional.

## Troubleshooting

| Sintoma | Ação |
| --- | --- |
| `UTF8:path` ao rodar pipeline | Converter arquivo para UTF-8 puro e remover BOM. |
| `CRLF:path` | Aplicar `dos2unix` ou regravar o arquivo com finais de linha `\n`. |
| `S6-E-SCHEMA` ou `BOSS-E-STAGE-SCHEMA` | Validar JSONs com `python -m jsonschema --instance ... --schema ...`. |
| `guard_status.txt` = `FAIL` | Consultar `report.md` e executar plano de ação descrito no campo `guidance` da métrica. |

## Geração de relatórios

Os relatórios devem ficar em `out/s6_scorecards/` e `out/q1_boss_final/`. Ambos contêm `report.json`, `report.md`, `badge.svg`, `pr_comment.md`, `bundle.sha256` e `guard_status.txt`. Nunca editar manualmente estes arquivos — execute os scripts correspondentes.

## Rotação e fallback

- Scorecards diários às 06:00 UTC (workflow `s6-scorecards`).
- Boss Final às 07:00 UTC com agregação das etapas `s1..s6` (workflow `q1-boss-final`).
- Comentários de PR sempre acompanham badge; fallback escreve no `GITHUB_STEP_SUMMARY`.

## Referências adicionais

- Schemas: `schemas/thresholds.schema.json`, `schemas/metrics.schema.json`, `schemas/report.schema.json`, `schemas/q1_boss_report.schema.json`.
- Dados de validação: `s6_validation/thresholds.json`, `s6_validation/metrics_static.json`, `s6_validation/README.md`.
- Dashboards: `dashboards/grafana/scorecards_quorum_failover_staleness.json` (janela `now-24h → now`).
# Sprint 6 Scorecards — Runbook

Este runbook descreve o contrato da Sprint 6 para gerar scorecards determinísticos,
alimentar os guardas de CI/CD e publicar evidências auditáveis. A fonte de verdade
continua sendo a [especificação Sprint 6 (Q1)](../DNA/quarters/Q1/Sprint%206%20(Q1).md);
este documento consolida os passos operacionais exigidos pela governança.

## Objetivo

Calcular o veredito PASS/FAIL para os cinco indicadores mandatórios — `quorum_ratio`,
`failover_time_p95_s`, `staleness_p95_s`, `cdc_lag_p95_s` e `divergence_pct` — a
partir dos contratos versionados em `s6_validation/`. Os resultados alimentam o
workflow `s6-scorecards` e o estágio S6 do pipeline Boss Final.

## Entradas canônicas

Os arquivos em `s6_validation/` são as únicas entradas para o cálculo offline:

- `thresholds.json`: objeto plano com `schema`, `schema_version`, `timestamp_utc`
  e os cinco alvos (`quorum_ratio`, `failover_time_p95_s`, `staleness_p95_s`,
  `cdc_lag_p95_s`, `divergence_pct`).
- `metrics_static.json`: objeto plano com `schema`, `schema_version`,
  `timestamp_utc` e os cinco valores observados correspondentes.

Ambos validam contra os schemas Draft‑07 (`schemas/thresholds.schema.json` e
`schemas/metrics.schema.json`) com `schema_version: 2` protegido por `const`.
Formatação canônica (`sort_keys=true`, separadores `(",",":")`, newline final e
UTF‑8) é obrigatória para preservar o hash do bundle.

## Aritmética e EPS

A avaliação utiliza `Decimal` (precisão 28, `ROUND_HALF_EVEN`) com epsilon fixo
`1e-12`. Cada métrica aplica o comparador definido no contrato (`gte` para
`quorum_ratio`, `lte` para as demais). O resultado global é PASS apenas se todos
os indicadores estiverem dentro dos limites após considerar o epsilon.

## Execução local

```bash
PYTHONHASHSEED=0 PYTHONUTF8=1 HYPOTHESIS_PROFILE=ci HYPOTHESIS_SEED=12345 \
  python scripts/scorecards/s6_scorecards.py
python -m jsonschema --instance out/s6_scorecards/report.json --schema schemas/report.schema.json
```

A execução gera `out/s6_scorecards/` contendo `report.json`, `report.md`,
`pr_comment.md`, `badge.svg`, `scorecard.svg`, `bundle.sha256` e `guard_status.txt`.
O guard é FAIL se qualquer métrica reprovar; o watcher `scripts/watchers/s6_scorecard_guard.sh`
exige `guard_status.txt` = `PASS`.

## Estrutura do report

`report.json` segue o schema Draft‑07 `schemas/report.schema.json`:

- `schema`: `trendmarketv2.sprint6.report`
- `schema_version`: `2`
- `timestamp_utc`: instante da avaliação
- `status`: `PASS` ou `FAIL`
- `metrics.<metric>.{observed,target,ok}`: valores em ponto flutuante
- `inputs.{thresholds,metrics}.{schema,schema_version,timestamp_utc}`:
  proveniência dos arquivos de entrada
- `bundle.sha256`: hash do bundle (thresholds + metrics em serialização canônica)

Os artefatos markdown e SVG são regenerados a partir desse payload; qualquer
edição manual é proibida.

## Governança

1. Alterações em `s6_validation/**` exigem validação contra os schemas, execução
   do script e atualização dos artefatos em `out/s6_scorecards/`.
2. `actions.lock` deve listar cada ação por SHA, data, autor e justificativa.
3. Toda revisão precisa de aprovação dupla (scorecards + observabilidade) e deve
   referenciar a seção aplicável da especificação.
4. Pull requests devem anexar o hash do bundle (`out/s6_scorecards/bundle.sha256`).

## CI (`.github/workflows/s6-scorecards.yml`)

O workflow executa em matriz (`clean_runner: [false,true]`) com `concurrency`
por branch. As etapas principais:

1. Instalação de dependências (`ruff`, `pytest`, `hypothesis`, `jsonschema`, `jq`).
2. Linters (`yamllint`, `ruff check`, `ruff format --check`).
3. Validação do painel Grafana via `jq` com as cinco métricas exigidas.
4. `pytest -q` para a suíte de scorecards/Boss Final.
5. Higiene UTF‑8/EOL.
6. Execução do script `scripts/scorecards/s6_scorecards.py` e validação do schema
do relatório gerado.
7. Upload de artefatos, leitura do guard e comentário no PR com fallback para o
   `GITHUB_STEP_SUMMARY` em caso de falha da API.

O job falha se qualquer etapa crítica retornar status diferente de `PASS` ou se o
`guard_status.txt` não contiver `PASS`.

## Pipeline Boss Final

O estágio S6 do `q1-boss-final` reutiliza o mesmo script e valida o guard antes de
agregar os resultados. O agregador (`scripts/boss_final/aggregate_q1.py`) só emite
PASS se todos os estágios (S1–S6) passaram nas variantes `primary` e `clean`.

## Troubleshooting

- **Schema**: use `python -m jsonschema` para diagnosticar mensagens específicas.
- **Hash divergente**: verifique ordenação de chaves e newline final nos JSONs.
- **Falha em métricas**: inspeccione `out/s6_scorecards/report.md` para detalhes
  de cada indicador e siga o runbook indicado pela sprint.

## Auditoria

Arquive sempre os artefatos regenerados (Markdown, SVG, bundle hash) e cite o
commit correspondente na revisão. Isso garante rastreabilidade completa conforme
as exigências da Sprint 6.
