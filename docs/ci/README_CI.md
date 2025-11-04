# S7 — ORR Exec V2

A V2 da esteira de evidências da Sprint 7 foi construída em modo blue/green. A versão antiga (V1)
continua ativa até que três execuções consecutivas desta V2 fiquem verdes. Esta página descreve
como acionar a pipeline, reproduzir localmente e interpretar os artefatos gerados.

## Como executar no GitHub Actions

1. Acesse **Actions → S7 — ORR Exec V2**.
2. Clique em **Run workflow** na branch desejada (o botão fica disponível na branch padrão).
3. Opcionalmente defina os inputs:
   - `ref`: SHA ou referência para executar (por padrão o HEAD do workflow).
   - `run_microbench`: ativa a versão estendida do microbench determinístico.
   - `run_tla`: força a execução da verificação TLA se os modelos `.tla` estiverem presentes e o
     binário `tlc` existir no runner.
4. Aguarde o término da execução. Todos os gates obrigatórios (lint-workflows, unit-tests,
   dbt-duckdb e bundle) devem ficar verdes. Os jobs opcionais (`microbench-smoke`,
   `tla-optional`, `gitleaks-optional`) não bloqueiam se estiverem marcados como ausentes.

O único artifact publicado chama-se **`s7-orr-evidence`** e contém dois arquivos:

- `out/obs_gatecheck/s7-orr-evidence-<GIT_SHA>.zip`
- `out/obs_gatecheck/SHA256SUMS`

O ZIP inclui todos os logs determinísticos em `out/obs_gatecheck/s7_v2/`, bem como o arquivo
`scorecards/s7.json`.

## Como reproduzir localmente

A execução local é idêntica à CI. No ambiente do repositório execute:

```bash
make s7_offline
```

O alvo chama o script `bin/s7_offline_gatecheck`, que roda todos os gates (yamllint,
actionlint, pytest, microbench determinístico, `dbt build` com DuckDB, além das verificações
opcionais de TLA e gitleaks caso as ferramentas estejam disponíveis). Ao final o comando imprime o
caminho do bundle e o conteúdo de `out/obs_gatecheck/SHA256SUMS`.

Os artefatos gerados localmente ficam nos mesmos caminhos que a CI:

- `out/obs_gatecheck/s7-orr-evidence-<GIT_SHA>.zip`
- `out/obs_gatecheck/SHA256SUMS`
- `scorecards/s7.json`

Os timestamps dos arquivos do ZIP são normalizados para permitir comparação byte-a-byte entre
execuções sucessivas.

## Estrutura do bundle

O arquivo ZIP contém:

- `out/obs_gatecheck/s7_v2/logs/*.log` — logs crus de cada gate (yamllint, actionlint, pytest,
  dbt, opcionalmente TLA e gitleaks).
- `out/obs_gatecheck/s7_v2/reports/*.json` — relatórios determinísticos, como o microbench e
  resultados opcionais.
- `scorecards/s7.json` — scorecard canônico da Sprint 7 V2.

O arquivo `SHA256SUMS` lista o hash SHA-256 do ZIP, permitindo a validação das evidências sem
abrir o arquivo.

## Scorecard (`scorecards/s7.json`)

Chaves obrigatórias e semântica:

| Chave                     | Tipo   | Descrição                                                                 |
|---------------------------|--------|----------------------------------------------------------------------------|
| `yaml_ok`                 | bool   | Resultado do `yamllint` (true se nenhum erro).                             |
| `actionlint_ok`           | bool   | Resultado do `actionlint` nos workflows.                                   |
| `tests_ok`                | bool   | Resultado do `pytest -q tests/test_normalizer.py tests/test_signature.py`. |
| `microbench_p50_ms`       | number | Mediana determinística (ms) do microbench smoke.                           |
| `microbench_p95_ms`       | number | Percentil 95 determinístico (ms) do microbench smoke.                      |
| `dbt_ok`                  | bool   | Resultado do `dbt build` usando DuckDB local.                              |
| `tla_ok_or_absent`        | bool   | `true` se o check TLA passou ou não era aplicável.                          |
| `gitleaks_ok_or_absent`   | bool   | `true` se gitleaks não encontrou achados ou estava ausente.                |
| `timestamp`               | string | Timestamp ISO-8601 em UTC do bundle.                                       |
| `git_sha`                 | string | SHA git usado para gerar a evidência.                                      |

## Migração de ruleset (blue/green)

1. Acompanhe o histórico do workflow **S7 — ORR Exec V2** até obter **3 execuções consecutivas
   verdes**.
2. Em **Settings → Rules → Branches → main → Pull requests → Required status checks**, adicione o
   check obrigatório `S7 — ORR Exec V2`.
3. Após manter três execuções verdes e estáveis, planeje a desativação da V1: remova os checks
   antigos associados à V1 e, se desejado, renomeie o workflow V2 para o nome legadado apenas após a
   migração completa.

Documente cada etapa na retrospectiva da Sprint antes de desligar a V1.
