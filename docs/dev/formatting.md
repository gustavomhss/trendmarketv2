# Formatação com Ruff

Este repositório usa [`ruff`](https://docs.astral.sh/ruff/) como formatter e linter de Python com versão pinada para garantir reprodutibilidade. As instruções abaixo valem para qualquer ambiente (local ou CI) e mantêm o pipeline **Boss Final S1** saudável.

## Versão pinada

A versão única da ferramenta vive em [`.tools/ruff.version`](../../.tools/ruff.version). O script [`./.github/scripts/ensure_ruff_version.sh`](../../.github/scripts/ensure_ruff_version.sh) instala e valida exatamente essa versão na venv corrente.

```bash
# Instala/garante a versão correta
bash .github/scripts/ensure_ruff_version.sh
```

Se o arquivo `.tools/ruff.version` estiver vazio ou ausente, o script aborta com mensagem explicando a inconsistência.

## Fluxo recomendado de contribuição

1. **Sincronize dependências**
   ```bash
   python -m pip install -r requirements.lock
   bash .github/scripts/ensure_ruff_version.sh
   ```
2. **Ative os hooks de `pre-commit` (uma vez por máquina)**
   ```bash
   pre-commit install
   ```
3. **Valide tudo antes de abrir PR**
   ```bash
   # Ajusta formatação automaticamente
   ruff format .

   # Executa linters + format check (sem alterar arquivos)
   pre-commit run -a
   ```

Os hooks configurados em [`.pre-commit-config.yaml`](../../.pre-commit-config.yaml) usam o mesmo `ruff` pinado, evitando divergência entre local e CI.

## Diagnóstico do Boss Final (S1)

O guard da Sprint 1 gera artefatos em `out/guard/s1/` sempre que roda no CI ou localmente:

* `ruff_format_diff.txt` — saída completa de `ruff format --check --diff .`.
* `ruff_offenders.txt` — lista (uma por linha) dos arquivos que seriam reformatados.

Quando a verificação falha, um resumo com os primeiros trechos do diff aparece no `GITHUB_STEP_SUMMARY` do job. Os mesmos arquivos são publicados como artefatos da execução para facilitar revisão.

## Auto-fix assistido no CI

O job aceita o input `RUN_AUTO_FORMAT=true` (ao despachar manualmente o workflow **Q1 Boss Final**). Quando ativado:

1. O guard executa `ruff format .` após uma falha de `--check`.
2. Se qualquer arquivo for modificado, o estágio falha explicitamente com o código `S1-AUTO-FIX` exigindo commit das mudanças.

Isso evita que o CI aplique correções silenciosas e mantém a disciplina de versionamento.

## Troubleshooting rápido

| Sintoma | Correção |
| --- | --- |
| `ensure_ruff_version` acusa mismatch | Remova a venv (`rm -rf .venv`), recrie (`python -m venv .venv`), reative e rode o script novamente. |
| `pre-commit` reclama de versão errada | Rode `bash .github/scripts/ensure_ruff_version.sh` seguido de `pre-commit clean` e `pre-commit install`. |
| `ruff format --check --diff` mostra arquivos inesperados | Consulte `out/guard/s1/ruff_offenders.txt`, aplique `ruff format <arquivo>` ou `ruff format .` e repita o check. |

Manter estes passos garante que os pipelines S1–S6 permaneçam verdes e evita regressões de formatação.
