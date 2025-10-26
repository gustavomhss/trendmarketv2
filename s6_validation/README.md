# Sprint 6 validation bundle

Os arquivos deste diretório sustentam a geração determinística dos scorecards da Sprint 6.

- `thresholds.json` define os limites oficiais (versão 1) para as cinco métricas mandatórias: `quorum_ratio`, `failover_time_p95_s`, `staleness_p95_s`, `cdc_lag_p95_s` e `divergence_pct`. Os valores são mantidos como strings decimais para preservar precisão.
- `metrics_static.json` fornece uma captura de referência com as mesmas métricas observadas, usada em testes determinísticos e validações locais.

## Governança

1. Toda alteração deve manter `version: 1` até que um novo conjunto de limites seja aprovado formalmente.
2. As chaves das métricas são fixas; alterações exigem revisão do schema correspondente em `schemas/` e aprovação de governança.
3. Os arquivos devem permanecer em UTF-8 com newline final e chaves ordenadas conforme `json.dumps(..., sort_keys=True)` para garantir hashing determinístico.
4. Atualizações requerem PR com evidências de validação (`scripts/scorecards/s6_scorecards.py`) e referência ao runbook em `docs/scorecards/S6_SCORECARDS.md`.

## Regeneração

Para gerar um novo bundle determinístico:

```bash
python scripts/scorecards/s6_scorecards.py
```

O comando valida `thresholds.json` e `metrics_static.json`, produz `out/s6_scorecards/report.json` e atualiza `bundle.sha256`. Execute `pytest tests/scorecards` para garantir cobertura de regressão.
