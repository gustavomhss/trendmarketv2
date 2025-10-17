# Contrato de Métricas — CRD‑8
> Fonte de verdade para nome, unidade, labels permitidas e limites de cardinalidade.

## amm_op_latency_seconds (histogram)
- **Unidade:** _seconds_
- **Labels permitidas:** `op`, `env`, `service`, `version`
- **Semântica:** tempo de operação (swap|add_liquidity|remove_liquidity|pricing|cdc_consume)
- **Buckets (iniciais):** 0.005,0.01,0.02,0.03,0.05,0.075,0.1,0.15,0.2,0.3,0.5,0.75,1,1.5,2,3,5
- **Cardinalidade alvo:** ≤ 400 séries

## data_freshness_seconds (gauge)
- **Unidade:** _seconds_
- **Labels:** `source`, `domain`, `service`, `env`
- **Semântica:** `now() - event_time`

## cdc_lag_seconds (gauge)
- **Unidade:** _seconds_
- **Labels:** `stream`, `partition`, `service`, `env`
- **Semântica:** `consumer_wallclock - origin_commit_ts`

## drift_score (gauge)
- **Labels:** `feature`, `service`, `env`
- **Semântica:** PSI (default) / KL (opcional) por janela
- **Thresholds:** warn 0.2, crit 0.4 (features críticas)

## hook_executions_total (counter)
- **Labels:** `hook_id`, `status`, `env`

## hook_coverage_ratio (gauge)
- **Labels:** `env`
- **Semântica:** executados_únicos/definidos na janela (ex.: 1h)

## synthetic_requests_total (counter)
- **Labels:** `route`, `service`, `env`
- **Semântica:** total de execuções do prober sintético por rota.

## synthetic_latency_seconds (histogram)
- **Unidade:** _seconds_
- **Labels:** `route`, `service`, `env`
- **Semântica:** latência observada pelo prober sintético por rota.
- **Buckets (iniciais):** 0.001,0.002,0.003,0.005,0.01,0.02

## synthetic_ok_ratio (gauge)
- **Labels:** `route`, `service`, `env`
- **Semântica:** proporção de respostas bem-sucedidas do prober na janela.

> O linter `scripts/prom_label_lint.py` deve retornar **LABELS_OK**; do contrário, falhar PR.
