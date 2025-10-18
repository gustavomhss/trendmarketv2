# CRD-8 Observability Release — crd-8-obs-20251018

## Resumo
- Versão: `20251018`
- Perfil ORR: `unknown`
- Ambiente: `unknown`
- Acceptance: `OK`
- Gatecheck: `OK`
- Timestamp: `2025-10-18T04:09:17Z`

## Bundle
- Caminho: `/home/runner/work/trendmarketv2/trendmarketv2/out/obs_gatecheck/bundle.zip`
- Tamanho: 20687 bytes
- SHA256: `2347fd4e19a44a1bfaec5427a271fb2bb526f2f3ce7c682fb467366d3b1c69d5`

## Evidências
| Item | Status |
| --- | --- |
| `amm_state` | ✅ |
| `baseline_perf` | ✅ |
| `chaos_summary` | ✅ |
| `costs_cardinality` | ✅ |
| `golden_traces` | ✅ |
| `metrics_summary` | ✅ |
| `metrics_unit` | ✅ |
| `pii_probe` | ✅ |
| `prometheus_text` | ✅ |
| `sbom` | ✅ |
| `synthetic_probe` | ✅ |
| `trace_log_smoke` | ✅ |

## Custos e Cardinalidade
- Custo estimado (USD/mês): 7.74
- Maior razão: 0.5833
- Métrica crítica: `synthetic_latency_seconds_bucket`

## Prober Sintético
- OK: 20 de 20
- OK ratio: 1.0

## Métricas
- p95 swap (s): 0.04925
- synthetic swap ok ratio: 1.0

## Watchers
- Simulação executada: ✅
- Alertas esperados: 9

### Alertas esperados
- `OBS_P95_Swap_TooHigh` — p95 swap > 60ms durante rampa sintética
- `OBS_Oracle_Stale` — freshness oracle > 5s por 10m
- `OBS_CDC_Lag_Warn` — stream orders com lag > 10s
- `OBS_Drift_Critical_Feature_Warn` — drift_score price_psi acima de 0.2
- `OBS_Hook_Coverage_Low` — hook_coverage_ratio abaixo de 0.95
- `OBS_Hook_Execution_Stalled` — hook_pre_trade sem execuções em 1h
- `OBS_Cardinality_Budget_Warn` — observability_series_budget_ratio > 0.7
- `OBS_Cardinality_Budget_Crit` — observability_series_budget_ratio > 0.9
- `OBS_Synthetic_OK_Ratio_Low` — synthetic_ok_ratio abaixo de 99%

## Drills
- **baseline_perf**: cpu_overhead_pct=2.6, host=x86_64, p95_ms=55
- **chaos**: chaos=docker, duration_sec=10, service=prom
- **golden_traces**: add_liquidity=True, cdc_consume=True, pricing_quote=True, swap=True
- **pii_probe**: fields=['cpf', 'email', 'msg'], pii_fields=['email', 'cpf']
- **trace_log_smoke**: correlated_ratio=1.0, observability_level=full, skipped=False, total_spans=23

## SBOM
- Caminho: `/home/runner/work/trendmarketv2/trendmarketv2/out/obs_gatecheck/evidence/sbom.cdx.json`
- SHA256: `a6e3fed551508133492e3b5af3a561ed7541ff78fc63f15aa914dd696ef8cd03`

## Artefatos
- Manifesto: `/home/runner/work/trendmarketv2/trendmarketv2/out/obs_gatecheck/release_manifest.json`
- Metadata: `/home/runner/work/trendmarketv2/trendmarketv2/out/obs_gatecheck/release_metadata.json`
