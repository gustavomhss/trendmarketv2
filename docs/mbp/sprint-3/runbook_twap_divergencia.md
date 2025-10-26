# Runbook – TWAP Divergência

## Objetivo
Detectar divergências persistentes de preço usando TWAP e intervalos de confiança de 99%.

## Passos
1. Rodar `python3 scripts/s3/twap_compute.py <CSV_PRECOS> out/s3_gatecheck/evidence/twap.csv`.
2. Executar `bash scripts/s3/twap_freeze_check.sh out/s3_gatecheck/evidence/twap.csv out/s3_gatecheck/evidence/twap_events.json`.
3. Revisar `out/s3_gatecheck/evidence/twap_freeze.json` para motivo (`divergence` ou `ic99`).

## Rollback
- Ajustar parâmetros de divergência em `configs/policies/mbp_s3.yml`.
- Reexecutar `scripts/s3/run_all_s3.sh` e publicar novo `bundle.zip`.

## Watchers
- Owner: `riskops@trend`.
- Telemetria: `telemetry_twap_compute.jsonl` e `twap_events.json`.
