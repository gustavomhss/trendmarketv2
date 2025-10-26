# Runbook – Anti-Abuso

## Objetivo
Monitorar bursts de ordens, violações de exposição e cooldowns no MBP S3.

## Passos
1. Executar `python3 scripts/s3/anti_abuse.py <ORDERS_JSON>`.
2. Verificar `out/s3_gatecheck/evidence/abuse_flags.json` para eventos com `reason` `burst`, `exposure` ou `cooldown_violation`.
3. Confirmar ações moderadas no `telemetry_anti_abuse.jsonl` com `trace_id` correlacionado.

## Rollback
- Ajustar limites em `configs/policies/mbp_s3.yml` > `risk_caps`.
- Reprocessar ordens e publicar novo bundle via `scripts/s3/run_all_s3.sh`.

## Watchers
- Owner: `trust@trend`.
- Telemetria: `telemetry_anti_abuse.jsonl` e `hook_abuse_burst.sh`.
