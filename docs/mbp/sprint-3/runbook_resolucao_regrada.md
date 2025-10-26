# Runbook – Resolução Regrada

## Objetivo
Garantir que mercados criados via template seguem a janela de resolução e fontes de verdade aprovadas.

## Passos
1. Executar `python3 scripts/s3/create_market_from_template.py <TEMPLATE_ID> <NOME>`.
2. Validar `out/s3_gatecheck/evidence/audit_market_created_template.jsonl` para confirmar `trace_id` e `market_created_template`.
3. Conferir `out/s3_gatecheck/evidence/rule_eval.json` para garantir que o `truth_source` associado está com status `ok`.

## Rollback
- Desabilitar `feature_flags.mbp.create.by_template` em `configs/policies/mbp_s3.yml`.
- Executar `scripts/s3/run_all_s3.sh` para gerar novo bundle com flag desligada.

## Watchers
- Owner: `markets@trend`.
- Telemetria: `telemetry_market_created_template.jsonl` e `rule_policy_hash.txt`.
