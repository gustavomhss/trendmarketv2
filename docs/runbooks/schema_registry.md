# Runbook — Schema Registry

## Objetivo
Manter `schema_drift=0` e `data_contract_break=false`.

## Diagnóstico
1. Validar alerta `SchemaDriftDetected`.
2. Rodar `python3 scripts/schema_compat_check.py schemas/mbp/quotes/v1.2.0.json`.
3. Consultar `EVI/schema_diff.txt` para detalhes de incompatibilidade.

## Mitigação
1. Bloquear deploy corrente via CI.
2. Preparar hotfix MINOR compatível ou reverter PR ofensivo.
3. Registrar waiver apenas com aprovação do Painel e tempo limitado.
4. Após correção, garantir `dbt build` com sucesso e atualizar Evidence Pack.
