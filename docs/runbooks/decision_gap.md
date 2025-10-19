# Runbook — Decision Gap

## Objetivo
Manter `decision_gap_ratio:5m < 0.05`.

## Diagnóstico
1. Checar alerta `DecisionGapHigh`.
2. Validar latência DEC e número de decisões perdidas.
3. Revisar fila de mensagens do engine e logs de erro.

## Mitigação
1. Aplicar escala horizontal temporária no serviço de decisões.
2. Reconciliar fila pendente e reprocessar eventos.
3. Caso persista, acionar rollback do feature flag responsável.
4. Documentar incidente e anexar métricas ao Evidence Pack.
