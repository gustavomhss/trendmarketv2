# Runbook — CDC Lag

## Objetivo
Garantir `cdc:lag_p95_seconds:5m ≤ 120`.

## Diagnóstico
1. Validar alerta `CDCLagHigh` > 10 min.
2. Conferir status dos conectores Debezium e fila Kafka.
3. Verificar partições quentes e throughput no warehouse.

## Mitigação
1. Aplicar backpressure nas ingestões não críticas.
2. Rebalancear partições e aumentar threads de leitura.
3. Se lag persistir, acionar degradação parcial do pipeline e preparar rollback.
4. Confirmar recuperação com métrica ≤ 120 s em 20 min.
