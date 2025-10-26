# Runbook — CDC Lag > 120s

## Objetivo
Manter `cdc:lag_p95_seconds:5m ≤ 120`. O gatilho de incidente é `cdc_lag` quando a métrica excede 120 segundos por 10 minutos.

## Detectar
1. Confirmar alerta `cdc_lag` no Grafana (dashboard `MBP / CDC`), verificando `cdc:lag_p95_seconds:5m` e `cdc:lag_p99_seconds`.
2. Conferir logs do conector Debezium (`obs/ops/containers/cdc/values.yaml`) procurando por `WARN Rebalance` ou `ERROR CommitFailed`.
3. Executar `python3 scripts/sim_run.sh --probe cdc_status` para capturar estado das filas Kafka e offsets.
4. Validar se há manutenção ou alterações recentes no banco primário (`ops/release/changelog.md`).

## Mitigar
1. **Aplicar degrade controlado**
   - Acionar feature flag `lite_mode` via `policy_engine.sh set lite_mode=true` para reduzir volume de resoluções.
   - Suspender ingestão não crítica (streams analíticos) usando `obs/ops/watchers.yml` (`cdc_lag → degrade+rollback`).
2. **Rebalancear CDC**
   - Aumentar threads de leitura (`replication.slot.max_streams`) e redistribuir partições quentes (`kafka-topics.sh --alter`).
   - Se houver `schema_registry_drift`, seguir runbook correspondente antes de retomar consumo.
3. **Preparar rollback**
   - Caso `lag_p95` permaneça >120s por 15 minutos após degrade, iniciar rollback para versão anterior (`docs/runbooks/rollback-degrade.md`).
   - Validar integridade dos snapshots CDC (`out/s4_orr/logs/cdc_snapshot.txt`).
4. **Verificar recuperação**
   - Monitorar `cdc:lag_p95_seconds:5m` até estabilizar <120s por 3 janelas consecutivas.
   - Registrar incidente e anexar bundle `out/s4_evidence_bundle_*.zip`.

## Comunicação
- Anunciar status no canal `#dec-incident` e abrir ticket `INC-CDC`.
- Notificar owners em `obs/ops/watchers.yml` (SRE primário + Data Platform). Inclua horário de recuperação e ações tomadas.
