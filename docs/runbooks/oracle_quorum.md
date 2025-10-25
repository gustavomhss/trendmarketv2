# Runbook — Oracle Quorum & TWAP Degradation

## Objetivo
Garantir `quorum_ok ≥ 0.67`, `staleness_p95_ms ≤ 30000` e `diverg_pct ≤ 0.01` nas janelas de 5 minutos do MBP BR. Incident responde ao alerta `oracle_quorum_degraded` ou falha do gate RF-01/02/03.

## Detectar
1. Validar alerta no dashboard `S5 MBP Scale` – painéis "Oracle Staleness p95" e "Oracle Divergence p95" devem ficar dentro dos limites. Consultar regra Prometheus `mbp:oracle:quorum_ratio`.
2. Conferir `out/oracles/quorum_report.json` e `out/oracles/failover_events.json` anexados ao artefato `s4-orr-evidence` da execução corrente.
3. Examinar logs dos adaptadores (`logs/oracle/*.log`) procurando `FAILOVER_TRIGGERED` ou `QUOTE_STALE`.
4. Confirmar saúde das fontes primária/secundária (`ops/oracle/healthchecks.yaml`) e latência de rede.

## Mitigar
1. **Restaurar quorum**
   - Se `staleness_ms` > 30s na primária, acionar failover manual com `scripts/oracle_failover.sh --target secondary`.
   - Se divergência > 1%, reponderar fonte ofensora: `scripts/oracle_weight.py --symbol BRLUSD --source <id> --weight 0`.
2. **Reidratar TWAP**
   - Executar `SEED=42 python -m tools.sim_harness --scenario spike` para validar estabilidade pós-ajuste.
   - Reiniciar janela TWAP: `scripts/oracle_reset_window.sh --symbol BRLUSD --window 60`.
3. **Registrar evidência**
   - Atualizar `out/oracles/stability_summary.json` com notas da intervenção.
   - Abrir ticket `INC-ORACLE` e anexar gráficos/export promQL.

## Comunicação
- Avisar `#mbp-incident` com status inicial, ações tomadas e ETA de normalização.
- Escalar para Data Platform se `failover_time_s` > 60s em duas janelas consecutivas.
- Registrar post-mortem curto (<24h) com links para dashboard e audit logs.
