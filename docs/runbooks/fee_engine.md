# Runbook — Fee Engine Thrash or Cooldown Breach

## Objetivo
Manter `delta_fee_5m ≤ 0.20`, respeitar bounds configurados e garantir cooldown mínimo de 300s entre atualizações.

## Detectar
1. Monitorar painel "Fee Δ5m" no dashboard `S5 MBP Scale` e alerta `fee_delta_spike` baseado em `mbp:fee:delta_pct_5m`.
2. Verificar `out/fees/audit.json` e confirmar se entradas recentes respeitam `cooldown_applied=true`.
3. Consultar logs do serviço (`logs/fees/engine.log`) procurando mensagens `COOLDOWN_SKIPPED` ou `BOUND_CLAMPED`.
4. Validar profundidade de mercado em `fixtures/market_depth.json` ou fonte upstream para descartar spoofing.

## Mitigar
1. **Aplicar cooldown forçado**
   - Executar `python -m services.fees.engine --force-cooldown 600` para ampliar janela temporariamente.
   - Ajustar feature flag `fees.delta_bound` via `scripts/feature_flags.sh set fees.delta_bound=0.15` caso variações persistam.
2. **Sanear profundidade/volatilidade**
   - Rodar `SEED=42 python -m tools.sim_harness --scenario burst` e observar impacto de volumes extremos.
   - Se depth < esperado, coordenar com market makers para restaurar ordens ou ajustar `beta` temporariamente.
3. **Auditar ajustes**
   - Adicionar anotação ao audit log com `scripts/fees_append_audit.py --note "manual cooldown"`.
   - Atualizar `out/fees/audit.json` no artefato ORR e anexar resumo no ticket.

## Comunicação
- Informar `#mbp-incident` com valor atual de fee, delta observado e medidas adotadas.
- Escalar para Quant se o bound precisar ser alterado >10% do baseline ou se cooldown >900s.
- Registrar no relatório semanal de risco quaisquer overrides executados.
