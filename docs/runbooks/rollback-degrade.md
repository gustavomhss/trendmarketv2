# Runbook — Degrade e Rollback do DEC

## Objetivo
Executar degrade e rollback controlados quando `slo_budget_breach` ou `web_cwv_regression` são disparados, garantindo retorno ao
SLO `latency_p95 ≤ 0,8s`.

## Gatilhos
- `slo_budget_breach`: `dec.latency_p95` > 0,8s por 5 minutos.
- `web_cwv_regression`: queda de Core Web Vitals após mudança em roteamento.

## Passo a passo
1. **Avaliar contexto**
   - Revisar dashboard `MBP / DEC` (latências, cache hit, failovers).
   - Confirmar alertas em `obs/ops/watchers.yml` (owner SRE primário).
2. **Aplicar degrade**
   - Ativar `lite_mode` via `policy_engine.sh set lite_mode=true`.
   - Desabilitar features não críticas: `route_safe_only=true`, `abuse_recheck=false`.
   - Garantir que `match_core` esteja operando apenas com mercados com liquidez suficiente.
3. **Executar rollback (se degrade não estabilizar em 5 min)**
   - Utilizar pacote preparado (`ops/release/rollback_dec.sh <tag>`).
   - Validar compatibilidade de schema (`scripts/schema_compat_check.py`) antes de concluir.
   - Reiniciar serviços relacionados (`systemctl restart dec-engine` ou helm rollback).
4. **Verificação pós-rollback**
   - Confirmar `dec.latency_p95` < 0,8s por 3 janelas.
   - Rodar `bash scripts/microbench_dec.sh` (quando aplicável) para validar limites.
   - Executar `python3 scripts/verify_microbench.py` para correlacionar com thresholds históricos.
5. **Comunicação**
   - Atualizar incidente (`INC-DEC`) e registrar etapas executadas.
   - Informar produto (`PM DEC`) e Data Platform sobre impacto (ver `obs/ops/watchers.yml`).

## Evidências obrigatórias
- Log `out/s4_orr/logs/microbench.txt`.
- Bundle `out/s4_evidence_bundle_*.zip` anexado ao incidente.
- Notas de mudança armazenadas em `docs/runbooks/rollback-degrade.md` (seções de lições aprendidas).
