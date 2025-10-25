# Runbook — Fee Thrash / Cooldown Breach

## Objetivo
Impedir variação de fee > 20% por 5 minutos e restaurar `mbp:fee:delta_pct_5m ≤ 0.20`, `mbp:fee:in_bounds ≥ 0.99` e `mbp:fee:cooldown_hits = 0` em até 30 minutos após o alerta `fee_cooldown_breach`. O incidente afeta a estabilidade de PnL/LPs e pode disparar halts automáticos.

## Detectar
1. Validar alerta `fee_cooldown_breach` (hook ou PD). Abra o dashboard "S5 MBP Scale" e revise os painéis **"Fee Δ5m"** e **"Fee Cooldown Hits"**.
2. Consulte as séries canônicas via PromQL (salve o resultado para evidência):
   ```promql
   mbp:fee:delta_pct_5m{env="prod"}
   mbp:fee:in_bounds{env="prod"}
   mbp:fee:cooldown_hits{env="prod"}
   ```
3. Execute `kubectl logs deploy/fee-engine -n mbp --since=10m | rg -i 'cooldown|delta_pct|clamped'` para localizar a origem.
4. Correlacione traces `fee.update` no Tempo/Jaeger para confirmar se o cooldown foi ignorado por bursts de volume.

## Diagnóstico
1. **Integridade dos parâmetros** — Capture os limites vigentes `fees.*` via `bash scripts/policy_engine.sh --emit-policy-hash --out out/obs_gatecheck/evidence` e valide `fees.cooldown_ms`, `fees.delta_bound`.
2. **Volume / Profundidade** — Gere relatório determinístico com `python tools/sim_harness.py --fixtures seeds/s3 --scenario burst --out out/obs_gatecheck/evidence/fee_sim_burst.json` para observar `quorum_ratio`, `divergence_max` e impacto em fees.
3. **Auditoria** — Verifique `out/obs_gatecheck/logs/fee_engine.log` (ou Loki `label=service:fee-engine`) para entradas `reason=cooldown_active` ausentes.
4. **Dependências** — Se `depth` estiver anômala, consulte o runbook de liquidez/market maker e confirme se não há correlato com `cdc_lag` ou `oracle`.

## Mitigar
1. **Aplicar cooldown rígido** — `policy_engine.sh set fees.cooldown_ms=600000` (10 min) e `policy_engine.sh set fees.delta_bound=0.15` temporariamente.
2. **Suavizar input** — Habilite modo de amortecimento `policy_engine.sh set fees.mode=damped` quando disponível. Enquanto isso, injete média móvel via `kubectl exec deploy/fee-engine -- env FEE_SMOOTHING=ewma_5m`.
3. **Recalibrar base** — Atualize `configs/policies/mbp_s3.yml` com novo `f0`/`bounds` se o excesso for estrutural; submeta PR emergencial.
4. **Retorno** — Quando `mbp:fee:delta_pct_5m ≤ 0.15` por 3 janelas consecutivas e `mbp:fee:cooldown_hits` zerado por 30 min, reverta ajustes (`policy_engine.sh set fees.cooldown_ms=300000`, `fees.delta_bound=0.20`).
5. **Pós-ação** — Consolidar `out/obs_gatecheck/evidence/fees_report.json` com before/after de `mbp:fee:*` (`promtool query range …`) e resumo de ajustes aplicados.

## Evidência ORR
- Exportar as queries PromQL para `out/obs_gatecheck/evidence/fee_cooldown_metrics.json`.
- Anexar `fee_sim_burst.json` com delta pós-ajuste ≤ 0.15.
- Incluir log/screenshot do painel `Fee Δ5m` após normalização em `out/obs_gatecheck/evidence/fee_dashboard.png`.
- Atualizar `out/obs_gatecheck/logs/fee_runbook.txt` com timestamps, toggles e hash de política.

## Comunicação & Escalonamento
- Comunicar status inicial no Slack `#dec-incident`; incluir `#finance-ops` se impacto > 15 min.
- PagerDuty: acionar `pm-dec` se for preciso alterar parâmetros permanentes.
- Se `mbp:fee:in_bounds < 0.95` por 1h ou houver três incidentes em 7 dias, abrir ação corretiva com `risk@trendmarketv2.dev` e registrar CAPA.
