# Runbook — Oráculos: Quorum / TWAP Failover

## Objetivo
Restabelecer quorum ≥ 2/3 e manter `mbp:oracle:staleness_p95_ms ≤ 30000`, `mbp:oracle:divergence_p95 ≤ 0.01` e `mbp:oracle:failover_time_p95_s < 60` em até 15 minutos após o gatilho. O alerta chega pelos hooks `oracle_staleness_guard` ou `twap_divergence` (freeze automático) e compromete o SLA de preços do MBP.

## Detectar
1. Validar o alerta no Grafana (`dashboard "S5 MBP Scale"`). Revise os painéis **"Oracle Staleness p95 (ms)"** e **"Oracle Divergence p95"** para confirmar a regressão.
2. Execute as consultas PromQL para confirmar a severidade:
   ```promql
   mbp:oracle:staleness_p95_ms{symbol="BRLUSD"}
   mbp:oracle:divergence_p95{symbol="BRLUSD"}
   mbp:oracle:quorum_ratio
   mbp:oracle:failover_time_p95_s
   ```
   Use `promtool query instant http://prometheus:9090 '…' --time=$(date -u +%s)` para arquivar o resultado.
3. Cheque logs recentes do agregador `oracle-gateway` (`kubectl logs deploy/oracle-gateway -n mbp --since=15m | rg -i 'quorum|stale|failover'`).
4. Se o freeze ocorreu por `twap_divergence`, confirme eventos `twap_recomputed` e `freeze` via `tempo`/`jaeger` filtrando por `trace.service=dec-engine` e `span.name=twap.compute`.

## Diagnóstico
1. **Saúde das fontes** — Liste batidas de heartbeat por feed (`kubectl exec statefulset/oracle-feed -- curl -s localhost:8080/healthz`). Verifique `quality_score` e `staleness`.
2. **Quorum real** — Rode `python tools/sim_harness.py --fixtures seeds/s3 --scenario spike --out out/obs_gatecheck/evidence/oracle_sim_spike.json` para comparar quorum e TWAP com amostras determinísticas.
3. **Configuração atual** — Capture toggles ativos via `bash scripts/policy_engine.sh --emit-policy-hash --out out/obs_gatecheck/evidence` e valide se `enable_twap_failover` e `enable_quorum` estão `true`.
4. **Causa raiz provável** —
   - Divergência alta persistente → fonte enviesada (verificar `services/oracles/aggregator.py`).
   - Staleness elevado → atraso na ingestão (`CDC`, upstream HTTP, fila). Cruze com runbook `docs/runbooks/cdc_lag.md` se necessário.
   - Quorum < 2/3 → feeds indisponíveis; revisar circuit-breakers (`ops/watchers/a110_observability.yaml`).

## Mitigar
1. **Failover imediato** — `policy_engine.sh set enable_twap_failover=true` (mantém TWAP de 60s servido). Verifique `mbp:oracle:failover_time_p95_s` < 60 após 2 janelas.
2. **Rebalancear quorum** — Atualize os pesos no ConfigMap `oracle-quorum` (`kubectl edit configmap/oracle-quorum -n mbp`) garantindo pelo menos duas fontes `weight ≥ 0.3`. Registre valores aplicados.
3. **Sanear feeds** —
   - Banir feed degradado: `policy_engine.sh set oracle.feed.<id>.enabled=false`.
   - Forçar refresh (`kubectl exec` feed afetado → `curl -XPOST /refresh`).
4. **Retorno gradual** — Quando `mbp:oracle:quorum_ratio ≥ 0.66` e `mbp:oracle:staleness_p95_ms ≤ 15000` por 3 janelas, reverta reweights, reabilite feeds e desative failover (`policy_engine.sh set enable_twap_failover=false`).
5. **Preventivo** — Abrir tarefa para ajustar limites (`configs/policies/mbp_s3.yml`) se o incidente demandou alteração permanente.

## Evidência ORR
- Exportar as queries PromQL acima para `out/obs_gatecheck/evidence/oracle_quorum_metrics.json` (JSON line).
- Anexar `out/obs_gatecheck/evidence/oracle_sim_spike.json` do `tools/sim_harness.py` com `quorum_ratio` pós-correção ≥ 0.66.
- Capturar screenshot do painel Grafana pós-recuperação e arquivar em `out/obs_gatecheck/evidence/oracle_dashboard.png`.
- Atualizar `out/obs_gatecheck/logs/oracle_failover.txt` com comandos executados e hashes de políticas (`policy_hash.txt`).

## Comunicação & Escalonamento
- Anunciar status inicial e atualizações no Slack `#dec-incident`; abrir incidente `INC-ORACLE` com timeline e métricas anexadas.
- PagerDuty: acionar `sre-primary`. Notificar `pm.dec@trendmarketv2.dev` quando failover for ativado > 10 min.
- Se o quorum não recuperar em 30 min ou houver segunda ocorrência em <24 h, escalar para `compliance@trendmarketv2.dev` e iniciar revisão de provedores.
