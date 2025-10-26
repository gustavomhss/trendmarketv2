# Runbook — Synthetic Prober degradado

## Objetivo
Restaurar `synthetic_ok_ratio ≥ 0.99` e latência p95 ≤ 500 ms durante incidentes disparados pelo alerta `OBS_Synthetic_OK_Ratio_Low`.

> Dashboard operacional: [`dashboards/grafana/d6_synthetic_prober.json`](../../dashboards/grafana/d6_synthetic_prober.json)

## Detectar
1. Abrir o painel **D6 — Synthetic Prober** (Grafana → Observabilidade → D6). Validar:
   - Painel **Synthetic requests (5m rate)** para checar quedas abruptas de execuções.
   - Painel **Synthetic latency p75 / p95** (com links para Tempo) para identificar rotas degradadas.
   - Painel **Synthetic success ratio (5m avg)** para confirmar violação do limiar 0.99.
2. Usar o link "Trace quick links" no dashboard para abrir Tempo/Jaeger já filtrado por `service=$service` e `route=$route`.
3. Correlacionar com métricas de backend (`obs/ops/grafana/D1-Latencia.json`) caso a latência do core também esteja elevada.
4. Verificar erros recentes em `loki` (`{service="trendmarket-amm",route="$route"}`) para detectar timeouts/5xx.

## Mitigar
1. **Rotas específicas com erro**
   - Aplicar _feature flag_ de _retry_ elevado: `policy_engine.sh set synthetic.max_retries=5`.
   - Se for rota `pricing`, considerar degradar cálculo avançado (`pricing.mode=basic`).
2. **Latência generalizada**
   - Escalar horizontalmente o serviço `trendmarket-amm` (`kubectl scale deployment trendmarket-amm --replicas=+$N`).
   - Reduzir carga opcional suspendendo ganchos não críticos (`obs/ops/watchers/a110_observability.yaml` → comentar hooks `lite_mode`).
3. **Falha externa (dependências)**
   - Checar status dos provedores (CDC, oráculos). Se instáveis, acionar runbooks correspondentes antes de retomar o prober.
   - Pausar prober sintético via `scripts/sim_run.sh --probe synthetic --pause` para evitar ruído enquanto a causa raiz é tratada.
4. Validar recuperação acompanhando `synthetic_ok_ratio` ≥ 0.99 e `synthetic_latency_seconds` p95 ≤ 0.5 s por 3 janelas de 5 minutos.

## Comunicação
- Atualizar `#dec-incident` a cada 15 minutos com progresso e ETA.
- Abrir ticket `INC-SYNTHETIC` com timeline, métricas capturadas (incluir screenshot do dashboard D6) e ações executadas.
- Após resolução, anexar o bundle `out/obs_gatecheck/bundle.zip` à retroativa ORR.
