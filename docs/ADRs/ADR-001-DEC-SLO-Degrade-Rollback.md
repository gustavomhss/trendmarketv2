# ADR-001 — DEC Decision Engine Hardening

- **Status:** Accepted
- **Data:** 2024-03-18
- **Contexto:** O Decision Engine (DEC) precisa entregar decisões com `p95 ≤ 0,8s` mesmo em horários de pico. A versão MVP possuía
  caches inconsistentes, ausência de controle explícito de GC e um plano de degrade/rollback pouco exercitado. Incidentes das
  sprints S2/S3 mostraram risco de saturação por burst de ordens, gerando acúmulo de filas no roteamento e degradação de SLO.
- **Forças:**
  - SLO crítico `dec.latency_p95` com orçamento mensal apertado.
  - Dependência de caches de mercado (quotes + TWAP) e rota rápida com fallback determinístico.
  - Observabilidade orientada a tracing, necessária para correlação com auditoria.

## Decisão

1. **Camadas de cache determinísticas**
   - Cache quente em memória para ordens recentes com invalidadores por mercado (`cache::market_{id}`) e TTL curto (5s) alinhado ao
     heartbeat das oracles.
   - Cache frio compartilhado (Redis cluster) apenas para replay; acesso assíncrono via `spawn_blocking` para não bloquear o loop
     de matching.
2. **Controle explícito de GC e alocação**
   - Limitar arenas de alocação (`jemalloc arenas=4`) e reutilizar buffers de decisões via `Vec::with_capacity` nos hot paths
     (`match_core`, `route_fast`).
   - Métricas `dec.gc_pause_ms` e hooks de alerta para pausas > 20ms.
3. **Degrade / rollback automático guiado por SLO**
   - Gatilho `slo_budget_breach` quando `latency_p95 > 0,8s` por 5 minutos → degrade (`lite_mode`, redução de verificações
     cruzadas e suspender audit async).
   - Persistindo por 5 minutos adicionais, executar rollback automatizado usando pacote preparado pelo release manager.
4. **Roteamento resiliente**
   - `route_fast` aplica ordenação por preço ajustado, penalidade por latência (>120ms) e confiabilidade mínima 0,9.
   - Failover para `route_safe` (modo determinístico com pré-configuração) quando `cdc_lag` ou `oracle_staleness` excedem limites.
5. **Observabilidade e guard rails**
   - Spans padronizados (`dec.match_core`, `dec.route_fast`) e logs estruturados com `decision_id`.
   - Métricas exportadas para Prometheus: `dec.latency_p95`, `dec.cache_hit_ratio`, `dec.failover_count`.

## Consequências

- Aumenta o custo operacional (gestão de caches + tuning de GC), porém garante previsibilidade e documentação para o runbook de
  rollback.
- Necessidade de treinamento da equipe SRE para operar o degrade automático e validar rollback via `docs/runbooks/rollback-
  degrade.md`.
- Observabilidade mais rica implica atualizar dashboards (`obs/ops/grafana/dec_slo.json`) e watchers (`obs/ops/watchers.yml`).
- O pipeline CI passa a exigir microbenchmarks (`match_core`, `route_fast`, `twap_update`) para detectar regressões antes do deploy.

## Rationale & Trade-offs

- Adotar GC controlado ao invés de migrar para linguagem sem GC preserva o ecossistema atual em Rust + runtime async.
- O degrade automático preferido ao manual para reduzir MTTR; risco mitigado por rollback manual documentado.
- Manter caches em duas camadas evita recalcular TWAP com latência alta, mas requer consistência via invalidadores e métricas.

## Observabilidade e Governança

- Watchers: `slo_budget_breach → degrade+rollback`, `dec_failover_spike → abrir incidente`. Ambos descritos em `obs/ops/watchers.yml`.
- Runbooks associados: `docs/runbooks/rollback-degrade.md` e `docs/runbooks/cdc-lag.md`.
- Evidências obrigatórias: microbench (`out/s4_orr/logs/microbench.txt`), bundle (`out/s4_evidence_bundle_*.zip`) e relatório de
  watchers.

## Estado Futuro

- Integrar com o schema registry de decisões para validar compatibilidade na borda.
- Expandir critérios de degrade para considerar `twap_divergence` e sinais de abuso (`abuse.detect`).
