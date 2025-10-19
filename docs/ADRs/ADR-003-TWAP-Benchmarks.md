# ADR-003 — TWAP Benchmarks e Monitoramento

- **Status:** Accepted
- **Data:** 2024-03-18
- **Contexto:** TWAP é componente crítico para decisões de preço e freeze automático. O SLO definido em S4 estabelece `TWAP
  divergence ≤ 1,0%` (janelas 5m) e a suíte de microbenchmarks deve assegurar que cálculos incrementais permaneçam abaixo de
  0,45 ms. Antes desta decisão não existia medição contínua nem integração com ORR.

## Decisão

1. **Implementação incremental do TWAP**
   - `twap_update` mantém janela deslizante de 5m com normalização por duração, permitindo ingestão contínua sem recomputar séries
     completas.
   - Estado armazenado em `TwapState` com pruning determinístico, garantindo estabilidade numérica.
2. **Benchmarks Criterion**
   - `benches/dec_benches.rs` cobre `match_core`, `route_fast` e `twap_update` com cenários representativos.
   - Limites aceitos (`match_core ≤ 1,20 ms`, `route_fast ≤ 0,70 ms`, `twap_update ≤ 0,45 ms`) validados por
     `scripts/microbench_dec.sh`.
3. **Observabilidade**
   - Métrica `engine.twap_gap` alimenta watcher `twap_divergence` (ação `freeze`).
   - Eventos `twap_recomputed` correlacionam traces (`rule.eval`, `twap.compute`).
4. **Integração com ORR**
   - `scripts/orr_s4_bundle.sh` embala microbench, dbt docs e ADRs.
   - Workflow `_s4-orr.yml` roda microbench condicionalmente (`run_microbench=true`) e coleta evidências.

## Consequências

- Necessário manter seeds realistas (`seeds/s3/price_stream_sample.csv`) para validar divergência.
- Gate opcional no CI evita falsa falha quando bench não está presente, mas falha determinística quando limites são excedidos.
- TWAP torna-se peça central nos runbooks (`docs/runbooks/cdc-lag.md`, `docs/runbooks/rollback-degrade.md`).

## Próximos Passos

- Estender benchmark com cenário de cauda (`dec_tail`) após instrumentação de traces.
- Adicionar watcher dedicado `twap_compute_regression → block_deploy` quando divergência exceder 1% por 2 janelas.
