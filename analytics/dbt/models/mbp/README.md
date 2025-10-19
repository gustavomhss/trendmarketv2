# MBP Models — Documentation

## Visão Geral
Modelos do Market Balancing Platform (MBP) responsáveis por mercados, quotes, resoluções e eventos de abuso. Mantêm integridade referencial com validações de TWAP e cobertura de governança.

## Tabelas
- **mbp_markets:** Catálogo de mercados. Chave `market_id`. Propriedades: status, timestamps de abertura/fechamento, flags de abuso.
- **mbp_quotes:** Quotes emitidas enquanto o mercado está ativo. FK para `mbp_markets`. Regras garantem ausência de quotes em mercados fechados.
- **mbp_resolutions:** Resultado final do mercado com métricas TWAP e validação de abusos.
- **mbp_abuse_events:** Eventos sinalizados pelo engine com severidade classificada.

## Lineage
```
raw.mbp_markets -> stg.mbp_markets -> mbp_markets -> mbp_quotes / mbp_resolutions
raw.mbp_abuse_events -> stg.mbp_abuse_events -> mbp_abuse_events
```

## Owners
- Data Platform: data@trendmarketv2.dev
- MBP Engine: mbp@trendmarketv2.dev

## Tests
- `unique`, `not_null`, `relationships`, `accepted_values`, `dbt_utils.expression_is_true`.
- Regras A106/A87/A89 incorporadas via constraints de status/TWAP.

## Documentação Complementar
- Runbooks: `docs/runbooks/dec_slo.md`, `docs/runbooks/cdc_lag.md`, `docs/runbooks/schema_registry.md`.
- ADRs: `docs/adr/ADR-001-DEC-SLO-Degrade-Rollback.md`, `docs/adr/ADR-002-Resolution-Engine-Regra.md`, `docs/adr/ADR-003-TWAP-Benchmarks.md`.
