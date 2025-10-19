# ADR-002 — Regras do Resolution Engine

- **Status:** Accepted
- **Data:** 2024-03-04
- **Contexto:** Resoluções inconsistentes geravam disputas e impacto financeiro. Precisamos de regras determinísticas para o engine.
- **Decisão:** Formalizar regras de resolução baseadas em TWAP e eventos de abuso. Toda resolução deve validar: (a) TWAP ≤ 1% de divergência; (b) ausência de eventos `abuse` não tratados; (c) timestamp consistente com `resolved_at`.
- **Consequências:**
  - Necessidade de métricas adicionais (`engine.twap_gap`).
  - Integração com CDC para validação on-chain.
  - Documentação reforçada em runbooks e schema registry.
