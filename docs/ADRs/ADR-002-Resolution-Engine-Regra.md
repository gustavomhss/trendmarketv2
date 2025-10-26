# ADR-002 — Resolution Engine Regrado

- **Status:** Accepted
- **Data:** 2024-03-18
- **Contexto:** O pipeline de resolução precisava atender contratos A106/A87/A89, garantindo consistência entre mercado,
  auditoria e CDC. Ausência de validações determinísticas gerava disputas e risco de regressão quando novos mercados eram
  habilitados. O ORR S4 exige evidências de qualidade externa (dbt tests/docs) e integração com Schema Registry.

## Decisão

1. **Contratos formais**
   - Especificar schemas versionados para `mbp_resolutions` e `mbp_abuse_events` no registry, com regras de compatibilidade
     `BACKWARD`.
  - `dbt` passa a ser autoridade externa para validar qualidade dos datasets (`data/analytics/dbt/models/sources.yml`).
2. **Engine regrado**
   - Fluxo de resolução executa `rule.eval` determinística (TWAP, quorum, abuso) antes de emitir decisão.
   - Toda decisão inclui `resolution_proof` e `audit_trace_id`, permitindo reconciliação posterior.
3. **Guard rails no CI**
   - `dbt build` roda quando secrets GCP estão presentes; falha impede merge (`dbt_test_failure → block_merge`).
   - Hook `schema_registry_drift` bloqueia deploy quando schema diverge do contrato aceito.
4. **Observabilidade acoplada a CDC**
   - Métrica `resolution.consistency_ok` acompanha percentuais de decisões aprovadas.
  - Runbook `docs/runbooks/schema_registry.md` documenta processo de correção.

## Consequências

- Necessário manter `data/analytics/dbt` atualizado com documentação (`dbt docs generate`) e publicar artifacts.
- Adoção de `profiles.yml` com `env_var` protege secrets de BigQuery.
- Incorpora watchers específicos: `dbt_test_failure → block_merge`, `schema_registry_drift → block_deploy`, owners compartilhados
  entre Data e SRE.
- Exige alinhamento com times de dados para garantir que amostras CDC estejam sincronizadas com orquestração.

## Considerações Operacionais

- Falhas em `dbt build` devem gerar incidente `Data Quality` e acionar rota `data-eng`.
- Revisões de schema demandam ADR e atualização do registry antes do rollout.
- Evidências `dbt-docs` e `pip-audit` passam a compor o bundle S4 (`scripts/orr_s4_bundle.sh`).

## Futuro

- Incluir testes de reconciliação cruzados com trilhas on-chain.
- Automatizar publicação de manifestos do Schema Registry após cada merge.
