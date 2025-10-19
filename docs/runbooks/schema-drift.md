# Runbook — Schema Drift

## Objetivo
Responder ao watcher `schema_registry_drift` e restaurar compatibilidade entre produtores DEC e consumidores downstream.

## Detectar
1. Alerta `schema_registry_drift` no Slack (`#dec-incident`) indicando evento bloqueado no CI.
2. Conferir diff em `out/s4_orr/logs/schema_diff.txt` ou output do job `schema_compat_check.py`.
3. Validar versão atual do schema no registry (`schemas/mbp/*`) e comparar com o manifesto (`analytics/dbt/target/manifest.json`).
4. Revisar PR ou deploy recente que alterou campos (`ops/release/changelog.md`).

## Mitigar
1. **Bloquear implantação**
   - Pausar pipeline (`gh workflow run cancel <workflow_id>`) conforme `ops/watchers.yml` (`schema_registry_drift → block_deploy`).
2. **Corrigir schema**
   - Ajustar schema para respeitar regra `BACKWARD` (adicionar campos opcionais ou bump de versão compatível).
   - Atualizar contratos em `schemas/mbp/` e executar `python3 scripts/schema_compat_check.py <schema>`.
3. **Validar dados existentes**
   - Rodar `dbt build` (com secrets válidos) para garantir que dados históricos permanecem consistentes.
   - Conferir se TWAP/Tick pipelines consomem novos campos sem erro.
4. **Retomar deploy**
   - Após aprovação, gerar novo bundle (`bash scripts/orr_s4_bundle.sh`) e anexar ao incidente.
   - Atualizar watchers com resumo da correção.

## Comunicação
- Responsável primário: Data Platform.
- Stakeholders: PM DEC, SRE, Compliance (caso drift afete contratos A106/A87/A89).
- Registrar incidente `INC-SCHEMA` com ações, commits e evidências.

## Checklist pós-incidente
- `dbt build` verde.
- `schema_registry_drift` limpo por 24h.
- Bundle atualizado disponível em `out/s4_evidence_bundle_*.zip`.
