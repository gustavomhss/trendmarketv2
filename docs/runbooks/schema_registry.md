# Schema Registry Drift — Runbook

## Contexto

Monitoramentos `schema_registry_drift` disparam quando a versão publicada no registry
não corresponde aos contratos aceitos pelo Sprint 4. Falhas aqui bloqueiam deploys e
impedem o gate `prega`/`make prega` de concluir com `GATECHECK_OK`.

## Detecção

- **Alertas Prometheus:** `SchemaDriftDetected` em `obs/ops/prom/rules_s4.yaml`.
- **Watchers:** `schema_registry_drift` em `obs/ops/watchers.yml` (fail-closed).
- **Evidências:** `out/s4_orr/EVI/schema_diff.txt` e `out/s4_orr/EVI/schema_compat.log`.

## Diagnóstico

1. Abrir `out/s4_orr/EVI/schema_diff.txt` para identificar campos removidos,
   tipos incompatíveis ou mudanças de obrigatoriedade.
2. Validar `data/analytics/dbt/target/manifest.json` contra os contratos em
   `data/cdc/schemas/mbp/`.
3. Conferir últimas alterações no diretório `data/cdc/schemas/` e ADRs
   relacionados (`docs/ADRs/ADR-001-DEC-SLO-Degrade-Rollback.md`,
   `docs/ADRs/ADR-002-Resolution-Engine-Regra.md`).

## Mitigação

- Se a alteração é **esperada**, abrir ADR e versionar novo schema no registry
  antes de reexecutar `make prega`.
- Se a alteração é **acidental**, revertê-la e regenerar evidências (`make prega`).
- Atualizar `data/analytics/dbt/models/sources.yml` e documentar impactos no
  README correspondente.

## Validação

1. Rodar `make prega` para regenerar evidências.
2. Confirmar que `schema_diff.txt` reporta `Sem diferenças incompatíveis`.
3. Verificar publicação dos novos artefatos no bundle (`scripts/s4_bundle.sh`).
4. Encerrar alerta quando `SchemaDriftDetected` retornar a `OK`.

## Contatos

- **Owner primário:** Data Platform — data@trendmarketv2.dev
- **Escalada:** SRE (pager `sre-primary`) caso bloqueio impacte deploy crítico.
