# Demo S4 — Pre-GA em 7 passos

1. **One-command:** Executar `make prega` e observar resumo: SLOs, SHA-256, ANCHOR_ROOT e tag Git.
2. **Performance:** Mostrar gráfico `dec:p95_seconds:5m` ≤ 0.8s @ 120 rps com 5xx=0.
3. **CDC:** Verificar `cdc:lag_p95_seconds:5m` ≤ 120s e runbook acionável.
4. **Governança de Dados:** Evidenciar `schema_drift=0`, `data_contract_break=false`, diff salvo em `EVI/schema_diff.txt`.
5. **dbt:** `dbt build` verde e docs (`catalog.json`, `manifest.json`, `index.html`) publicados como artifact.
6. **RUM:** Métrica `web_vitals_inp_ms{page,env}` ≤ 200ms com snapshot `EVI/web_inp_snapshot.json`.
7. **Âncora:** Mostrar `out/s4_orr/ANCHOR.json` + tag `anchor-M2-<root>` e bundle zipado.

## 60s para ler o `make prega`

1. **Linha 1:** Estado dos SLOs principais (DEC p95, CDC p95, INP p75) marcados como OK/within.
2. **Linha 2:** `BUNDLE_SHA256` e `ANCHOR_ROOT` prontos para copiar no PR/Release.
3. **Linha 3:** Contagem de evidências e principais diretórios (`EVI/...`, `docs/adr/...`, `ops/prom/...`).
