# TrendMarketV2 — Observabilidade (CRD‑8)

## Como rodar no GitHub Actions
1. **Plan:** Actions → **CRD Epic — Plan** (ou comente `/crd plan docs/obs/CRD-8-epic.md`).
2. **Exec (fast):** Actions → **CRD Epic — Exec** → profile `fast` (smoke) → baixe o artefato `obs-bundle-*`.
3. **Exec (full):** profile `full` (SBOM, audit, testes) → verifique `ACCEPTANCE_OK` e `GATECHECK_OK` e `summary.json`.

## Estrutura útil
- `docs/obs/CRD-8-epic.md` — especificação (fonte textual)
- `ops/` — configs (Collector, Watchers, Dashboards)
- `scripts/` — ORR T1→T12 e utilitários
- `out/obs_gatecheck/` — **saída do CI** (não comitar)

## Após merge
- Proteja `main` exigindo checks Plan & Exec (full).
- Tag: `crd-8-obs-YYYYMMDD` após ORR full GREEN.
