# Results — MBP Sprint 2

## Visão Geral
A Sprint 2 consolida o pacote ORR fast→real com métricas determinísticas, ganchos A110 exercitados e governança criptográfica pronta para L2. Os resultados abaixo foram regenerados a partir das sementes versionadas.

---

## 1. Burn-rate
- **Reproduza com:** `bash scripts/analysis/burnrate_report.sh --out out/orr_gatecheck/evidence --seed-file data/cdc/seeds/engine/burnrate_seed.json`
- **Semente:** `data/cdc/seeds/engine/burnrate_seed.json` (SHA256 `a00f7ebfa430c396e193156a68036692905c3cb253c9f18ca3bd7b8e5db3b3f2`)
- **Evidências:**
  - `out/orr_gatecheck/evidence/analysis/burnrate_report.csv`
  - `out/orr_gatecheck/evidence/analysis/burnrate_chart.png`
  - `out/orr_gatecheck/evidence/burnrate/forecast_window.json`

## 2. CWV / INP
- **Reproduza com:** `bash scripts/analysis/cwv_report.sh --out out/orr_gatecheck/evidence --seed-file data/cdc/seeds/rum/cwv_seed.json`
- **Semente:** `data/cdc/seeds/rum/cwv_seed.json` (SHA256 `55982c89afcbd673f2a6ea390ebed7dffc6e41eff725c4d38695c4ebd1467f70`)
- **Evidências:**
  - `out/orr_gatecheck/evidence/analysis/cwv_report.csv`
  - `out/orr_gatecheck/evidence/analysis/cwv_chart.png`
  - `out/orr_gatecheck/evidence/rum/diff_report.json`
  - `out/orr_gatecheck/evidence/rum/confidence_intervals.csv`

## 3. Spans & Tracing
- **Reproduza com:** `bash scripts/analysis/spans_report.sh --out out/orr_gatecheck/evidence --seed-file data/cdc/seeds/engine/spans_seed.json`
- **Semente:** `data/cdc/seeds/engine/spans_seed.json` (SHA256 `44eda8df7df0c95a13a4c54cb2257d326731f3acafffb71290091d3bb44e4804`)
- **Evidências:**
  - `out/orr_gatecheck/evidence/analysis/spans_report.csv`
  - `out/orr_gatecheck/evidence/analysis/spans_chart.png`
  - `out/orr_gatecheck/evidence/traces/span_coverage.txt`

## 4. Cardinalidade
- **Reproduza com:** `bash scripts/analysis/cardinality_report.sh --out out/orr_gatecheck/evidence --seed-file data/cdc/seeds/load/cardinality_seed.json`
- **Semente:** `data/cdc/seeds/load/cardinality_seed.json` (SHA256 `9b7e4d4985710bc6e78366e8fe3a43d21791462622e7ee42a58edc13dbc2119c`)
- **Evidências:**
  - `out/orr_gatecheck/evidence/cardinality.txt`
  - `out/orr_gatecheck/evidence/analysis/cardinality_budget.csv`
  - `out/orr_gatecheck/evidence/analysis/cardinality_chart.png`

## 5. Política & Modelo
- **Reproduza com:** `bash scripts/policy_engine.sh --out out/orr_gatecheck/evidence --emit-policy-hash`
- **Artefatos principais:** `policy_hash.txt`, `policy_composition.json`, `policy_engine_report.json`.
- **Garantias:** `INV1..INV5` e `LF1..LF2` rastreados em `docs/spec/SPEC.md` e ecoados por `scripts/spec_check.sh`.

## 6. Proveniência e Assinaturas
- **Reproduza com:** `bash scripts/provenance/publish_root.sh --evidence out/orr_gatecheck/evidence --dry-run`
- **Assinaturas:** `bash scripts/provenance/verify_signatures.sh --evidence out/orr_gatecheck/evidence`
- **Evidências:** `provenance_onchain.json`, `signatures.json`, `bundle.sha256.txt`.

## 7. Seeds & Determinismo
Todas as sementes residem em `data/cdc/seeds/` (separadas por domínio) e são versionadas. O `scripts/analysis/run_all.sh` aceita `--seed-dir` para reusar os mesmos valores e manter o pipeline determinístico.
