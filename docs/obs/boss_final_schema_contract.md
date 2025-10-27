# Boss Final Local Aggregate — Schema Contract

## Context

The Q1 Boss Final aggregate job now enforces the presence of a schema identifier
in every locally generated report. The pipeline previously failed during the
"Validate report schema (local)" step because the local aggregator omitted the
`schema` property.

## Contract

- Local aggregate reports **must** define `"schema": "boss_final.report@v1"`.
- `generated_at` is emitted in UTC with second precision (ISO-8601). Guard code
  injects the field if any consumer forgets it.
- Evidence bundle emitted to CI artifacts contains:
  - `out/boss_final/report.local.json`
  - `out/boss_final/report.local.json.sha256.txt`
  - `out/boss_final/diagnostics.txt`

## CI Evidence

The `Aggregate Boss Final` job uploads the files above under the
`boss-final-aggregate` artifact. The job summary surfaces:

```
report_path
schema
generated_at
sha256
```

These diagnostics are reproducible locally by running:

```bash
python scripts/boss_final/aggregate_reports_local.py
python scripts/boss_final/ensure_schema.py out/boss_final/report.local.json
```
