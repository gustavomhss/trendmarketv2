# Sprint 6 Validation Bundle

The fixtures in this directory are the canonical inputs for the Sprint 6 scorecard
pipeline described in the [Sprint 6 (Q1) specification](../docs/DNA/quarters/Q1/Sprint%206%20(Q1).md)
 and the [scorecard runbook](../docs/scorecards/S6_SCORECARDS.md). They are versioned
artefacts governed by the sprint’s change-control policy: every edit must keep the
contracts in lockstep, regenerate the downstream outputs, and include reviewer
approval from the scorecard and observability maintainers.

## Files and schema contracts

| File | Purpose |
| --- | --- |
| `thresholds.json` | Declares the guard-rail targets for the Sprint 6 metrics. |
| `metrics_static.json` | Provides the deterministic measurement snapshot that the scorecard evaluates. |

Both JSON documents:

- follow the Draft‑07 schemas in `schemas/thresholds.schema.json` and
  `schemas/metrics.schema.json` (flat objects with the five metric keys);
- declare immutable `schema` identifiers and `schema_version: 2` guards using
  JSON Schema `const`; and
- include `timestamp_utc` values using RFC 3339 in UTC.

## Deterministic regeneration flow

1. Update the JSON payloads while preserving the five required metric keys:
   `quorum_ratio`, `failover_time_p95_s`, `staleness_p95_s`, `cdc_lag_p95_s`, and
   `divergence_pct`.
2. Format using a canonical serializer (`sort_keys=true`, `ensure_ascii=false`,
   `separators=(",", ":")`) and ensure `thresholds.json` precede
   `metrics_static.json` quando concatenados; o script calcula
   `bundle.sha256` sobre essa ordem canônica.
3. Validate against the schemas:
   ```bash
   python -m jsonschema --instance s6_validation/thresholds.json --schema schemas/thresholds.schema.json
   python -m jsonschema --instance s6_validation/metrics_static.json --schema schemas/metrics.schema.json
   ```
4. Regenerate the scorecard artefacts via `make s6-scorecards` and commit the
   refreshed outputs under `out/s6_scorecards/`, including `bundle.sha256`.

## Review and governance

- All changes must reference the Sprint 6 specification sections motivating the
  update and include regenerated artefacts with matching bundle hashes.
- At least one scorecard maintainer and one observability reviewer must approve
  the change after verifying schema compliance, deterministic formatting, and
  guard status.
- `actions.lock` updates and workflow changes triggered by scorecard revisions
  must follow the governance rules documented in the runbook.

## Provenance and audits

The fixtures serve as the reproducible evidence for automation and manual audits.
Their history should demonstrate the rationale for every revision and link back to
spec clauses or incident reviews that required the update.
