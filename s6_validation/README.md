# Sprint 6 Validation Fixtures

This directory stores the immutable inputs that back the Sprint 6 scorecard gate defined in the [Sprint 6 (Q1) specification](../docs/DNA/quarters/Q1/Sprint%206%20(Q1).md). The spec’s governance rules (§2, §9, §12) require these fixtures to remain deterministic, schema-valid, and reviewable so every rerun of the scorecard pipeline yields the same bundle hash and PASS/FAIL verdict.

## Fixture summary

| File | Purpose |
| --- | --- |
| `thresholds.json` | Declares the contract for each monitored metric—identifier, order, comparator, target value, unit, and remediation pointer—that the scorecard evaluates on every run. |
| `metrics_static.json` | Provides the deterministic observed values that the offline pipeline compares against the thresholds to render the scorecard outputs (`report.json`, `report.md`, badges, guard files). |

Both files must advance in lockstep so that downstream automation receives a coherent snapshot of targets and sampled measurements.

## Schema contracts and versions

- Each JSON document declares `schema_version: 1` and must validate against the Draft-07 schemas under `schemas/thresholds.schema.json` and `schemas/metrics.schema.json` respectively.
- Bumping the schema version requires a paired schema update, refreshed validation coverage, and documentation of the contract change in the Sprint 6 scorecard runbook before merge.
- Timestamps (`generated_at`, `collected_at`) must use RFC 3339 to satisfy the provenance rules in the specification.

## Regenerating the bundle

1. Format both JSON files with a canonical, sorted-keys serializer (for example, `python -m json.tool --sort-keys`) to preserve byte ordering.
2. Validate them against their schemas:
   ```bash
   python -m jsonschema --instance s6_validation/thresholds.json --schema schemas/thresholds.schema.json
   python -m jsonschema --instance s6_validation/metrics_static.json --schema schemas/metrics.schema.json
   ```
3. Rebuild the scorecard artefacts:
   ```bash
   make s6-scorecards
   scripts/watchers/s6_scorecard_guard.sh
   ```
   The `make` target calls `python scripts/scorecards/s6_scorecards.py`, regenerating `out/s6_scorecards/` (including `bundle.sha256`). The watcher asserts the guard described in the Sprint 6 spec and must pass before publishing changes.
4. Attach the refreshed artefacts from `out/s6_scorecards/` to the PR description so reviewers can compare hashes and reports.

## Review and governance policy

- Follow the Sprint 6 governance workflow: at least one scorecard maintainer and one Observability reviewer must approve changes touching this directory, confirming schema validity, regenerated artefacts, and alignment with the spec’s targets.
- Every PR must cite the relevant Sprint 6 spec clauses motivating the change (new threshold, refreshed metric sample, etc.) and include evidence of the passing guard run.
- Workflow or automation updates (for example, GitHub Actions, watchers) must keep their SHA pins in sync with `actions.lock`, per the locked-by-SHA policy referenced in the spec.

## Determinism checklist

- Encode JSON as UTF-8 without BOM, include exactly one trailing newline, and keep object keys sorted to maintain the canonical hash referenced by CI.
- Keep arrays ordered by the `order` field so `thresholds.json` and `metrics_static.json` stay aligned.
- Never hand-edit artefacts under `out/`; always regenerate them with the commands above.
- When running locally outside the Makefile, export deterministic environment variables to mirror CI:
  ```bash
  PYTHONHASHSEED=0 PYTHONUTF8=1 HYPOTHESIS_PROFILE=ci HYPOTHESIS_SEED=12345 python scripts/scorecards/s6_scorecards.py
  ```
  This reproduces the same bundle hash expected by the Sprint 6 governance checks.
