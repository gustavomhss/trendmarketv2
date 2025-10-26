# Sprint 6 Validation Fixtures

This directory stores the immutable inputs that back the Sprint 6 scorecard gate defined in the [Sprint 6 (Q1) specification](../docs/DNA/quarters/Q1/Sprint%206%20(Q1).md). The spec’s governance rules (§2, §9, §12) require these fixtures to remain deterministic, schema-valid, and reviewable so every rerun of the scorecard pipeline yields the same bundle hash and PASS/FAIL verdict.

## Fixture summary
# Sprint 6 Validation Inputs

The `s6_validation` bundle is the canonical source for the Sprint 6 scorecard gate. It is governed by the Sprint 6 (Q1) specification and supporting scorecard runbook; changes must follow the contracts and governance in §§2, 4, 9, and 10 of the spec and the automation workflow documented in `docs/scorecards/S6_SCORECARDS.md`.

## Fixtures and their purpose (§§2, 3, 4)

- **`thresholds.json`** – Declares the guard-rail contract for every monitored metric (identifier, comparator, target, units, remediation note). The scorecard job uses it as the DbC reference when deciding PASS/FAIL.
- **`metrics_static.json`** – Provides the deterministic measurement sample that is compared against the thresholds. Scorecard outputs (`report.json`, `report.md`, badges, guard status) are derived solely from this snapshot.

The metric list and semantics must stay aligned between the two fixtures and in the order mandated by the spec (quorum ratio, failover P95, staleness P95, CDC lag P95, divergence percentage).

## Schema contracts and versioning (§§2, 5, 7)

- Each fixture must declare `version: 1` and validate against the Draft‑07 schemas under `schemas/thresholds.schema.json` and `schemas/metrics.schema.json`.
- Raising the schema version requires adding/updating the corresponding schema file, extending the regression coverage, and updating the Sprint 6 specification and runbook so downstream automation can adopt the change in lockstep.

## Regeneration workflow (§§4, 5, 9, 10; Runbook §2)

1. Edit the JSON fixtures in a feature branch, keeping identifiers stable unless the spec introduces a new metric.
2. Format them deterministically (`python -m json.tool --sort-keys`) to preserve canonical ordering and UTF‑8 newline encoding.
3. Validate against the schemas:
| File | Purpose |
| --- | --- |
| `thresholds.json` | Declares the contract for each monitored metric—identifier, order, comparator, target value, unit, and remediation pointer—that the scorecard evaluates on every run. |
| `metrics_static.json` | Provides the deterministic observed values that the offline pipeline compares against the thresholds to render the scorecard outputs (`report.json`, `report.md`, badges, guard files). |

Both files must advance in lockstep so that downstream automation receives a coherent snapshot of targets and sampled measurements.

## Schema contracts and versions

- Each JSON document declares `schema_version: 1` and must validate against the Draft-07 schemas under `schemas/thresholds.schema.json` and `schemas/metrics.schema.json` respectively.
- Bumping the schema version requires a paired schema update, refreshed validation coverage, and documentation of the contract change in the Sprint 6 scorecard runbook before merge.
- Timestamps (`generated_at`, `collected_at`) must use RFC 3339 to satisfy the provenance rules in the specification.
- Both files conform to Draft-07 JSON Schemas committed under `schemas/thresholds.schema.json` and `schemas/metrics.schema.json`.
- Validation in CI and local runs relies on the upstream [`jsonschema`](https://pypi.org/project/jsonschema/) package pinned at `4.23.0` (see `requirements.lock`).
- The `schema_version` field in each document tracks compatibility. The current bundle is on version `1`. Any change that bumps this value requires an accompanying schema migration note in the scorecards documentation and alignment with the specification above.
- Timestamps (`generated_at`, `collected_at`) use RFC 3339 and should reflect the source extraction moment.

## Regenerating the bundle

1. Format both JSON files with a canonical, sorted-keys serializer (for example, `python -m json.tool --sort-keys`) to preserve byte ordering.
2. Validate them against their schemas:
   ```bash
   python -m jsonschema --instance s6_validation/thresholds.json --schema schemas/thresholds.schema.json
   python -m jsonschema --instance s6_validation/metrics_static.json --schema schemas/metrics.schema.json
   ```
3. Rebuild the scorecard artefacts:
4. Rebuild the scorecard bundle:
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
   This reruns `python scripts/scorecards/s6_scorecards.py`, regenerates `out/s6_scorecards/*`, and enforces the guard defined in the spec and runbook.
5. Attach the refreshed artifacts (including `bundle.sha256`) to the PR so reviewers can verify determinism.

## Review and governance policy (§§2, 4, 9, 10; Runbook §§3-4)

- Every change must ship in a PR that keeps both fixtures synchronized and includes regenerated outputs with green CI.
- Review requires at least one scorecard maintainer and one observability reviewer. Approvers verify schema compliance, rationale for metric/threshold adjustments, guard status, and SHA updates for any automation touched.
- PR descriptions must reference the relevant Sprint 6 spec sections that justify the change and link evidence from the regenerated bundle.

## Determinism requirements (§§2, 4, 9)

- Store fixtures as UTF‑8 without BOM, with exactly one trailing newline.
- Serialize objects with sorted keys (`sort_keys=True`) and keep metric arrays ordered as defined by the spec.
- Regenerated artifacts must be byte-for-byte stable apart from approved timestamps so the canonical SHA-256 hash (`bundle.sha256`) remains reproducible across reruns.
- Never hand-edit files under `out/`; rely on the regeneration workflow so CI can replay the job deterministically.
