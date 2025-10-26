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
   ```bash
   python -m jsonschema --instance s6_validation/thresholds.json --schema schemas/thresholds.schema.json
   python -m jsonschema --instance s6_validation/metrics_static.json --schema schemas/metrics.schema.json
   ```
4. Rebuild the scorecard bundle:
   ```bash
   make s6-scorecards
   scripts/watchers/s6_scorecard_guard.sh
   ```
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
