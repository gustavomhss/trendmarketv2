# Sprint 6 Validation Bundle

## Purpose of the static inputs
- **`thresholds.json`** codifies the guard-rail targets for each S6 metric, including ordering, comparison semantics, units, and runbook pointers for remediation. It is treated as the contract that the scorecard job enforces on every run.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L34-L64】【F:s6_validation/thresholds.json†L1-L33】
- **`metrics_static.json`** provides the deterministic input sample that the offline scorecard pipeline consumes to render `report.json`, `report.md`, badges, and gate files. These observed values are compared against the thresholds to compute PASS/FAIL status, keeping the bundle self-contained and reproducible without external data fetches.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L34-L83】【F:s6_validation/metrics_static.json†L1-L22】

## Schema contracts and versions
- Both files must comply with their Draft-07 JSON Schemas and declare `schema_version: 1`, matching the v1 contracts referenced by the Sprint 6 specification.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L65-L123】【F:s6_validation/thresholds.json†L1-L4】【F:s6_validation/metrics_static.json†L1-L7】
- Introducing a new schema version requires an accompanying schema update under `schemas/`, validation coverage, and explicit mention in the sprint scorecard documentation per the governance policy.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L65-L123】【F:docs/scorecards/S6_SCORECARDS.md†L1-L40】

## Regenerating the bundle
1. Run `python scripts/scorecards/s6_scorecards.py` to rebuild the scorecard artifacts from the static inputs.【F:docs/scorecards/S6_SCORECARDS.md†L9-L20】
2. Validate `out/s6_scorecards/report.json` against `schemas/report.schema.json` and ensure `guard_status.txt` reports `PASS` using `scripts/watchers/s6_scorecard_guard.sh`.【F:docs/scorecards/S6_SCORECARDS.md†L9-L29】
3. Re-run the command if any input files change to keep the outputs aligned with the canonical sorted-key serialization mandated by the spec.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L34-L83】【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L124-L146】

## Governance, review, and update policy
- Sprint 6 enforces Design by Contract: any change to these inputs must maintain valid schemas and preserve the deterministic CI guard described in Sections 4 and 10 of the spec. Proposed edits ship as PRs that include regenerated artifacts and passing CI to avoid breaking the mandatory gate.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L34-L146】
- Governance for supporting automation (actions, watchers, scorecard jobs) follows the locked-by-SHA policy in Section 10 and the action rotation workflow documented in the Sprint 6 runbook. Updates to the bundle must reference the same process, including reviewers confirming SHA pins and recording rationale in `actions.lock` when workflows change.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L124-L194】【F:docs/scorecards/S6_SCORECARDS.md†L21-L48】
- Reviewers should verify that any threshold or metric adjustment includes context on the trigger for the change, proof of deterministic reruns (identical `bundle.sha256`/`report.md` under unchanged inputs), and adherence to the boss-final aggregation contract before approval.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L83-L123】【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L146-L194】

## Determinism checklist
- Encode files as UTF-8 with a trailing newline, keep JSON keys sorted, and ensure regenerated artifacts remain byte-for-byte stable apart from allowed timestamps. CI replays rely on this determinism to compute the canonical hash described in Sections 2 and 9.【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L34-L83】【F:docs/DNA/quarters/Q1/Sprint 6 (Q1).md†L124-L146】
- Never edit `out/` artifacts manually—use the regeneration steps so the pipelines stay reproducible and satisfy the deterministic bundle contract.【F:docs/scorecards/S6_SCORECARDS.md†L33-L42】
