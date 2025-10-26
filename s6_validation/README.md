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
# S6 Validation Bundle

This directory stores the static inputs that power the Sprint 6 scorecard gate described in the [Sprint 6 (Q1) specification](../docs/DNA/quarters/Q1/Sprint%206%20(Q1).md). Both JSON files are governed as immutable validation artefacts per the spec’s data-governance mandates in §2 (Escopo — itens 1 & 3) and §9 (Regras de Reprodutibilidade): they must remain deterministic, versioned and traceable so scorecard runs are reproducible byte-for-byte.

## Files and purpose

| File | Purpose |
| --- | --- |
| `thresholds.json` | Declares the contract for each monitored metric (identifier, ordering, comparator, target value, units and the remediation note that the on-call follows when the metric fails). These entries define the structure that downstream reports must respect when presenting scorecards. |
| `metrics_static.json` | Captures the latest approved measurements that are compared against the thresholds. Each record mirrors a thresholded metric, providing the collected value, unit, sampling window and sample size used by the deterministically generated report. |

## Schemas and versioning

- Both files conform to Draft-07 JSON Schemas committed under `schemas/thresholds.schema.json` and `schemas/metrics.schema.json`.
- The `schema_version` field in each document tracks compatibility. The current bundle is on version `1`. Any change that bumps this value requires an accompanying schema migration note in the scorecards documentation and alignment with the specification above.
- Timestamps (`generated_at`, `collected_at`) use RFC 3339 and should reflect the source extraction moment.

## Update workflow

1. Propose the content edits inside a dedicated branch; keep metric identifiers stable unless the spec introduces new ones.
2. Format each JSON via `python -m json.tool --sort-keys <file>` (or an equivalent formatter) so keys remain canonical, UTF-8 encoded and terminated by a single trailing newline.
3. Validate the files against their schemas:
   ```bash
   python -m jsonschema --instance s6_validation/thresholds.json --schema schemas/thresholds.schema.json
   python -m jsonschema --instance s6_validation/metrics_static.json --schema schemas/metrics.schema.json
   ```
4. Regenerate the scorecard bundle and reports deterministically:
   ```bash
   make s6-scorecards
   scripts/watchers/s6_scorecard_guard.sh
   ```
   The `make` target reruns `python scripts/scorecards/s6_scorecards.py`, which recomputes `out/s6_scorecards/bundle.sha256` using canonical serialization (`sort_keys=True`, `ensure_ascii=False`, `separators=(",", ":")`) and checks the generated `report.json` against its schema.
5. Attach the resulting `out/s6_scorecards` artifacts (including `bundle.sha256`) to the PR description for reviewer verification.

### Governance, review, and bundling

- Proposed edits follow the Sprint 6 data-governance process: bundle updates are made in lockstep across both JSONs, validated, and shipped together so that the canonical hash reflects a coherent snapshot (§2, §5, §9).
- Review mirrors the spec’s requirement that Observability and scorecard maintainers jointly gate changes; reviewers confirm the regenerated hash, schema conformance, remediation notes, and rationale linking back to the governing spec (§12, §14, §17).
- Accepted changes are merged only when the regenerated bundle, watcher guard, and CI evidence demonstrate determinism and compliance with the bundle contract; the merged state becomes the new reference snapshot for downstream scorecard jobs (§2, §9, §16).

## Review expectations

- At least one reviewer from the scorecards maintainers and one from Observability must approve changes that touch this directory; reviewers verify that the edits are consistent with the governing spec and that remediation guidance remains actionable.
- Every PR must reference the relevant section of the Sprint 6 specification and explain why the metric values or thresholds changed (for example, new SLO targets or refreshed measurements).
- CI must show the `s6-scorecards` workflow (and guard watcher) passing; merges without green runs are not allowed.

## Regenerating and hashing the bundle

The scorecard script computes the bundle hash by concatenating the canonical JSON representations of `thresholds.json` and `metrics_static.json` (thresholds first) and hashing the bytes with SHA-256. Manual edits must preserve:

- UTF-8 encoding without BOM and exactly one trailing `\n` (§2, §9).
- Canonically sorted object keys (`sort_keys=True`) so the hash stays stable (§2, §9).
- Metric arrays ordered by the `order` field and in sync between both files.

If you must rebuild the bundle outside of the Makefile, export deterministic environment variables before calling the script:
```bash
PYTHONHASHSEED=0 PYTHONUTF8=1 HYPOTHESIS_PROFILE=ci HYPOTHESIS_SEED=12345 python scripts/scorecards/s6_scorecards.py
```
This reproduces the same artifacts as CI. Always refresh `out/s6_scorecards/bundle.sha256` after edits and commit the updated JSONs together so reviewers can trace the change set end to end.
