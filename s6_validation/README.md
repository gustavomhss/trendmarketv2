# S6 Validation Bundle

This directory stores the static inputs that power the Sprint 6 scorecard gate described in the [Sprint 6 (Q1) specification](../docs/DNA/quarters/Q1/Sprint%206%20(Q1).md). Both JSON files are treated as part of the immutable validation bundle and must stay deterministic so that scorecard runs are reproducible byte-for-byte.

## Files and purpose

| File | Purpose |
| --- | --- |
| `thresholds.json` | Declares the contract for each monitored metric (identifier, ordering, comparator, target value, units and the remediation note that the on-call follows when the metric fails). These entries define the structure that downstream reports must respect when presenting scorecards. |
| `metrics_static.json` | Captures the latest approved measurements that are compared against the thresholds. Each record mirrors a thresholded metric, providing the collected value, unit, sampling window and sample size used by the deterministically generated report. |

## Schemas and versioning

- Both files conform to Draft-07 JSON Schemas committed under `schemas/thresholds.schema.json` and `schemas/metrics.schema.json`.
- Validation in CI and local runs relies on the upstream [`jsonschema`](https://pypi.org/project/jsonschema/) package pinned at `4.23.0` (see `requirements.lock`).
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

## Review expectations

- At least one reviewer from the scorecards maintainers and one from Observability must approve changes that touch this directory; reviewers verify that the edits are consistent with the governing spec and that remediation guidance remains actionable.
- Every PR must reference the relevant section of the Sprint 6 specification and explain why the metric values or thresholds changed (for example, new SLO targets or refreshed measurements).
- CI must show the `s6-scorecards` workflow (and guard watcher) passing; merges without green runs are not allowed.

## Regenerating and hashing the bundle

The scorecard script computes the bundle hash by concatenating the canonical JSON representations of `thresholds.json` and `metrics_static.json` (thresholds first) and hashing the bytes with SHA-256. Manual edits must preserve:

- UTF-8 encoding without BOM and exactly one trailing `\n`.
- Canonically sorted object keys (`sort_keys=True`) so the hash stays stable.
- Metric arrays ordered by the `order` field and in sync between both files.

If you must rebuild the bundle outside of the Makefile, export deterministic environment variables before calling the script:
```bash
PYTHONHASHSEED=0 PYTHONUTF8=1 HYPOTHESIS_PROFILE=ci HYPOTHESIS_SEED=12345 python scripts/scorecards/s6_scorecards.py
```
This reproduces the same artifacts as CI. Always refresh `out/s6_scorecards/bundle.sha256` after edits and commit the updated JSONs together so reviewers can trace the change set end to end.
