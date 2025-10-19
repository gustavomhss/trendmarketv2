SHELL := /usr/bin/env bash
MAKEFLAGS += --warn-undefined-variables
.DEFAULT_GOAL := prega

OUT_DIR := out/s4_orr
BUNDLE_DIR := out

.PHONY: prega env.pin orr bundle anchors flame micro dbt.docs rum.docs nb.perf clean

prega: env.pin orr bundle anchors nb.perf
@echo "[prega] pipeline concluída"

env.pin:
@set -euo pipefail; ./scripts/env_pin_check.sh

orr:
@set -euo pipefail; ./scripts/orr_s4_run.sh

bundle:
@set -euo pipefail; ./scripts/s4_bundle.sh

anchors:
@set -euo pipefail; ./scripts/anchor_integrity.sh

flame:
@set -euo pipefail; ./scripts/flamegraph_hotpaths.sh

micro:
@set -euo pipefail; ./scripts/microbench_dec.sh

dbt.docs:
@set -euo pipefail; dbt docs generate --project-dir analytics/dbt --profiles-dir analytics/dbt/profiles

rum.docs:
@set -euo pipefail; node fe/rum/collector_publish.js

nb.perf:
@set -euo pipefail; python3 scripts/nb_perf_export.py

clean:
rm -rf $(OUT_DIR) out/s4_evidence_bundle_*.zip out/s4_evidence_bundle_*.zip.sha256 || true
