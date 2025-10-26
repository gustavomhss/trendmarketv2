SHELL := /usr/bin/env bash
MAKEFLAGS += --warn-undefined-variables
.DEFAULT_GOAL := prega

OUT_DIR := out/s4_orr
BUNDLE_DIR := out

.PHONY: prega env.pin orr bundle anchors flame micro dbt.docs rum.docs nb.perf clean

prega: env.pin orr dbt.docs rum.docs flame bundle anchors nb.perf
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

.PHONY: dbt-ci sim-all orr-bundle

dbt-ci:
	mkdir -p out/dbt/tmp
        pip install 'dbt-duckdb~=1.8.0'
        dbt deps --profiles-dir ~/.dbt --profile ce_profile --project-dir analytics/dbt
        dbt debug --profiles-dir ~/.dbt --profile ce_profile --project-dir analytics/dbt
        dbt run   --profiles-dir ~/.dbt --profile ce_profile --project-dir analytics/dbt
        dbt test  --profiles-dir ~/.dbt --profile ce_profile --project-dir analytics/dbt

sim-all:
	SEED=42 python -m tools.sim_harness --fixtures fixtures --scenario spike --out out/sim/spike.report.json
	SEED=42 python -m tools.sim_harness --fixtures fixtures --scenario gap   --out out/sim/gap.report.json
	SEED=42 python -m tools.sim_harness --fixtures fixtures --scenario burst --out out/sim/burst.report.json

orr-bundle:
	mkdir -p out && zip -r out/s4-orr-evidence.zip out/** target/** logs/** || true

.PHONY: s6-scorecards q1-boss-final

s6-scorecards:
	@set -euo pipefail; PYTHONHASHSEED=0 PYTHONUTF8=1 HYPOTHESIS_PROFILE=ci HYPOTHESIS_SEED=12345 python scripts/scorecards/s6_scorecards.py
        @set -euo pipefail; python -m jsonschema --instance out/s6_scorecards/report.json --schema data/cdc/schemas/report.schema.json

q1-boss-final:
	@set -euo pipefail; for variant in primary clean; do \
		for stage in s1 s2 s3 s4 s5 s6; do \
			PYTHONHASHSEED=0 PYTHONUTF8=1 HYPOTHESIS_PROFILE=ci HYPOTHESIS_SEED=12345 python scripts/boss_final/sprint_guard.py --stage $$stage --variant $$variant; \
		done; \
	done
	@set -euo pipefail; python scripts/boss_final/aggregate_q1.py
        @set -euo pipefail; python -m jsonschema --instance out/q1_boss_final/report.json --schema data/cdc/schemas/q1_boss_report.schema.json
