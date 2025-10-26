#!/usr/bin/env bash
set -euo pipefail
EVID=out/s3_gatecheck/evidence
mkdir -p "$EVID"

# policy hash
bash scripts/s3/policy_engine_s3.sh "$EVID"

# rule engine evaluation
python3 scripts/s3/rule_engine.py evaluate "seeds/engine/rule_seeds.json"

# smoke test: market creator
bash tests/s3/smoke_create_market.sh || { echo "smoke_create_market FAIL" >&2; exit 1; }

# twap compute + check
python3 scripts/s3/twap_compute.py data/cdc/seeds/s3/price_stream_sample.csv "$EVID/twap.csv"
bash scripts/s3/twap_freeze_check.sh "$EVID/twap.csv" > "$EVID/twap_freeze.txt"
# abuse
python3 scripts/s3/anti_abuse.py data/cdc/seeds/s3/orders_sample.json >/dev/null
python3 scripts/s3/twap_compute.py seeds/s3/price_stream_sample.csv "$EVID/twap.csv"
bash scripts/s3/twap_freeze_check.sh "$EVID/twap.csv" "$EVID/twap_events.json" > "$EVID/twap_freeze.txt"

# abuse detector
python3 scripts/s3/anti_abuse.py seeds/s3/orders_sample.json >/dev/null
cp out/s3_gatecheck/abuse_flags.json "$EVID/abuse_flags.json"

# hooks (synthetic)
bash scripts/hooks_s3/hook_price_spike_divergence.sh data/cdc/seeds/s3/price_stream_sample.csv "$EVID/hook_price_spike.json"
bash scripts/hooks_s3/hook_liquidity_depth_gap.sh <(echo 450) "$EVID/hook_liquidity.json" || true
bash scripts/hooks_s3/hook_resolution_sla_breach.sh 25 "$EVID/hook_resolution.json"
bash scripts/hooks_s3/hook_abuse_burst.sh data/cdc/seeds/s3/orders_sample.json "$EVID/hook_abuse.json"
bash scripts/hooks_s3/hook_cdc_lag.sh 180 "$EVID/hook_cdc.json"

# dashboard validation
jq '.' dashboards/grafana/mbp_s3_panel.json > "$EVID/dashboard_valid.json"

# dbt suite (best-effort)
mkdir -p "$EVID/dbt"
if command -v dbt >/dev/null 2>&1; then
  (cd analytics/dbt && dbt deps && dbt seed && dbt test) | tee "$EVID/dbt/run.log"
else
  python3 - <<'PY' >"$EVID/dbt/run.log"
import json, time
print("dbt command not available; writing stub evidence")
print(json.dumps({"timestamp": time.time(), "status": "skipped"}))
PY
fi

# spec check s3 (forte)
bash scripts/s3/spec_check_s3.sh "$EVID"

# analysis index + hashes
bash scripts/s3/analysis_index.sh "$EVID"
bash scripts/s3/hash_manifest_s3.sh "$EVID"

# bundle artifacts
(cd out/s3_gatecheck && zip -qr bundle.zip evidence)
(cd out/s3_gatecheck && sha256sum bundle.zip > bundle.sha256.txt)

echo "GATECHECK_OK"
