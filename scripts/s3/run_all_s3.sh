#!/usr/bin/env bash
set -euo pipefail
EVID=out/s3_gatecheck/evidence
mkdir -p "$EVID"
# policy hash
bash scripts/s3/policy_engine_s3.sh "$EVID"
# smoke test: market creator
bash tests/s3/smoke_create_market.sh || { echo "smoke_create_market FAIL" >&2; exit 1; }
# twap compute + check
python3 scripts/s3/twap_compute.py data/cdc/seeds/s3/price_stream_sample.csv "$EVID/twap.csv"
bash scripts/s3/twap_freeze_check.sh "$EVID/twap.csv" > "$EVID/twap_freeze.txt"
# abuse
python3 scripts/s3/anti_abuse.py data/cdc/seeds/s3/orders_sample.json >/dev/null
cp out/s3_gatecheck/abuse_flags.json "$EVID/abuse_flags.json"
# hooks (synthetic)
bash scripts/hooks_s3/hook_price_spike_divergence.sh data/cdc/seeds/s3/price_stream_sample.csv "$EVID/hook_price_spike.json"
bash scripts/hooks_s3/hook_liquidity_depth_gap.sh <(echo 450) "$EVID/hook_liquidity.json" || true
bash scripts/hooks_s3/hook_resolution_sla_breach.sh 25 "$EVID/hook_resolution.json"
bash scripts/hooks_s3/hook_abuse_burst.sh data/cdc/seeds/s3/orders_sample.json "$EVID/hook_abuse.json"
bash scripts/hooks_s3/hook_cdc_lag.sh 180 "$EVID/hook_cdc.json"
# spec check s3 (forte)
bash scripts/s3/spec_check_s3.sh "$EVID"
# analysis index + hashes
bash scripts/s3/analysis_index.sh "$EVID"
bash scripts/s3/hash_manifest_s3.sh "$EVID"
