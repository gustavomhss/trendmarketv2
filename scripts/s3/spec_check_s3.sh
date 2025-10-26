#!/usr/bin/env bash
set -euo pipefail
EVID="${1:-out/s3_gatecheck/evidence}"
RESULT="$EVID/spec_check_s3.txt"
REASONS=()
status=PASS
req=(
  policy_hash_s3.txt
  rule_eval.json
  rule_policy_hash.txt
  twap.csv
  twap_events.json
  twap_freeze.txt
  twap_freeze.json
  abuse_flags.json
  hook_price_spike.json
  hook_liquidity.json
  hook_resolution.json
  hook_abuse.json
  hook_cdc.json
  dashboard_valid.json
  dbt/run.log
)
for f in "${req[@]}"; do
  [[ -s "$EVID/$f" ]] || { REASONS+=("missing:$f"); status=FAIL; }
done
FREEZE=$(grep -Eo 'FREEZE=YES|FREEZE=NO' "$EVID/twap_freeze.txt" || true)
[[ -z "$FREEZE" ]] && { REASONS+=("twap_freeze_format"); status=FAIL; }
[[ ! -s "$EVID/twap_freeze.json" ]] && { REASONS+=("twap_freeze_json"); status=FAIL; }

if [[ -s "$EVID/rule_eval.json" ]]; then
  if ! jq -e 'all(.[]; has("trace_id") and (.result.status != null))' "$EVID/rule_eval.json" >/dev/null; then
    REASONS+=("rule_eval_format"); status=FAIL
  fi
fi

if [[ -s "$EVID/abuse_flags.json" ]]; then
  if ! jq -e 'all(.[]; .event == "abuse_flagged" and (.trace_id|length>0))' "$EVID/abuse_flags.json" >/dev/null; then
    REASONS+=("abuse_flags_format"); status=FAIL
  fi
fi

{
  echo "RESULT=$status"
  [[ ${#REASONS[@]} -gt 0 ]] && echo "REASONS=$(IFS=';'; echo "${REASONS[*]}")"
} > "$RESULT"
[[ "$status" == "PASS" ]] || { echo "[spec_check_s3] FAIL: ${REASONS[*]}" >&2; exit 1; }
