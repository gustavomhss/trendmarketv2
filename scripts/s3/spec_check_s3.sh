#!/usr/bin/env bash
set -euo pipefail
EVID="${1:-out/s3_gatecheck/evidence}"
RESULT="$EVID/spec_check_s3.txt"
REASONS=()
status=PASS
req=(policy_hash_s3.txt twap.csv twap_freeze.txt abuse_flags.json hook_price_spike.json hook_liquidity.json hook_resolution.json hook_abuse.json hook_cdc.json)
for f in "${req[@]}"; do
  [[ -s "$EVID/$f" ]] || { REASONS+=("missing:$f"); status=FAIL; }
done
FREEZE=$(grep -Eo 'FREEZE=YES|FREEZE=NO' "$EVID/twap_freeze.txt" || true)
[[ -z "$FREEZE" ]] && { REASONS+=("twap_freeze_format"); status=FAIL; }
{
  echo "RESULT=$status"
  [[ ${#REASONS[@]} -gt 0 ]] && echo "REASONS=$(IFS=';'; echo "${REASONS[*]}")"
} > "$RESULT"
[[ "$status" == "PASS" ]] || { echo "[spec_check_s3] FAIL: ${REASONS[*]}" >&2; exit 1; }
