#!/usr/bin/env bash
set -euo pipefail

OUT="out/obs_gatecheck"
EVI="$OUT/evidence"
LOG="$OUT/logs"
mkdir -p "$OUT"

ACCEPTANCE="FAIL"
GATECHECK="FAIL"

# Lê as linhas finais do orr_all.txt
if [ -f "$LOG/orr_all.txt" ]; then
  grep -q 'ACCEPTANCE_OK' "$LOG/orr_all.txt" && ACCEPTANCE="OK" || true
  grep -q 'GATECHECK_OK' "$LOG/orr_all.txt" && GATECHECK="OK" || true
fi

EVI_COUNT=$(find "$EVI" -type f 2>/dev/null | wc -l | tr -d ' ')
TS=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

PROFILE="${PROFILE:-unknown}"
ENVIRONMENT="${ENVIRONMENT:-unknown}"
EPIC_PATH="${EPIC_PATH:-docs/obs/CRD-8-epic.md}"

CARDINALITY_PATH="$EVI/costs_cardinality.json"
CARD_COST=""
CARD_RATIO=""
CARD_METRIC=""
if [ -f "$CARDINALITY_PATH" ]; then
  eval "$(CARDINALITY_PATH="$CARDINALITY_PATH" python3 - <<'PY'
import json, os
path = os.environ["CARDINALITY_PATH"]
data = json.loads(open(path, "r", encoding="utf-8").read())
def emit(key, value):
    if value in (None, ""):
        return ""
    if isinstance(value, str):
        safe = value.replace("'", "\'")
        return f"{key}='{safe}'"
    return f"{key}={value}"
fields = [
    emit("CARD_COST", data.get("total_estimated_usd_month")),
    emit("CARD_RATIO", data.get("max_ratio")),
    emit("CARD_METRIC", data.get("max_ratio_metric")),
]
print(";".join(filter(None, fields)))
PY
)"
fi

if [ -z "$CARD_COST" ]; then CARD_COST=null; fi
if [ -z "$CARD_RATIO" ]; then CARD_RATIO=null; fi
if [ -n "$CARD_METRIC" ]; then
  CARD_METRIC_JSON="\"$CARD_METRIC\""
else
  CARD_METRIC_JSON=null
fi

cat > "$OUT/summary.json" <<JSON
{ "ts": "$TS",
  "profile": "$PROFILE",
  "environment": "$ENVIRONMENT",
  "epic_path": "$EPIC_PATH",
  "acceptance": "$ACCEPTANCE",
  "gatecheck": "$GATECHECK",
  "evidence_files": $EVI_COUNT,
  "cardinality_cost_est_usd": $CARD_COST,
  "cardinality_max_ratio": $CARD_RATIO,
  "cardinality_max_metric": $CARD_METRIC_JSON }
JSON

echo SUMMARY_OK
