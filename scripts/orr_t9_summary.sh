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

cat > "$OUT/summary.json" <<JSON
{ "ts": "$TS",
  "profile": "$PROFILE",
  "environment": "$ENVIRONMENT",
  "epic_path": "$EPIC_PATH",
  "acceptance": "$ACCEPTANCE",
  "gatecheck": "$GATECHECK",
  "evidence_files": $EVI_COUNT }
JSON

echo SUMMARY_OK
