#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck/plan"; mkdir -p "$OUT"
EPIC_PATH="${EPIC_PATH:-docs/obs/CRD-8-epic.md}"
TASKS=$(grep -Eo 'OBS-[0-9]+' "$EPIC_PATH" | sort -u | tr '\n' ',' | sed 's/,$//')
GATES=$(grep -Eo 'T[0-9]+' "$EPIC_PATH" | sort -u | tr '\n' ',' | sed 's/,$//')
cat > "$OUT/crd_task_graph.json" <<JSON
{"epic":"$EPIC_PATH","version":"v4","tasks":[${TASKS}],"gates":[${GATES}]}
JSON
cat > "$OUT/state.json" <<JSON
{"epic":"$EPIC_PATH","version":"v4","last_phase":"T0","waves_completed":0,"completed":[],"partial":[],"missing":[]}
JSON
echo PLAN_OK
