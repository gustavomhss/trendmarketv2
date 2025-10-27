#!/usr/bin/env bash
set -euo pipefail
STAGE="${STAGE:-}"
CLEAN_RUNNER="${CLEAN_RUNNER:-false}"
ARTDIR="${ARTIFACT_DIR:-$RUNNER_TEMP/boss-stage-${STAGE}}"
mkdir -p "$ARTDIR"
LOG="$ARTDIR/guard.log"
. ./.venv/bin/activate 2>/dev/null || true
set +e
python scripts/boss_final/sprint_guard.py --stage "$STAGE" | tee "$LOG"
CODE=${PIPESTATUS[0]}
set -e
python - "$STAGE" "$CLEAN_RUNNER" "$CODE" "$ARTDIR/report.json" <<'PY'
import json,sys
stage,clean,code,out=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
rep={"stages":[{"name":stage,"clean":(clean=="true"),"status":"passed" if code==0 else "failed","exit_code":code}]}
open(out,'w',encoding='utf-8').write(json.dumps(rep,ensure_ascii=False))
PY
exit "$CODE"
