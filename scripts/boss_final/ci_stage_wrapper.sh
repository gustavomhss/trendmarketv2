#!/usr/bin/env bash
set -euo pipefail
STAGE="${STAGE:-}"
CLEAN_RUNNER="${CLEAN_RUNNER:-false}"
VARIANT="primary"
if [[ "${CLEAN_RUNNER,,}" == "true" ]]; then
  VARIANT="clean"
fi
ARTDIR="${ARTIFACT_DIR:-$RUNNER_TEMP/boss-stage-${STAGE}}"
mkdir -p "$ARTDIR"
LOG="$ARTDIR/guard.log"
. ./.venv/bin/activate 2>/dev/null || true
set +e
# Captura STDOUT+STDERR do guard
python -u scripts/boss_final/sprint_guard.py --stage "$STAGE" --variant "$VARIANT" 2>&1 | tee "$LOG"
CODE=${PIPESTATUS[0]}
set -e
python - "$STAGE" "$VARIANT" "$CODE" "$LOG" "$ARTDIR/report.json" <<'PY'
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

stage, variant, code_str, log_path, out_path = sys.argv[1:]
code = int(code_str)
timestamp = (
    datetime.now(timezone.utc)
    .replace(microsecond=0)
    .isoformat()
    .replace("+00:00", "Z")
)
log_excerpt = ""
try:
    lines = Path(log_path).read_text(encoding="utf-8", errors="ignore").splitlines()
    for line in reversed(lines):
        if line.strip():
            log_excerpt = line.strip()
            break
except Exception:
    pass
status = "passed" if code == 0 else "failed"
notes = "Guard stage completed com sucesso" if code == 0 else f"Guard falhou (exit {code})"
payload = {
    "generated_at": timestamp,
    "stages": [
        {
            "name": stage,
            "variant": variant,
            "clean": variant == "clean",
            "status": status,
            "exit_code": code,
            "timestamp_utc": timestamp,
            "log_excerpt": log_excerpt,
            "notes": notes,
        }
    ],
}
Path(out_path).write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
PY
STAGE_OUTPUT="out/q1_boss_final/stages/${STAGE}"
if [[ -d "$STAGE_OUTPUT" ]]; then
  rm -rf "$ARTDIR/${STAGE}"
  cp -R "$STAGE_OUTPUT" "$ARTDIR/"
fi
# Resumo no Step Summary (até 300 linhas do log)
{
  echo "### Guard — ${STAGE} (${VARIANT}) (exit=${CODE})"; echo;
  echo '```'; tail -n 300 "$LOG" || true; echo '```'
} >> "$GITHUB_STEP_SUMMARY" || true
# Propaga o exit code real (sem silenciar)
exit "$CODE"
