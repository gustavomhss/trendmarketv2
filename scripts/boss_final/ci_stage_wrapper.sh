#!/usr/bin/env bash
set -euo pipefail
STAGE="${STAGE:-}"               # esperado "s1".."s6"; se vazio, o guard deve falhar com mensagem clara
CLEAN_RUNNER="${CLEAN_RUNNER:-false}"
ARTDIR="${ARTIFACT_DIR:-$RUNNER_TEMP/boss-stage-${STAGE}}"
mkdir -p "$ARTDIR"
LOG="$ARTDIR/guard.log"

# 1) venv autônomo
if [ ! -x ".venv/bin/python" ]; then
  echo "[wrapper] Criando venv local (.venv)..." | tee -a "$LOG"
  python3 -m venv .venv
fi
. ./.venv/bin/activate
python -V | tee -a "$LOG"

# 2) deps mínimas (isoladas do projeto)
python -m pip install -U pip >/dev/null
python -m pip install -q ruff yamllint pytest hypothesis jsonschema >/dev/null
echo "[wrapper] Ferramentas: ruff/yamllint/pytest/hypothesis/jsonschema" | tee -a "$LOG"

# 3) executa guard com captura total
set +e
python -u scripts/boss_final/sprint_guard.py --stage "$STAGE" 2>&1 | tee -a "$LOG"
CODE=${PIPESTATUS[0]}
set -e

# 4) sintetiza report.json do stage
python - "$STAGE" "$CLEAN_RUNNER" "$CODE" "$ARTDIR/report.json" <<'PY'
import json,sys
stage,clean,code,out=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]
rep={"stages":[{"name":stage,"clean":(clean=="true"),"status":"passed" if code==0 else "failed","exit_code":code}]}
open(out,'w',encoding='utf-8').write(json.dumps(rep,ensure_ascii=False))
PY

# 5) Step Summary (diagnóstico)
{
  echo "### Guard — ${STAGE} (exit=${CODE})"; echo
  echo '```'; tail -n 300 "$LOG" || true; echo '```'
} >> "$GITHUB_STEP_SUMMARY" || true

exit "$CODE"
