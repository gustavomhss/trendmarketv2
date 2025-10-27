#!/usr/bin/env bash
set -euo pipefail
STAGE="${STAGE:-}"               # s1..s6
CLEAN_RUNNER="${CLEAN_RUNNER:-false}"
ARTDIR="${ARTIFACT_DIR:-$RUNNER_TEMP/boss-stage-${STAGE}}"
mkdir -p "$ARTDIR"
LOG="$ARTDIR/guard.log"
TRIAGE_LOG="$ARTDIR/triage.log"

# 1) venv autônomo + deps mínimas
if [ ! -x ".venv/bin/python" ]; then
  echo "[wrapper] Criando venv local (.venv)..." | tee -a "$LOG"
  python3 -m venv .venv
fi
. ./.venv/bin/activate
python -V | tee -a "$LOG"
python -m pip install -U pip >/dev/null
python -m pip install -q ruff yamllint pytest hypothesis jsonschema >/dev/null
echo "[wrapper] Ferramentas: ruff/yamllint/pytest/hypothesis/jsonschema" | tee -a "$LOG"

# 2) Executa guard
set +e
GUARD_OUT=$(python -u scripts/boss_final/sprint_guard.py --stage "$STAGE" 2>&1)
CODE=$?
set -e
if [ -n "$GUARD_OUT" ]; then echo "$GUARD_OUT" | tee -a "$LOG"; fi

# 3) Triagem quando o guard falha e não imprime nada
TRIAGE_REASON=""
if [ "$CODE" -ne 0 ] && [ -z "$GUARD_OUT" ]; then
  echo "[wrapper] Guard falhou sem output — iniciando triagem para ${STAGE}..." | tee -a "$LOG"
  case "$STAGE" in
    s1)
      # Lint geral
      (ruff --version && ruff check . -v) >"$TRIAGE_LOG" 2>&1 || true
      TRIAGE_REASON="ruff_failed_or_issues_found" ;;
    s2)
      # Testes unitários
      (pytest -q || pytest -q -k unit) >"$TRIAGE_LOG" 2>&1 || true
      TRIAGE_REASON="pytest_unit_failed_or_error" ;;
    s3)
      # Smoke/integration
      (pytest -q -k smoke || pytest -q) >"$TRIAGE_LOG" 2>&1 || true
      TRIAGE_REASON="pytest_smoke_failed_or_error" ;;
    s4)
      # YAML lint em configs/ops
      (yamllint -s configs ops) >"$TRIAGE_LOG" 2>&1 || true
      TRIAGE_REASON="yamllint_failed_or_yaml_invalid" ;;
    *)
      # fallback
      echo "[triage] Sem rotina específica para ${STAGE}" >"$TRIAGE_LOG" ;;
  esac
  # anexa resumo da triagem no log principal
  { echo "\n[triage] resumo:"; tail -n 200 "$TRIAGE_LOG" 2>/dev/null || true; } >> "$LOG"
fi

# 4) report.json enriquecido
python - "$STAGE" "$CLEAN_RUNNER" "$CODE" "$ARTDIR/report.json" "$TRIAGE_REASON" <<'PY'
import json,sys,os
stage,clean,code,out,reason=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4],sys.argv[5]
rep={"stages":[{"name":stage,"clean":(clean=="true"),"status":"passed" if code==0 else "failed","exit_code":code}]}
if code!=0:
    rep["failure_reason"]=reason or "guard_failed_no_output"
    p=os.path.join(os.path.dirname(out),'triage.log')
    if os.path.exists(p):
        try:
            with open(p,'r',encoding='utf-8',errors='ignore') as h:
                rep["triage_tail"]=h.read()[-5000:]  # último bloco
        except Exception:
            pass
open(out,'w',encoding='utf-8').write(json.dumps(rep,ensure_ascii=False))
PY

# 5) Step Summary (diagnóstico)
{
  echo "### Guard — ${STAGE} (exit=${CODE})"; echo
  echo '```'; tail -n 300 "$LOG" || true; echo '```'
  if [ -f "$TRIAGE_LOG" ]; then
    echo; echo "#### Triage (${STAGE})"; echo; echo '```'; tail -n 200 "$TRIAGE_LOG" || true; echo '```'
  fi
} >> "$GITHUB_STEP_SUMMARY" || true

# 6) Propaga o exit code
exit "$CODE"
