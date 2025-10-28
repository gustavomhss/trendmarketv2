#!/usr/bin/env bash
set -euo pipefail
export PYTHONPATH="${PYTHONPATH:+$PYTHONPATH:}src"
STAGE="${STAGE:-}"               # s1..s6
CLEAN_RUNNER="${CLEAN_RUNNER:-false}"
ARTDIR="${ARTIFACT_DIR:-$RUNNER_TEMP/boss-stage-${STAGE}}"
ROOT_OUT_DIR="$PWD/out"
LOG_DIR="$ROOT_OUT_DIR/logs"
GUARD_DIR="$ROOT_OUT_DIR/guard"
JUNIT_DIR="$ROOT_OUT_DIR/junit"
mkdir -p "$ARTDIR" "$LOG_DIR" "$GUARD_DIR" "$JUNIT_DIR"
LOG="$LOG_DIR/guard_${STAGE}.log"
TRIAGE_LOG="$ARTDIR/triage.log"
SUMMARY_STAGE="$GUARD_DIR/summary-${STAGE}.txt"
SUMMARY_LATEST="$GUARD_DIR/summary.txt"
: >"$LOG"
rm -f "$SUMMARY_STAGE"
rm -f "$SUMMARY_LATEST"

# 1) venv autônomo + deps mínimas
if [ ! -x ".venv/bin/python" ]; then
  echo "[wrapper] Criando venv local (.venv)..." | tee -a "$LOG"
  python3 -m venv .venv
fi
. ./.venv/bin/activate
python -V | tee -a "$LOG"
python -m pip install -U pip >/dev/null
python -m pip install -q yamllint pytest hypothesis jsonschema >/dev/null
bash .github/scripts/ensure_ruff_version.sh >/dev/null
RUFF_VERSION="$(tr -d '\r\n' < .tools/ruff.version 2>/dev/null || echo 'unknown')"
echo "[wrapper] Ferramentas: ruff ${RUFF_VERSION} (pin)/yamllint/pytest/hypothesis/jsonschema" | tee -a "$LOG"

if [ "${STAGE}" = "s1" ]; then
  echo "[S1] Compile Python (py_compile)" | tee -a "$LOG"
  python - <<'PY' 2>&1 | tee -a "$LOG"
import sys
import pathlib
import py_compile

root = pathlib.Path('.').resolve()
excluded = {'.git', '.venv', 'venv', '__pycache__', '.mypy_cache', '.ruff_cache', '**pycache**'}
errors = []

for path in root.rglob('*.py'):
    if any(part in excluded for part in path.parts):
        continue
    try:
        py_compile.compile(str(path), doraise=True)
    except Exception as exc:  # pragma: no cover - diagnostic path
        errors.append((str(path), str(exc)))

if errors:
    print("[py_compile] FAIL — arquivos com erro de sintaxe:")
    for file_path, err in errors:
        print(f"  - {file_path}: {err}")
    sys.exit(1)

print("[py_compile] OK — nenhum erro de sintaxe")
PY
fi

# 2) Executa guard
set +e
python -u scripts/boss_final/sprint_guard.py --stage "$STAGE" 2>&1 | tee -a "$LOG"
CODE=${PIPESTATUS[0]}
set -e

# 3) Triagem quando o guard falha
TRIAGE_REASON=""
if [ "$CODE" -ne 0 ]; then
  echo "[wrapper] Guard exit code ${CODE} — iniciando triagem para ${STAGE}..." | tee -a "$LOG"
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

if [ ! -s "$SUMMARY_STAGE" ] && [ -s "$SUMMARY_LATEST" ]; then
  cp "$SUMMARY_LATEST" "$SUMMARY_STAGE"
fi
if [ ! -s "$SUMMARY_STAGE" ] && [ ! -s "$SUMMARY_LATEST" ]; then
  {
    echo "Stage ${STAGE^^} guard resumo indisponível."
    echo "Guard exit code: ${CODE}"
  } >"$SUMMARY_STAGE"
  cp "$SUMMARY_STAGE" "$SUMMARY_LATEST"
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

# 5) Copia artefatos padronizados
mkdir -p "$ARTDIR/out/logs" "$ARTDIR/out/guard" "$ARTDIR/out/junit"
cp "$LOG" "$ARTDIR/guard.log"
cp "$LOG" "$ARTDIR/out/logs/guard_${STAGE}.log"
if [ -s "$SUMMARY_STAGE" ]; then
  cp "$SUMMARY_STAGE" "$ARTDIR/out/guard/summary-${STAGE}.txt"
fi
if [ -s "$SUMMARY_LATEST" ]; then
  cp "$SUMMARY_LATEST" "$ARTDIR/out/guard/summary.txt"
fi
if [ -d "$ROOT_OUT_DIR/guard" ]; then
  cp -R "$ROOT_OUT_DIR/guard/." "$ARTDIR/out/guard/" 2>/dev/null || true
fi
if compgen -G "${JUNIT_DIR}"/*.xml >/dev/null; then
  cp "${JUNIT_DIR}"/*.xml "$ARTDIR/out/junit/"
fi

# 6) Resumo amigável em stdout e logs
{
  echo "=== RESUMO GUARD ${STAGE^^} ==="
  if [ -s "$SUMMARY_STAGE" ]; then
    sed -E 's/^/  /' "$SUMMARY_STAGE"
  elif [ -s "$SUMMARY_LATEST" ]; then
    sed -E 's/^/  /' "$SUMMARY_LATEST"
  else
    echo "  (sem resumo compilado; ver logs em artifacts)"
  fi
} | tee -a "$LOG"

# 7) Step Summary (diagnóstico)
{
  echo "### Guard — ${STAGE} (exit=${CODE})"; echo
  echo '```'; tail -n 300 "$LOG" || true; echo '```'
  if [ -f "$TRIAGE_LOG" ]; then
    echo; echo "#### Triage (${STAGE})"; echo; echo '```'; tail -n 200 "$TRIAGE_LOG" || true; echo '```'
  fi
} >> "$GITHUB_STEP_SUMMARY" || true

# 8) Propaga o exit code
exit "$CODE"
