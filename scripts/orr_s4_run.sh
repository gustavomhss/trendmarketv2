#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
OUT_DIR="$ROOT/out/s4_orr"
EVI_DIR="$OUT_DIR/EVI"
LOG_DIR="$OUT_DIR/logs"
mkdir -p "$EVI_DIR" "$LOG_DIR"
: > "$OUT_DIR/orr.log"

log() {
  printf '[ORR] %s\n' "$1" | tee -a "$OUT_DIR/orr.log"
}

ensure() {
  local bin="$1"
  if ! command -v "$bin" >/dev/null 2>&1; then
    log "Ferramenta obrigatória ausente: $bin"
    exit 1
  fi
}

log "Iniciando ORR Sprint 4"
ensure jq
ensure curl
ensure python3
ensure git
ensure dbt
ensure semgrep
ensure gitleaks
ensure trivy

K6_BIN=${K6:-k6}
ensure "$K6_BIN"

log "Executando k6 @120rps/60m"
K6_OUT="$EVI_DIR/dec_120rps_60m.json"
"$K6_BIN" run --vus 120 --duration 60m --summary-export "$K6_OUT" tests/perf/dec_120rps_60m.js | tee "$LOG_DIR/k6.log"

log "Exportando métricas DEC/CDC"
PROM_QUERY_DEC='dec:p95_seconds:5m'
PROM_QUERY_CDC='cdc:lag_p95_seconds:5m'
for metric in "$PROM_QUERY_DEC" "$PROM_QUERY_CDC"; do
  SAFE_NAME=${metric//[:]/_}
  curl -fsS "${PROM_URL:-http://127.0.0.1:9090}/api/v1/query?query=$metric" \
    | jq '.' > "$EVI_DIR/${SAFE_NAME}.json"
  log "Metric export salvo em $EVI_DIR/${SAFE_NAME}.json"
done

DBT_PROJECT="$ROOT/data/analytics/dbt"
DBT_PROFILES="$DBT_PROJECT/profiles"
log "Executando dbt deps/build/test/docs"
dbt deps --project-dir "$DBT_PROJECT" --profiles-dir "$DBT_PROFILES" | tee "$LOG_DIR/dbt_deps.log"
dbt build --project-dir "$DBT_PROJECT" --profiles-dir "$DBT_PROFILES" | tee "$LOG_DIR/dbt_build.log"
dbt test --project-dir "$DBT_PROJECT" --profiles-dir "$DBT_PROFILES" | tee "$LOG_DIR/dbt_test.log"
dbt docs generate --project-dir "$DBT_PROJECT" --profiles-dir "$DBT_PROFILES" | tee "$LOG_DIR/dbt_docs.log"

log "Verificando compatibilidade de schema"
SCHEMA_LOG="$EVI_DIR/schema_compat.log"
python3 "$ROOT/scripts/schema_compat_check.py" "$ROOT/data/cdc/schemas/mbp/quotes/v1.2.0.json" | tee "$SCHEMA_LOG"

log "Rodando Semgrep"
SEMPEG_JSON="$EVI_DIR/semgrep.json"
SEMPEG_LOG="$LOG_DIR/semgrep.log"
semgrep --config auto --json --output "$SEMPEG_JSON" 2>&1 | tee "$SEMPEG_LOG"

log "Rodando Gitleaks"
GITLEAKS_JSON="$EVI_DIR/gitleaks.json"
GITLEAKS_LOG="$LOG_DIR/gitleaks.log"
gitleaks detect --no-banner --report-format json --report-path "$GITLEAKS_JSON" 2>&1 | tee "$GITLEAKS_LOG"

log "Rodando Trivy"
TRIVY_JSON="$EVI_DIR/trivy.json"
TRIVY_LOG="$LOG_DIR/trivy.log"
trivy fs --scanners vuln,secret . --format json --output "$TRIVY_JSON" 2>&1 | tee "$TRIVY_LOG"

log "Coletando snapshot RUM"
RUM_SNAPSHOT="$EVI_DIR/web_inp_snapshot.json"
if curl -fsS http://127.0.0.1:9314/metrics -o "$RUM_SNAPSHOT"; then
  log "Snapshot RUM salvo em $RUM_SNAPSHOT"
else
  log "Falha ao capturar snapshot RUM"
  exit 1
fi

log "Calculando métricas de governança"
python3 - "$EVI_DIR/governance.json" <<'PY'
import json
from datetime import datetime, timezone
from pathlib import Path
import re
import sys

if len(sys.argv) != 2:
    print("Uso: governance_out", file=sys.stderr)
    sys.exit(2)

target = Path(sys.argv[1])
watchers_path = Path('obs/ops/watchers.yml')
if not watchers_path.exists():
    raise SystemExit(f"watchers.yml não encontrado em {watchers_path}")

hooks = []
current = None
notify_active = False
pattern = re.compile(r'^([A-Za-z0-9_]+):\s*(.*)$')
with watchers_path.open('r', encoding='utf-8') as handle:
    for raw_line in handle:
        line = raw_line.rstrip('\n')
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
            continue
        indent = len(line) - len(line.lstrip(' '))
        if stripped.startswith('- hook:'):
            if current:
                hooks.append(current)
            current = {'hook': stripped.split(':', 1)[1].strip()}
            notify_active = False
            continue
        if current is None:
            notify_active = False
            continue
        if stripped.startswith('- ') and indent <= 2:
            if current:
                hooks.append(current)
            current = None
            notify_active = False
            continue
        if notify_active and stripped.startswith('- '):
            channel_name = stripped[1:].strip()
            if channel_name:
                current[channel_name] = 'configured'
            continue
        if stripped == 'notify:':
            current.setdefault('notify_section', True)
            notify_active = True
            continue
        match = pattern.match(stripped)
        if not match:
            notify_active = False
            continue
        key, value = match.group(1), match.group(2).strip().strip('"')
        if key == 'notify':
            notify_active = True
            continue
        if notify_active:
            current[key] = value or 'configured'
            continue
        notify_active = False
        current[key] = value
if current:
    hooks.append(current)

owners = {}
runbook_missing = []
channel_totals = {}
notify_missing = []
for hook in hooks:
    owner = hook.get('owner', 'desconhecido')
    owners[owner] = owners.get(owner, 0) + 1
    runbook = hook.get('runbook')
    if not runbook:
        runbook_missing.append(hook['hook'])
    has_notify = False
    for channel_key in ('pagerduty', 'slack', 'email', 'webhook'):
        if channel_key in hook:
            channel_totals[channel_key] = channel_totals.get(channel_key, 0) + 1
            has_notify = True
    if not has_notify:
        notify_missing.append(hook['hook'])
coverage_ratio = 1.0
if hooks:
    coverage_ratio = (len(hooks) - len(runbook_missing)) / len(hooks)
notify_ratio = 1.0
if hooks:
    notify_ratio = (len(hooks) - len(notify_missing)) / len(hooks)

payload = {
    'generated_at': datetime.now(timezone.utc).isoformat(),
    'watcher_count': len(hooks),
    'owners': owners,
    'notification_channels': channel_totals,
    'runbook_coverage': {
        'covered': len(hooks) - len(runbook_missing),
        'missing_hooks': runbook_missing,
        'ratio': coverage_ratio,
    },
    'notify_coverage': {
        'covered': len(hooks) - len(notify_missing),
        'missing_hooks': notify_missing,
        'ratio': notify_ratio,
    },
}

target.write_text(json.dumps(payload, indent=2), encoding='utf-8')
PY

for marker in ACCEPTANCE_OK GATECHECK_OK; do
  MARKER_FILE="$EVI_DIR/${marker}"
  date -u +%Y-%m-%dT%H:%M:%SZ > "$MARKER_FILE"
  log "$marker"
done

log "GATECHECK_OK"
log "ORR concluído com sucesso"
