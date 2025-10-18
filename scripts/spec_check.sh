#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'; export LC_ALL=C; export TZ=UTC

# ── Paths base ───────────────────────────────────────────────────────────────────
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Evidence precedence: Ambiente (EVID) → CLI (--out) → Default
DEFAULT_OUT="$ROOT/out/orr_gatecheck/evidence"
OUT_DIR="${EVID:-$DEFAULT_OUT}"

POLICY_DIR="$ROOT/configs/policies"

# ── Args ────────────────────────────────────────────────────────────────────────
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out|--evidence)
      shift
      OUT_DIR="$(cd "${1:-$OUT_DIR}" && pwd)"
      shift || true
      ;;
    *)
      echo "[spec_check] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$OUT_DIR"

POLICY_HASH_FILE="$OUT_DIR/policy_hash.txt"
BUNDLE_FILE="$OUT_DIR/bundle.sha256.txt"
PROVENANCE_FILE="$OUT_DIR/provenance_onchain.json"
SIGNATURES_FILE="$OUT_DIR/signatures.json"
RESULT_FILE="$OUT_DIR/spec_check.txt"
REFMAP_FILE="$OUT_DIR/refmap.json"

# Contagem de arquivos (exclui o próprio spec_check.txt)
COUNT=$(find "$OUT_DIR" -type f ! -name "spec_check.txt" | wc -l | tr -d ' ')

REASONS=()
STATUS="PASS"

# ── Validações ─────────────────────────────────────────────────────────────────
# policy_hash
POLICY_HASH_RECORDED=""
if [[ -s "$POLICY_HASH_FILE" ]]; then
  POLICY_HASH_RECORDED="$(tr -d '\n' < "$POLICY_HASH_FILE")"
else
  REASONS+=("policy_hash.txt ausente ou vazio")
  STATUS="FAIL"
fi

# bundle.sha256
BUNDLE_SHA=""
if [[ -s "$BUNDLE_FILE" ]]; then
  BUNDLE_SHA="$(tr -d '\n' < "$BUNDLE_FILE")"
  if [[ ${#BUNDLE_SHA} -ne 64 ]]; then
    REASONS+=("bundle.sha256 inválido")
    STATUS="FAIL"
  fi
else
  REASONS+=("bundle.sha256.txt ausente ou vazio")
  STATUS="FAIL"
fi

# provenance_onchain.json
MERKLE_ROOT=""
TX_OR_WORM=""
if [[ -s "$PROVENANCE_FILE" ]]; then
  readarray -t PROVENANCE < <(python - "$PROVENANCE_FILE" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    d = json.load(fp)
print(d.get('merkle_root',''))
print(d.get('tx_hash','') or d.get('worm_path',''))
PY
)
  MERKLE_ROOT="${PROVENANCE[0]}"
  TX_OR_WORM="${PROVENANCE[1]}"
  [[ -z "$MERKLE_ROOT" ]] && REASONS+=("merkle_root ausente no provenance") && STATUS="FAIL"
  [[ -z "$TX_OR_WORM" ]] && REASONS+=("tx_hash ou worm_path ausente no provenance") && STATUS="FAIL"
else
  REASONS+=("provenance_onchain.json ausente ou vazio")
  STATUS="FAIL"
fi

# signatures.json (threshold 2-de-N e ≥2 assinaturas)
SIGNATURES_INFO=""
if [[ -s "$SIGNATURES_FILE" ]]; then
  readarray -t SIGNATURE_DETAILS < <(python - "$SIGNATURES_FILE" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    d = json.load(fp)
print(d.get('threshold'))
print(len(d.get('pubkeys', [])))
print(len(d.get('signatures', [])))
PY
)
  THRESHOLD="${SIGNATURE_DETAILS[0]:-}"
  PUB_COUNT="${SIGNATURE_DETAILS[1]:-0}"
  SIG_COUNT="${SIGNATURE_DETAILS[2]:-0}"
  SIGNATURES_INFO="threshold=${THRESHOLD};pubkeys=${PUB_COUNT};signatures=${SIG_COUNT}"
  if [[ "$THRESHOLD" != "2" ]]; then
    REASONS+=("threshold 2-de-N não encontrado")
    STATUS="FAIL"
  fi
  if (( SIG_COUNT < 2 )); then
    REASONS+=("menos de duas assinaturas registradas")
    STATUS="FAIL"
  fi
else
  REASONS+=("signatures.json ausente ou vazio")
  STATUS="FAIL"
fi

# policy_hash esperado a partir dos YAMLs (project < env < mbp_s2)
if [[ -n "$POLICY_HASH_RECORDED" ]]; then
  if [[ -r "$POLICY_DIR/project.yml" && -r "$POLICY_DIR/env.yml" && -r "$POLICY_DIR/mbp_s2.yml" ]]; then
    EXPECTED_HASH=$(cat "$POLICY_DIR/project.yml" "$POLICY_DIR/env.yml" "$POLICY_DIR/mbp_s2.yml" | sha256sum | awk '{print $1}')
    if [[ "$POLICY_HASH_RECORDED" != "$EXPECTED_HASH" ]]; then
      REASONS+=("policy_hash divergente do esperado")
      STATUS="FAIL"
    fi
  else
    REASONS+=("arquivos de política ausentes para validar o hash")
    STATUS="FAIL"
  fi
fi

# ── refmap.json (rico: variáveis do modelo + artefatos + file_count) ────────────
cat > "$REFMAP_FILE" <<JSON
{
  "metrics": ["lat_p95_ms", "err5xx_rate", "burn4h", "invariant", "inp_p75_ms", "obs_uptime"],
  "policy_hash": "$(cat "$POLICY_HASH_FILE" 2>/dev/null || echo "")",
  "evidence": ["bundle.sha256.txt", "provenance_onchain.json", "signatures.json", "env_dump.txt"],
  "file_count": $COUNT,
  "model_variables": {
    "State": "docs/spec/SPEC.md",
    "Metrics": "docs/spec/SPEC.md",
    "Policy.hash": "$OUT_DIR/policy_hash.txt",
    "Evidence.bundle_sha256": "$OUT_DIR/bundle.sha256.txt",
    "Evidence.merkle_root": "$OUT_DIR/provenance_onchain.json",
    "Evidence.signatures": "$OUT_DIR/signatures.json"
  },
  "analysis_artifacts": [
    "$OUT_DIR/analysis/burnrate_report.csv",
    "$OUT_DIR/analysis/cwv_report.csv",
    "$OUT_DIR/analysis/spans_report.csv",
    "$OUT_DIR/analysis/cardinality_budget.csv"
  ]
}
JSON

# ── spec_check.txt ──────────────────────────────────────────────────────────────
{
  echo "RESULT=${STATUS}"
  if [[ ${#REASONS[@]} -gt 0 ]]; then
    echo "REASONS=$(IFS=';'; echo "${REASONS[*]}")"
  fi
  [[ -n "$POLICY_HASH_RECORDED" ]] && echo "POLICY_HASH=${POLICY_HASH_RECORDED}"
  [[ -n "$BUNDLE_SHA" ]] && echo "BUNDLE_SHA256=${BUNDLE_SHA}"
  [[ -n "$MERKLE_ROOT" ]] && echo "MERKLE_ROOT=${MERKLE_ROOT}"
  [[ -n "$TX_OR_WORM" ]] && echo "TX_OR_WORM=${TX_OR_WORM}"
  [[ -n "$SIGNATURES_INFO" ]] && echo "SIGNATURES=${SIGNATURES_INFO}"
  echo "FILES_IN_EVIDENCE=$COUNT"
} > "$RESULT_FILE"

if [[ "$STATUS" == "FAIL" ]]; then
  echo "[spec_check] falha: ${REASONS[*]}" >&2
  exit 1
fi

echo "[spec_check] OK — evidência em ${RESULT_FILE}"
