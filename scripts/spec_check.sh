#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$SCRIPT_DIR/.."
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
POLICY_DIR="$ROOT/configs/policies"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      OUT_DIR="$(cd "$2" && pwd)"
      shift 2
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

REASONS=()
STATUS="PASS"

if [[ ! -f "$POLICY_HASH_FILE" ]]; then
  REASONS+=("policy_hash.txt ausente")
  STATUS="FAIL"
fi

if [[ ! -f "$BUNDLE_FILE" ]]; then
  REASONS+=("bundle.sha256.txt ausente")
  STATUS="FAIL"
fi

if [[ ! -f "$PROVENANCE_FILE" ]]; then
  REASONS+=("provenance_onchain.json ausente")
  STATUS="FAIL"
fi

if [[ ! -f "$SIGNATURES_FILE" ]]; then
  REASONS+=("signatures.json ausente")
  STATUS="FAIL"
fi

POLICY_HASH_RECORDED=""
if [[ -f "$POLICY_HASH_FILE" ]]; then
  POLICY_HASH_RECORDED="$(tr -d '\n' < "$POLICY_HASH_FILE")"
  EXPECTED_HASH=$(cat "$POLICY_DIR/project.yml" "$POLICY_DIR/env.yml" "$POLICY_DIR/mbp_s2.yml" | sha256sum | awk '{print $1}')
  if [[ "$POLICY_HASH_RECORDED" != "$EXPECTED_HASH" ]]; then
    REASONS+=("policy_hash divergente do esperado")
    STATUS="FAIL"
  fi
fi

BUNDLE_SHA=""
if [[ -f "$BUNDLE_FILE" ]]; then
  BUNDLE_SHA="$(tr -d '\n' < "$BUNDLE_FILE")"
  if [[ ${#BUNDLE_SHA} -ne 64 ]]; then
    REASONS+=("bundle.sha256 inválido")
    STATUS="FAIL"
  fi
fi

MERKLE_ROOT=""
TX_HASH=""
if [[ -f "$PROVENANCE_FILE" ]]; then
  readarray -t PROVENANCE < <(python - "$PROVENANCE_FILE" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    data = json.load(fp)
print(data.get('merkle_root', ''))
print(data.get('tx_hash', '') or data.get('worm_path', ''))
PY
)
  MERKLE_ROOT="${PROVENANCE[0]}"
  TX_HASH="${PROVENANCE[1]}"
  if [[ -z "$MERKLE_ROOT" ]]; then
    REASONS+=("merkle_root ausente no provenance")
    STATUS="FAIL"
  fi
  if [[ -z "$TX_HASH" ]]; then
    REASONS+=("tx_hash ou worm_path ausente no provenance")
    STATUS="FAIL"
  fi
fi

SIGNATURES_INFO=""
if [[ -f "$SIGNATURES_FILE" ]]; then
  readarray -t SIGNATURE_DETAILS < <(python - "$SIGNATURES_FILE" <<'PY'
import json, sys
with open(sys.argv[1], 'r', encoding='utf-8') as fp:
    data = json.load(fp)
print(data.get('threshold'))
print(len(data.get('pubkeys', [])))
print(len(data.get('signatures', [])))
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
fi

cat > "$REFMAP_FILE" <<JSON
{
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

{
  echo "RESULT=${STATUS}"
  if [[ ${#REASONS[@]} -gt 0 ]]; then
    echo "REASONS=$(IFS=';'; echo "${REASONS[*]}")"
  fi
  [[ -n "$POLICY_HASH_RECORDED" ]] && echo "POLICY_HASH=${POLICY_HASH_RECORDED}"
  [[ -n "$BUNDLE_SHA" ]] && echo "BUNDLE_SHA256=${BUNDLE_SHA}"
  [[ -n "$MERKLE_ROOT" ]] && echo "MERKLE_ROOT=${MERKLE_ROOT}"
  [[ -n "$TX_HASH" ]] && echo "TX_OR_WORM=${TX_HASH}"
  [[ -n "$SIGNATURES_INFO" ]] && echo "SIGNATURES=${SIGNATURES_INFO}"
} > "$RESULT_FILE"

if [[ "$STATUS" == "FAIL" ]]; then
  echo "[spec_check] falha: ${REASONS[*]}" >&2
  exit 1
fi

echo "[spec_check] OK — evidência em ${RESULT_FILE}"
