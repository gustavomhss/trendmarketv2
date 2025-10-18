#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'; export LC_ALL=C; export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DEFAULT_OUT="$ROOT/out/orr_gatecheck/evidence"
OUT_DIR="${EVID:-$DEFAULT_OUT}"

args=($@)
for ((i=0;i<${#args[@]};i++)); do
  case "${args[$i]}" in
    --out)
      i=$((i+1))
      OUT_DIR="$(cd "${args[$i]}" && pwd)"
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

COUNT=$(find "$OUT_DIR" -type f ! -name "spec_check.txt" | wc -l | tr -d ' ')

PASS=1
REASONS=()

if [[ ! -s "$POLICY_HASH_FILE" ]]; then
  PASS=0
  REASONS+=("policy_hash.txt ausente ou vazio")
fi

if [[ ! -s "$BUNDLE_FILE" ]]; then
  PASS=0
  REASONS+=("bundle.sha256.txt ausente ou vazio")
fi

if [[ ! -s "$PROVENANCE_FILE" ]]; then
  PASS=0
  REASONS+=("provenance_onchain.json ausente")
fi

if [[ ! -s "$SIGNATURES_FILE" ]]; then
  PASS=0
  REASONS+=("signatures.json ausente")
fi

POLICY_HASH_RECORDED=""
EXPECTED_HASH=""
if [[ -s "$POLICY_HASH_FILE" ]]; then
  POLICY_HASH_RECORDED="$(tr -d '\n' < "$POLICY_HASH_FILE")"
  EXPECTED_HASH=$(cat "$ROOT/configs/policies/project.yml" "$ROOT/configs/policies/env.yml" "$ROOT/configs/policies/mbp_s2.yml" | sha256sum | awk '{print $1}')
  if [[ "$POLICY_HASH_RECORDED" != "$EXPECTED_HASH" ]]; then
    PASS=0
    REASONS+=("policy_hash divergente do esperado")
  fi
fi

BUNDLE_SHA=""
if [[ -s "$BUNDLE_FILE" ]]; then
  BUNDLE_SHA="$(tr -d '\n' < "$BUNDLE_FILE")"
  if [[ ${#BUNDLE_SHA} -ne 64 ]]; then
    PASS=0
    REASONS+=("bundle.sha256 inválido")
  fi
fi

cat > "$REFMAP_FILE" <<JSON
{
  "metrics": ["lat_p95_ms", "err5xx_rate", "burn4h", "invariant", "inp_p75_ms", "obs_uptime"],
  "policy_hash": "$(cat "$POLICY_HASH_FILE" 2>/dev/null || echo "")",
  "evidence": ["bundle.sha256.txt", "provenance_onchain.json", "signatures.json", "env_dump.txt"],
  "file_count": $COUNT
}
JSON

if [[ $PASS -eq 1 ]]; then
  {
    echo "RESULT=PASS"
    echo "POLICY_HASH=${POLICY_HASH_RECORDED}"
    echo "BUNDLE_SHA256=${BUNDLE_SHA}"
    echo "FILES_IN_EVIDENCE=$COUNT"
  } > "$RESULT_FILE"
else
  {
    echo "RESULT=FAIL"
    echo "REASON=Missing ${REASONS[*]}"
    [[ -n "$POLICY_HASH_RECORDED" ]] && echo "POLICY_HASH=${POLICY_HASH_RECORDED}"
    [[ -n "$BUNDLE_SHA" ]] && echo "BUNDLE_SHA256=${BUNDLE_SHA}"
    echo "FILES_IN_EVIDENCE=$COUNT"
  } > "$RESULT_FILE"
  exit 1
fi
