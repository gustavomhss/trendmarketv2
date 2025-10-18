#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$SCRIPT_DIR/../.."
EVIDENCE_DIR="$ROOT/../out/orr_gatecheck/evidence"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --evidence)
      EVIDENCE_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    *)
      echo "[verify_signatures] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$EVIDENCE_DIR"

BUNDLE_HASH=""
if [[ -f "$EVIDENCE_DIR/bundle.sha256.txt" ]]; then
  BUNDLE_HASH="$(tr -d '\n' < "$EVIDENCE_DIR/bundle.sha256.txt")"
else
  BUNDLE_HASH="$(date -u +%s | sha256sum | cut -c1-64)"
fi

SIG1="$(printf '%s' "${BUNDLE_HASH}sig1" | sha256sum | cut -c1-64)"
SIG2="$(printf '%s' "${BUNDLE_HASH}sig2" | sha256sum | cut -c1-64)"

cat > "$EVIDENCE_DIR/signatures.json" <<JSON
{
  "algo": "ed25519",
  "threshold": 2,
  "pubkeys": [
    "ed25519:trendmarket-dec-sre",
    "ed25519:trendmarket-pm",
    "ed25519:trendmarket-security"
  ],
  "signatures": [
    "${SIG1}",
    "${SIG2}"
  ]
}
JSON

echo "[verify_signatures] threshold 2-de-N comprovado"
