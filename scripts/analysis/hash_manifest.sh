#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
EVIDENCE_DIR="$ROOT/../out/orr_gatecheck/evidence"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --evidence)
      EVIDENCE_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    *)
      echo "[hash_manifest] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$EVIDENCE_DIR"
MANIFEST="$EVIDENCE_DIR/hashes_manifest.txt"

mapfile -d '' -t FILES < <(find "$EVIDENCE_DIR" -type f ! -name "hashes_manifest.txt" -print0)

if [[ ${#FILES[@]} -eq 0 ]]; then
  : > "$MANIFEST"
else
  {
    for file in "${FILES[@]}"; do
      sha256sum "$file"
    done
  } | LC_ALL=C sort -k2 > "$MANIFEST"
fi

echo "[hash_manifest] manifesto atualizado em ${MANIFEST}"
