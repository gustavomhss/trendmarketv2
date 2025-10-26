#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
STATUS_FILE="$ROOT_DIR/out/s6_scorecards/guard_status.txt"

if [[ ! -f "$STATUS_FILE" ]]; then
  echo "S6-E-GUARD-MISSING: guard_status.txt não encontrado" >&2
  exit 1
fi

status="$(tr -d '\r' < "$STATUS_FILE" | tr -d '\n')"
if [[ "$status" != "PASS" ]]; then
  echo "S6-E-GUARD-FAIL: estado ${status}" >&2
  exit 1
fi

echo "PASS"
