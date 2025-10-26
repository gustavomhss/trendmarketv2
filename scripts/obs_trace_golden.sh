#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
PYTHON_BIN="${PYTHON_BIN:-${PYTHON:-python3}}"

TEMPO_DEFAULT="${TEMPO_URL:-${JAEGER_BASE_URL:-http://127.0.0.1:3200}}"
GOLDEN_DIR_CANDIDATE="${TRACE_GOLDEN_FIXTURES_DIR:-}"
if [ -z "$GOLDEN_DIR_CANDIDATE" ] && [ -n "${TRACE_GOLDEN_FIXTURES:-}" ]; then
  if [ -d "${TRACE_GOLDEN_FIXTURES}" ]; then
    GOLDEN_DIR_CANDIDATE="${TRACE_GOLDEN_FIXTURES}"
  fi
fi
GOLDEN_DIR="${GOLDEN_DIR_CANDIDATE:-$ROOT_DIR/ops/traces/goldens}"
EVID_DIR="${TRACE_GOLDEN_EVID_DIR:-${EVID:-${EVI:-$ROOT_DIR/out/obs_gatecheck/evidence}}}"
OUTPUT_PATH="${TRACE_GOLDEN_OUTPUT:-$EVID_DIR/golden_traces.json}"
TRACE_SOURCE_OVERRIDE="${TRACE_GOLDEN_SOURCE:-}"
MISSING_CODE_RAW="${TRACE_GOLDEN_MISSING_CODE:-23}"
ONLY_FILTER="${TRACE_GOLDEN_ONLY:-}"
if [ -z "$ONLY_FILTER" ] && [ -n "${TRACE_GOLDEN_FIXTURES:-}" ] && [ ! -d "${TRACE_GOLDEN_FIXTURES}" ]; then
  ONLY_FILTER="${TRACE_GOLDEN_FIXTURES}"
fi

if ! [[ "$MISSING_CODE_RAW" =~ ^-?[0-9]+$ ]]; then
  echo "Invalid TRACE_GOLDEN_MISSING_CODE: $MISSING_CODE_RAW" >&2
  exit 2
fi
MISSING_CODE="${MISSING_CODE_RAW}"

if ! command -v "$PYTHON_BIN" >/dev/null 2>&1; then
  echo "Python interpreter not found: $PYTHON_BIN" >&2
  exit 2
fi

if [ ! -d "$GOLDEN_DIR" ]; then
  echo "Missing golden fixtures directory: $GOLDEN_DIR" >&2
  exit 2
fi

mkdir -p "$EVID_DIR"

ARGS=(
  "--tempo-url" "$TEMPO_DEFAULT"
  "--golden-dir" "$GOLDEN_DIR"
  "--output" "$OUTPUT_PATH"
  "--missing-code" "$MISSING_CODE"
)

if [ -n "$TRACE_SOURCE_OVERRIDE" ]; then
  ARGS+=("--override" "$TRACE_SOURCE_OVERRIDE")
fi

if [ -n "$ONLY_FILTER" ]; then
  ARGS+=("--only" "$ONLY_FILTER")
fi

set +e
"$PYTHON_BIN" "$SCRIPT_DIR/obs_trace_golden.py" "${ARGS[@]}" "$@"
status=$?
set -e

if [ "$status" -eq 0 ]; then
  echo TRACE_GOLDEN_OK
elif [ "$status" -eq "$MISSING_CODE" ]; then
  echo TRACE_GOLDEN_FAIL
else
  exit "$status"
fi

exit "$status"
