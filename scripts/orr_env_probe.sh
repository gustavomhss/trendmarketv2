#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; LOG="$OUT/logs"; mkdir -p "$EVI" "$LOG"
probe(){ curl -sf "$1" >/dev/null && echo UP || echo DOWN; }
PROM=$(probe "http://127.0.0.1:9090/-/ready")
OTEL=$( (curl -sf "http://127.0.0.1:13133/healthz" | grep -qi server && echo UP) || echo DOWN )
LOKI=$(probe "http://127.0.0.1:3100/loki/api/v1/labels")
TEMPO=$( (curl -sf "http://127.0.0.1:3200/" >/dev/null && echo UP) || echo DOWN )
cat > "$EVI/t1_scan.json" <<JSON
{"prom":"$PROM","otel":"$OTEL","loki":"$LOKI","tempo":"$TEMPO"}
JSON
