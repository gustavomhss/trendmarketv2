#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
METRICS_URL="${METRICS_URL:-http://127.0.0.1:9464/metrics}"
HEALTHZ_URL="${HEALTHZ_URL:-http://127.0.0.1:13133/healthz}"
REQUIRED_METRICS_STR="${REQUIRED_METRICS:-otelcol_process_uptime amm_op_latency_seconds hook_executions_total data_freshness_seconds cdc_lag_seconds}"
PROBE_TIMEOUT_SECS="${PROBE_TIMEOUT_SECS:-60}"
if ! [[ "$PROBE_TIMEOUT_SECS" =~ ^[0-9]+$ ]] || [[ "$PROBE_TIMEOUT_SECS" -le 0 ]]; then
  PROBE_TIMEOUT_SECS=60
fi
if [[ -z "$REQUIRED_METRICS_STR" ]]; then
  REQUIRED_METRICS_STR="otelcol_process_uptime amm_op_latency_seconds hook_executions_total data_freshness_seconds cdc_lag_seconds"
fi
if ! command -v curl >/dev/null 2>&1; then
  printf '{"healthz_url":"%s","metrics_url":"%s","healthz_http":0,"metrics_http":0,"found_metrics":[],"passed":false}\n' "$HEALTHZ_URL" "$METRICS_URL"
  echo "T6 probe failed" >&2
  exit 1
fi
now() { date +%s; }
http_status() {
  local code
  code=$(curl -fsS -m 3 -o /dev/null -w "%{http_code}" "$1" 2>/dev/null || true)
  if [[ -z "$code" ]] || ! [[ "$code" =~ ^[0-9]+$ ]]; then
    printf '0'
  else
    printf '%d' $((10#$code))
  fi
}
http_body() {
  curl -fsS -m 5 "$1" 2>/dev/null || true
}
deadline=$(( $(now) + PROBE_TIMEOUT_SECS ))
health_status=0
metrics_status=0
metrics_body=""
while :; do
  health_status=$(http_status "$HEALTHZ_URL")
  metrics_status=$(http_status "$METRICS_URL")
  if [[ "$health_status" == "200" && "$metrics_status" == "200" ]]; then
    metrics_body=$(http_body "$METRICS_URL")
    break
  fi
  if (( $(now) >= deadline )); then
    break
  fi
  sleep 1
done
found_list=()
if [[ -n "$metrics_body" ]]; then
  for metric in $REQUIRED_METRICS_STR; do
    [[ -z "$metric" ]] && continue
    if printf '%s\n' "$metrics_body" | grep -Eq "^${metric}(\\{| )"; then
      found_list+=("$metric")
    fi
  done
fi
pass=false
if [[ "$health_status" == "200" && "$metrics_status" == "200" && "${#found_list[@]}" -ge 1 ]]; then
  pass=true
fi
printf '{'
printf '"healthz_url":"%s",' "$HEALTHZ_URL"
printf '"metrics_url":"%s",' "$METRICS_URL"
printf '"healthz_http":%s,' "$health_status"
printf '"metrics_http":%s,' "$metrics_status"
printf '"found_metrics":['
for i in "${!found_list[@]}"; do
  printf '"%s"' "${found_list[$i]}"
  if (( i < ${#found_list[@]} - 1 )); then
    printf ','
  fi
done
printf '],'
printf '"passed":%s' "$pass"
printf '}\n'
if [[ "$pass" != "true" ]]; then
  echo "T6 probe failed" >&2
  exit 1
fi
