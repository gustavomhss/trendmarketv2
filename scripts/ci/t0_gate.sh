#!/usr/bin/env bash
set -euo pipefail

mode="strict"
output="out/obs_gatecheck/T0_discovery.json"
manif="docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_filemap_v_7.json"
notes_extra=()

while (($#)); do
  case "$1" in
    --mode)
      mode="$2"
      shift 2
      ;;
    --output)
      output="$2"
      shift 2
      ;;
    --manifest)
      manif="$2"
      shift 2
      ;;
    --note)
      notes_extra+=("$2")
      shift 2
      ;;
    *)
      echo "Unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

command -v jq >/dev/null 2>&1 || { echo "jq is required" >&2; exit 1; }
mkdir -p "$(dirname "$output")"
working_manifest="${RUNNER_TEMP:-/tmp}/s7_manifest.ndjson"
rescue=false
rm -f "$working_manifest"
if [[ -s "$manif" ]]; then
  cp "$manif" "$working_manifest"
else
  rescue=true
  : > "$working_manifest"
  git ls-files -- 'docs/DNA/Roadmap e Sprints/Q2/Sprint 7/s_7_*.md' | while IFS= read -r path; do
    [[ -z "$path" ]] && continue
    jq -n --arg path "$path" '{"path":$path}' >> "$working_manifest"
  done
fi
checked=0
missing_json='[]'
badhash_json='[]'
while IFS= read -r raw_line || [[ -n "$raw_line" ]]; do
  [[ -z "$raw_line" ]] && continue
  path=$(jq -r '.path? // empty' <<<"$raw_line")
  [[ -z "$path" ]] && continue
  checked=$((checked + 1))
  if [[ ! -f "$path" ]]; then
    missing_json=$(jq --arg path "$path" '. + [$path]' <<<"$missing_json")
    missing_json=$(jq -c '.' <<<"$missing_json")
    continue
  fi
  sha_expected=$(jq -r '.sha1? // empty' <<<"$raw_line")
  if [[ -n "$sha_expected" ]]; then
    sha_calc=$(git hash-object "$path")
    if [[ "$sha_calc" != "$sha_expected" ]]; then
      bytes_calc=$(stat -c%s "$path")
      badhash_json=$(jq --arg path "$path" --arg expected "$sha_expected" --arg calc "$sha_calc" --argjson bytes "$bytes_calc" '. + [{"path":$path,"sha1_expected":$expected,"sha1_calc":$calc,"bytes_calc":$bytes}]' <<<"$badhash_json")
      badhash_json=$(jq -c '.' <<<"$badhash_json")
    fi
  fi
done < "$working_manifest"
missing_count=$(jq 'length' <<<"$missing_json")
badhash_count=$(jq 'length' <<<"$badhash_json")
status="PASS"
if [[ "$missing_count" -gt 0 || "$badhash_count" -gt 0 ]]; then
  status="FAIL"
fi
note_parts=()
if [[ "$rescue" == true ]]; then
  note_parts+=("rescue-manifest mode")
fi
note_parts+=("checked=$checked")
note_parts+=("missing=$missing_count")
note_parts+=("badhash=$badhash_count")
for extra in "${notes_extra[@]:-}"; do
  [[ -z "$extra" ]] && continue
  note_parts+=("$extra")
done
notes=""
if [[ "${#note_parts[@]}" -gt 0 ]]; then
  notes=$(IFS='; '; printf '%s' "${note_parts[*]}")
fi
rescue_flag=false
if [[ "$rescue" == true ]]; then
  rescue_flag=true
fi
jq -n \
  --arg gate "T0" \
  --arg status "$status" \
  --arg notes "$notes" \
  --argjson checked "$checked" \
  --argjson missing "$missing_json" \
  --argjson badhash "$badhash_json" \
  --argjson rescue "$rescue_flag" \
  '{"gate":$gate,"status":$status,"checked":$checked,"missing":$missing,"badhash":$badhash,"rescue":$rescue,"notes":$notes}' \
  > "$output"
missing_msg="missing=${missing_count}"
badhash_msg="badhash=${badhash_count}"
rescue_msg="rescue=${rescue_flag}"
echo "T0 status $status; checked=$checked; ${missing_msg}; ${badhash_msg}; ${rescue_msg}" >&2
if [[ "$mode" == "strict" && "$status" == "FAIL" ]]; then
  exit 1
fi
exit 0
