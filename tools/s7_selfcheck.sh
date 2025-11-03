#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

errors=()

tmp_actions="$(mktemp)"
python - <<'PY' >"$tmp_actions"
import pathlib

sha_map = {
    'actions/checkout': '11bd71901bbe5b1630ceea73d27597364c9af683',
    'actions/upload-artifact': 'ea165f8d65b6e75b540449e92b4886f43607fa02',
    'actions/download-artifact': 'd3f86a106a0bac45b974a628896c90dbdf5c8093',
    'actions/setup-python': '42375524e23c412d93fb67b49958b491fce71c38',
}
allowed_suffixes = ('.yml', '.yaml', '.yml.off', '.yaml.off')
issues = []
for path in pathlib.Path('.github/workflows').rglob('*'):
    if not path.is_file() or not str(path).endswith(allowed_suffixes):
        continue
    for lineno, raw_line in enumerate(path.read_text().splitlines(), start=1):
        stripped = raw_line.strip()
        if not stripped.startswith('uses:') and not stripped.startswith('- uses:'):
            continue
        normalized = stripped
        if normalized.startswith('-'):
            normalized = normalized[1:].strip()
        if not normalized.startswith('uses:'):
            continue
        value = normalized.split('uses:', 1)[1].strip()
        if not value.startswith('actions/'):
            continue
        action_part, _, version_part = value.partition('@')
        if not version_part:
            issues.append(f"{path}:{lineno}: missing version for {action_part}")
            continue
        version = version_part.split()[0]
        expected = sha_map.get(action_part)
        if expected and version != expected:
            issues.append(f"{path}:{lineno}: expected {expected} for {action_part} but found {version}")
if issues:
    for issue in issues:
        print(issue)
PY
if [[ -s "$tmp_actions" ]]; then
  errors+=("Found non-canonical action pins:\n$(cat "$tmp_actions")")
fi
rm -f "$tmp_actions"

if rg -n "5d5fd0d0f13b66b0d7c0d180fba59a9d6f4b4c90" --hidden --glob "*" --glob '!tools/s7_selfcheck.sh' >/dev/null; then
  errors+=("Legacy upload-artifact SHA detected (5d5fd0d0f13b66b0d7c0d180fba59a9d6f4b4c90)")
fi

if ! rg -q "^  workflow_call:" .github/workflows/_s7-orr.yml; then
  errors+=("Reusable callee missing workflow_call trigger")
fi

t0_json="out/obs_gatecheck/T0_discovery.json"
if [[ -f "$t0_json" ]]; then
  tmp_t0="$(mktemp)"
  python - <<'PY' >"$tmp_t0"
import json
import pathlib
import sys
path = pathlib.Path('out/obs_gatecheck/T0_discovery.json')
try:
    data = json.loads(path.read_text())
except FileNotFoundError:
    sys.exit(0)
except json.JSONDecodeError as exc:
    print(f"JSON decode error: {exc}")
    sys.exit(0)
required = {'gate', 'status', 'checked', 'missing', 'badhash', 'rescue', 'notes'}
missing = required - data.keys()
if missing:
    print(f"Missing keys: {sorted(missing)}")
if data.get('gate') != 'T0':
    print("Gate field must equal 'T0'")
if data.get('status') not in {'PASS', 'FAIL'}:
    print("Status must be PASS or FAIL")
for key in ('missing', 'badhash'):
    if not isinstance(data.get(key), list):
        print(f"Field '{key}' must be a list")
PY
  if [[ -s "$tmp_t0" ]]; then
    errors+=("Invalid T0_discovery.json:\n$(cat "$tmp_t0")")
  fi
  rm -f "$tmp_t0"
else
  errors+=("Missing out/obs_gatecheck/T0_discovery.json")
fi

echo "--- S7 Self-check Report ---"
if ((${#errors[@]})); then
  for err in "${errors[@]}"; do
    printf 'ERROR: %s\n' "$err"
  done
  echo "SELF-CHECK: FAIL"
  exit 1
fi

echo "SELF-CHECK: PASS"
