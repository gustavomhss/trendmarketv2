#!/usr/bin/env bash
set -euo pipefail

failures=()

record_failure() {
  failures+=("$1")
}

check_workflow_call() {
  local file=".github/workflows/_s7-orr.yml"
  if ! grep -q 'workflow_call:' "$file"; then
    record_failure "workflow_call não configurado em $file"
  fi
}

check_pins() {
  local -a workflows=(
    ".github/workflows/s7-exec.yml"
    ".github/workflows/_s7-orr.yml"
    ".github/workflows/s7-t0.yml"
    ".github/workflows/s7-t0-fast.yml"
    ".github/workflows/s7-t0-strict.yml"
    ".github/workflows/s7-validator.yml"
  )
  local checkout_sha="actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683"
  local upload_sha="actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02"
  local download_sha="actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093"
  local setup_python_sha="actions/setup-python@42375524e23c412d93fb67b49958b491fce71c38"
  local banned_sha_part_a="5d5fd0d0f13b66b0d7c0d180fba59a9d6"
  local banned_sha_part_b="f4b4c90"
  local banned_sha="${banned_sha_part_a}${banned_sha_part_b}"

  if git grep -n "$banned_sha" >/dev/null 2>&1; then
    record_failure "SHA banido $banned_sha ainda presente no repositório"
  fi

  for workflow in "${workflows[@]}"; do
    if grep -q 'actions/checkout@' "$workflow" && ! grep -q "$checkout_sha" "$workflow"; then
      record_failure "${workflow}: checkout não pinado em $checkout_sha"
    fi
    if grep -q 'actions/upload-artifact@' "$workflow" && ! grep -q "$upload_sha" "$workflow"; then
      record_failure "${workflow}: upload-artifact sem pin canônico"
    fi
    if grep -q 'actions/download-artifact@' "$workflow" && ! grep -q "$download_sha" "$workflow"; then
      record_failure "${workflow}: download-artifact sem pin canônico"
    fi
    if grep -q 'actions/setup-python@' "$workflow" && ! grep -q "$setup_python_sha" "$workflow"; then
      record_failure "${workflow}: setup-python sem pin canônico"
    fi
  done
}

run_yamllint() {
  if [[ "${SELF_CHECK_SKIP_YAMLLINT:-0}" == "1" ]]; then
    return
  fi
  if ! command -v yamllint >/dev/null 2>&1; then
    python -m pip install --quiet --user yamllint >/dev/null 2>&1 || {
      record_failure "yamllint indisponível e instalação falhou"
      return
    }
    export PATH="$PATH:$HOME/.local/bin"
  fi

  local -a targets=(
    "models/tests/mrt_twap_5m.yml"
    "models/tests/stg_oracle_quotes.yml"
    "obs/ops/watchers/tests/a110_rules_test.yaml"
  )
  if ! yamllint "${targets[@]}" >/dev/null 2>&1; then
    record_failure "yamllint detectou violações nos arquivos alvo"
  fi
}

run_gitleaks() {
  if [[ "${SELF_CHECK_SKIP_GITLEAKS:-0}" == "1" ]]; then
    return
  fi
  if ! command -v gitleaks >/dev/null 2>&1; then
    record_failure "gitleaks não encontrado no PATH"
    return
  fi
  mkdir -p out/evidence/T2_security
  if ! gitleaks detect --source . --no-banner --redact --report-format json --report-path out/evidence/T2_security/gitleaks_report.json >/dev/null 2>&1; then
    record_failure "gitleaks detect retornou código diferente de zero"
  fi
}

run_t7_dry_run() {
  local out_dir="out/obs_gatecheck/T7_append_only_selfcheck"
  rm -rf "$out_dir"
  if ! scripts/guards/append_only.sh --out-dir "$out_dir" --base HEAD --head HEAD >/dev/null 2>&1; then
    record_failure "append_only.sh falhou no dry-run"
    return
  fi
  if [[ ! -f "$out_dir/summary.txt" ]]; then
    record_failure "summary.txt não gerado no dry-run do append-only"
  fi
  if [[ ! -f "$out_dir/violations.json" ]]; then
    record_failure "violations.json não gerado no dry-run do append-only"
  fi
}

main() {
  check_workflow_call
  check_pins
  run_yamllint
  run_gitleaks
  run_t7_dry_run

  if ((${#failures[@]})); then
    printf 'SELF-CHECK: FAIL\n' >&2
    for failure in "${failures[@]}"; do
      printf ' - %s\n' "$failure" >&2
    done
    exit 1
  fi
  printf 'SELF-CHECK: PASS\n'
}

main "$@"
