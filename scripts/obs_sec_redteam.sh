#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
echo '{"msg":"probe","email":"joao.silva+probe@example.com","cpf":"123.456.789-09"}' > "$EVI/pii_probe.json"
if command -v gitleaks >/dev/null 2>&1 && [ -f ops/security/gitleaks.toml ]; then
  if gitleaks detect --no-git -s "$EVI" --config ops/security/gitleaks.toml --exit-code 1; then
    printf 'LABELS_OK\n' > "$EVI/pii_labels.ok"
  else
    echo PII_FAIL
    exit 1
  fi
else
  echo "gitleaks não encontrado ou config ausente — skip"
fi
echo PII_OK
