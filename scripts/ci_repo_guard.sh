#!/usr/bin/env bash
set -euo pipefail
OUT="out/repo_guard"; mkdir -p "$OUT"
LIST="ops/sanity/denylist_patterns.txt"

# Arquivos que vamos varrer (texto), ignorando binários e a própria saída
INCLUDE=(
  "**/*.md" "**/*.yaml" "**/*.yml" "**/*.json" "**/*.sh" "**/*.py" "**/*.rs" "**/*.toml" "**/*.txt"
)
EXCLUDE=(
  ".git" "out/" "node_modules/" "target/" "*.zip" "*.png" "*.jpg" "*.svg"
)

# Monta o comando ripgrep se existir, senão usa grep -R
if command -v rg >/dev/null 2>&1; then
  FINDER=(rg --line-number --no-heading)
  for e in "${EXCLUDE[@]}"; do FINDER+=(--glob "!$e"); done
  for i in "${INCLUDE[@]}"; do FINDER+=(--glob "$i"); done
else
  FINDER=(grep -RIn)
fi

FAIL=0
REPORT="$OUT/denylist_hits.txt"
>"$REPORT"

if [ ! -f "$LIST" ]; then
  echo "[repo-guard] denylist não encontrada em $LIST" | tee -a "$REPORT"
  exit 1
fi

while IFS= read -r pattern || [ -n "$pattern" ]; do
  # ignora linhas vazias e comentários
  [[ -z "$pattern" || "$pattern" =~ ^# ]] && continue
  if "${FINDER[@]}" -- "$pattern" . >>"$REPORT" 2>/dev/null; then
    echo "[repo-guard] padrão proibido encontrado: $pattern" | tee -a "$REPORT"
    FAIL=1
  fi
done < "$LIST"

if [ $FAIL -ne 0 ]; then
  echo "\n✖ Repo guard falhou. Revise $REPORT" | tee "$OUT/summary.txt"
  exit 2
fi

echo "✔ Repo guard OK" | tee "$OUT/summary.txt"
