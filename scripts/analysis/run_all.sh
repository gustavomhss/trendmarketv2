#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'
export LC_ALL=C
export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUT_DIR="$ROOT/../out/orr_gatecheck/evidence"
SEED_DIR="$ROOT/seeds"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out)
      OUT_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    --seed-dir)
      SEED_DIR="$(cd "$2" && pwd)"
      shift 2
      ;;
    *)
      echo "[run_all] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

mkdir -p "$OUT_DIR" "$OUT_DIR/analysis" "$OUT_DIR/rum" "$OUT_DIR/traces" "$OUT_DIR/burnrate"

bash "$SCRIPT_DIR/burnrate_report.sh" --out "$OUT_DIR" --seed-file "$SEED_DIR/engine/burnrate_seed.json"
bash "$SCRIPT_DIR/cwv_report.sh" --out "$OUT_DIR" --seed-file "$SEED_DIR/rum/cwv_seed.json"
bash "$SCRIPT_DIR/spans_report.sh" --out "$OUT_DIR" --seed-file "$SEED_DIR/engine/spans_seed.json"
bash "$SCRIPT_DIR/cardinality_report.sh" --out "$OUT_DIR" --seed-file "$SEED_DIR/load/cardinality_seed.json"

INDEX_FILE="$OUT_DIR/analysis/index.html"
COMMAND="bash scripts/analysis/run_all.sh --out out/orr_gatecheck/evidence --seed-dir seeds"
cat > "$INDEX_FILE" <<HTML
<!DOCTYPE html>
<html lang="pt-BR">
<head>
  <meta charset="UTF-8" />
  <title>MBP Sprint 2 — Evidence Index</title>
  <style>
    body { font-family: "Fira Sans", Arial, sans-serif; margin: 2rem; background: #0b1120; color: #e2e8f0; }
    h1 { color: #38bdf8; }
    section { margin-bottom: 1.5rem; }
    .btn-copy { background: #22d3ee; border: none; color: #0f172a; padding: 0.6rem 1rem; cursor: pointer; border-radius: 6px; font-weight: 600; }
    .seed { font-family: "Fira Mono", monospace; background: #1e293b; padding: 0.4rem 0.6rem; border-radius: 4px; display: inline-block; margin-top: 0.4rem; }
  </style>
</head>
<body>
  <h1>MBP Sprint 2 — Evidence Index</h1>
  <section>
    <p>Use o botão abaixo para copiar o comando determinístico com as seeds versionadas.</p>
    <button class="btn-copy" data-command="${COMMAND}">Copiar comando</button>
    <div class="seed">Seed dir: ${SEED_DIR}</div>
  </section>
  <section>
    <h2>Artefatos Chave</h2>
    <ul>
      <li><a href="burnrate_report.csv">burnrate_report.csv</a></li>
      <li><a href="cwv_report.csv">cwv_report.csv</a></li>
      <li><a href="spans_report.csv">spans_report.csv</a></li>
      <li><a href="cardinality_budget.csv">cardinality_budget.csv</a></li>
    </ul>
  </section>
  <script>
    document.querySelector('.btn-copy').addEventListener('click', function () {
      navigator.clipboard.writeText(this.dataset.command);
      this.textContent = 'Comando copiado!';
      setTimeout(() => { this.textContent = 'Copiar comando'; }, 2400);
    });
  </script>
</body>
</html>
HTML
