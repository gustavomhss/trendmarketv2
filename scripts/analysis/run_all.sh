#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'; export LC_ALL=C; export TZ=UTC

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
DEFAULT_EVID="$ROOT/out/orr_gatecheck/evidence"
EVID="${EVID:-$DEFAULT_EVID}"
SEED_DIR="$ROOT/seeds"

args=($@)
for ((i=0;i<${#args[@]};i++)); do
  case "${args[$i]}" in
    --out)
      i=$((i+1))
      EVID="$(cd "${args[$i]}" && pwd)"
      ;;
    --seed-dir)
      i=$((i+1))
      SEED_DIR="$(cd "${args[$i]}" && pwd)"
      ;;
  esac
done

mkdir -p "$EVID/analysis" "$EVID/rum" "$EVID/traces" "$EVID/burnrate"

bash "$SCRIPT_DIR/burnrate_report.sh" --out "$EVID" --seed-file "$SEED_DIR/engine/burnrate_seed.json"
bash "$SCRIPT_DIR/cwv_report.sh" --out "$EVID" --seed-file "$SEED_DIR/rum/cwv_seed.json"
bash "$SCRIPT_DIR/spans_report.sh" --out "$EVID" --seed-file "$SEED_DIR/engine/spans_seed.json"
bash "$SCRIPT_DIR/cardinality_report.sh" --out "$EVID" --seed-file "$SEED_DIR/load/cardinality_seed.json"

INDEX_FILE="$EVID/analysis/index.html"
DEFAULT_REL="$(cd "$DEFAULT_EVID" && pwd)"
COMMAND_OUT="$EVID"
if [[ "$COMMAND_OUT" == "$DEFAULT_REL" ]]; then
  COMMAND_OUT="out/orr_gatecheck/evidence"
fi
COMMAND="bash scripts/analysis/run_all.sh --out ${COMMAND_OUT} --seed-dir seeds"
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
