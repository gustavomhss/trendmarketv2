#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'; export LC_ALL=C; export TZ=UTC

# Diretórios base
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Evidence: precedência Ambiente (EVID) -> CLI (--out/--evidence) -> Default
DEFAULT_EVID="$ROOT/../out/orr_gatecheck/evidence"
EVID="${EVID:-$DEFAULT_EVID}"

# Seeds (padrão)
SEED_DIR="$ROOT/seeds"

# Parsing de argumentos
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out|--evidence)
      shift
      EVID="$(cd "${1:-$EVID}" && pwd)"
      shift
      ;;
    --seed-dir)
      shift
      SEED_DIR="$(cd "${1:-$SEED_DIR}" && pwd)"
      shift
      ;;
    *)
      echo "[run_all] argumento desconhecido: $1" >&2
      exit 1
      ;;
  esac
done

# Garantir estrutura
mkdir -p "$EVID" \
         "$EVID/analysis" "$EVID/rum" "$EVID/traces" "$EVID/burnrate"

# Executa relatórios (respeitando --out e seeds)
bash "$SCRIPT_DIR/burnrate_report.sh"   --out "$EVID" --seed-file "$SEED_DIR/engine/burnrate_seed.json"
bash "$SCRIPT_DIR/cwv_report.sh"        --out "$EVID" --seed-file "$SEED_DIR/rum/cwv_seed.json"
bash "$SCRIPT_DIR/spans_report.sh"      --out "$EVID" --seed-file "$SEED_DIR/engine/spans_seed.json"
bash "$SCRIPT_DIR/cardinality_report.sh" --out "$EVID" --seed-file "$SEED_DIR/load/cardinality_seed.json"

# Monta índice HTML com botão de "Copiar comando"
INDEX_FILE="$EVID/analysis/index.html"

# Se o caminho efetivo do EVID for o default "canônico", exibir caminho relativo no comando copiado
# (melhor DX ao colar no terminal)
_default_abs="$(cd "$DEFAULT_EVID" 2>/dev/null && pwd -P 2>/dev/null || echo "$DEFAULT_EVID")"
_evid_abs="$(cd "$EVID" && pwd -P 2>/dev/null || echo "$EVID")"
COMMAND_OUT="$_evid_abs"
if [[ "$_evid_abs" == "$_default_abs" ]]; then
  COMMAND_OUT="out/obs_gatecheck/evidence"
fi

COMMAND="bash scripts/analysis/run_all.sh --out ${COMMAND_OUT} --seed-dir seeds"

cat > "$INDEX_FILE" <<HTML
<!DOCTYPE html>
<html lang="pt-BR">
<head>
  <meta charset="UTF-8" />
  <title>MBP Sprint 2 — Evidence Index</title>
  <style>
    body { font-family: system-ui, -apple-system, "Segoe UI", Roboto, Arial, sans-serif; margin: 2rem; background: #0b1120; color: #e2e8f0; }
    h1 { color: #38bdf8; margin-bottom: .5rem; }
    h2 { color: #93c5fd; }
    section { margin-bottom: 1.5rem; }
    .btn-copy { background: #22d3ee; border: none; color: #0f172a; padding: 0.6rem 1rem; cursor: pointer; border-radius: 6px; font-weight: 600; }
    .seed, .cmd { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace; background: #1e293b; padding: 0.4rem 0.6rem; border-radius: 4px; display: inline-block; margin-top: 0.4rem; }
    a { color: #93c5fd; text-decoration: none; }
    a:hover { text-decoration: underline; }
  </style>
</head>
<body>
  <h1>MBP Sprint 2 — Evidence Index</h1>
  <section>
    <p>Use o botão abaixo para copiar o comando determinístico com as seeds versionadas.</p>
    <button class="btn-copy" data-command="${COMMAND}">Copiar comando</button>
    <div class="seed">Seed dir: ${SEED_DIR}</div>
    <div class="cmd" style="display:block;margin-top:.5rem;">${COMMAND}</div>
  </section>
  <section>
    <h2>Artefatos Chave</h2>
    <ul>
      <li><a href="burnrate_report.csv">burnrate_report.csv</a></li>
      <li><a href="cwv_report.csv">cwv_report.csv</a></li>
      <li><a href="spans_report.csv">spans_report.csv</a></li>
      <li><a href="../cardinality.txt">cardinality.txt</a></li>
    </ul>
  </section>
  <script>
    const btn = document.querySelector('.btn-copy');
    btn.addEventListener('click', function () {
      navigator.clipboard.writeText(this.dataset.command)
        .then(() => { this.textContent = 'Comando copiado!'; })
        .catch(() => { this.textContent = 'Falha ao copiar'; });
      setTimeout(() => { this.textContent = 'Copiar comando'; }, 2400);
    });
  </script>
</body>
</html>
HTML

echo "✅ Evidence index gerado em: $INDEX_FILE"
