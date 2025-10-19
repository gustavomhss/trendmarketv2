# S4 — v1.3 FINAL (Última rodada de melhorias do Painel Oficial) — Plan→Exec→ORR

## 0) TL;DR (refinado)

**Objetivo (2 semanas):** Endurecer o MVP do MBP e fechar CE$ Fundações com **Gate Pre‑GA (M2) aprovado**.
**SLOs de aceite:** DEC p95 ≤ **800 ms** por 60 min @ 120 rps (**5xx=0**); **CDC lag p95 ≤ 120 s** (tabelas quentes); **schema_drift=0** e `data_contract_break=false`; **dbt tests=pass**; **Hook Coverage ≥ 98%** e **Audit Coverage ≥ 99%** (24h); **INP p75 ≤ 200 ms**; **segurança sem críticos** (SBOM/SAST/Secrets) e **logs 0 PII**.
**Painel Oficial (permanente):** Donald Knuth, Steve Jobs, Fernando Pérez, Alan Kay, Leslie Lamport, Vitalik Buterin.
**Critério adicional:** Evidence Pack com **âncora de integridade** (raiz Merkle + tag Git) e demo “one‑pager”.

---

## A) Delta v1.2 → v1.3 (aprovado pelo Painel)

1. **Invariantes formais e temporalidade** (Knuth+Lamport): safety/liveness/ordem temporal formalizadas e materializadas em `docs/spec/invariants.md` e `docs/spec/tla/dec_pre_ga.tla` (mínimo executável).
2. **UX de um comando impecável** (Jobs): `make prega` garante env pinado, ORR completo, bundle com SHA‑256, **âncora Merkle** e **tag Git**.
3. **Reprodutibilidade & locks** (Pérez): `requirements.lock`, `Cargo.lock`, `package-lock.json`, Dockerfile de ORR com digest pinado em runtime e notebook de análise pós‑perf.
4. **Fronteiras arquiteturais** (Kay): pastas por domínio com harness de simulação desacoplado.
5. **Precisão temporal de rollback** (Lamport): rollback/disparo ≤ 10 min, métricas de recuperação adicionadas.
6. **Fundação econômica CE$** (Vitalik): política CE$ SLO‑aware e **âncora de integridade** para ADRs/schemas/bundle; opção de publicação on‑chain deferida para S5.

---

## 1) Invariantes, Liveness e Ordem Temporal

Criar `docs/spec/invariants.md`:

```md
# Invariantes (Safety) e Propriedades de Liveness

## Safety
I1 — **No‑Trade‑After‑Resolve**: ∀q∈quotes, q.ts ≤ resolved_at(market(q)).
I2 — **Backward‑Compat**: required_old ⊆ required_new ∧ ∀f∈props_old: type_old(f)=type_new(f).
I3 — **TWAP Bound**: twap_divergence_percent ≤ 1.0% quando market.status≠frozen.
I4 — **Zero‑PII**: nenhum campo classificado PII sai do pipeline de logs.
I5 — **Fail‑Closed CI**: deploy bloqueado se schema_drift>0 ∨ contract_break=true ∨ dbt_tests≠pass.

## Liveness
L1 — **Rollback Timely**: rollback inicia ≤ 10 min após SLOBudgetBreach.
L2 — **CDC Recovery**: cdc_lag_p95 volta ≤120 s em ≤20 min após mitigação.
L3 — **ADRs Publicados**: ADR‑001..003 aceitos antes do Gate M2.

## Ordem Temporal
O1 — measure(DEC) → breach(DEC) → page(SRE) → degrade/rollback → recover(DEC≤0,8s). Atraso total ≤10 min.
O2 — schema_change(PR) → CI.compat_check → {pass→merge | fail→block}; sem bypass sem waiver timeboxed.
```

Criar `docs/spec/tla/dec_pre_ga.tla` (mínimo verificável):

```tla
---- MODULE dec_pre_ga ----
EXTENDS Naturals, Sequences
VARIABLES dec_p95, breach, rollback, recovered
Init == /\ dec_p95 \in Nat /\ dec_p95 = 0 /\ breach = FALSE /\ rollback = FALSE /\ recovered = FALSE
Next ==
  \/ /\ dec_p95' \in Nat /\ dec_p95' > 800 /\ breach' = TRUE /\ UNCHANGED <<rollback, recovered>>
  \/ /\ breach = TRUE /\ rollback' = TRUE /\ UNCHANGED <<dec_p95, recovered>>
  \/ /\ rollback = TRUE /\ dec_p95' <= 800 /\ recovered' = TRUE /\ UNCHANGED <<breach>>
Spec == Init /\ [][Next]_<<dec_p95, breach, rollback, recovered>>
Safety == ~(rollback = FALSE /\ recovered = TRUE /\ dec_p95 > 800)
Liveness == WF_<<dec_p95, breach, rollback, recovered>>(rollback)
====
```

---

## 2) One‑Command UX (Makefile final)

Criar/atualizar `Makefile`:

```make
SHELL := /usr/bin/env bash
.PHONY: prega env.pin orr bundle anchors flame micro dbt.docs rum.docs nb.perf

prega: env.pin orr bundle anchors nb.perf ## One-shot: valida tudo, empacota, ancora e gera análise

env.pin:
	set -euo pipefail; ./scripts/env_pin_check.sh

orr:
	set -euo pipefail; ./scripts/orr_s4_run.sh

bundle:
	set -euo pipefail; ./scripts/s4_bundle.sh

anchors:
	set -euo pipefail; ./scripts/anchor_integrity.sh

flame:
	set -euo pipefail; ./scripts/flamegraph_hotpaths.sh

micro:
	set -euo pipefail; ./scripts/microbench_dec.sh

dbt.docs:
	set -euo pipefail; dbt docs generate --project-dir analytics/dbt --profiles-dir analytics/dbt/profiles

rum.docs:
	set -euo pipefail; node fe/rum/collector_publish.js

nb.perf:
	set -euo pipefail; python3 notebooks/perf/dec_post_run_export.py
```

---

## 3) Pin de Ambiente e Supply‑Chain

Criar `scripts/env_pin_check.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
req() { command -v "$1" >/dev/null || { echo "Faltando: $1"; exit 2; }; }
req python3; req node; req jq; req git
python3 - <<'PY'
import pkgutil, sys
OK = True
# Versões mínimas exigidas
req = {
  'dbt-core': '1.8.6',
  'dbt-bigquery': '1.8.2',
  'semgrep': '1.80.0',
}
import importlib.metadata as md
for p,v in req.items():
    try:
        cur = md.version(p)
        print(f"{p}=={cur}")
    except md.PackageNotFoundError:
        print(f"Faltando pacote: {p}"); OK=False
sys.exit(0 if OK else 2)
PY
node -e "const v=require('fs').existsSync('package-lock.json'); if(!v){process.exit(2)}" || { echo 'package-lock.json ausente'; exit 2; }
[ -f requirements.lock ] || { echo 'requirements.lock ausente'; exit 2; }
[ -f Cargo.lock ] || { echo 'Cargo.lock ausente'; exit 2; }
echo 'ENV pin OK'
```

**Ação CI:** Docker do k6 com digest resolvido em runtime (sem placeholders) dentro do workflow, via `docker pull` + `docker inspect --format '{{index .RepoDigests 0}}'` e export de variável `K6_IMAGE`.

---

## 4) RUM → Prom (implementação completa)

Criar `fe/rum/collector.js` (no app web):

```js
import { onINP } from 'web-vitals/attribution';
function send(path, body){ navigator.sendBeacon(path, JSON.stringify(body)); }
onINP(({value, id}) => {
  const payload = { metric: 'INP', value: Math.round(value), id, page: location.pathname, ts: new Date().toISOString() };
  send('/rum/ingest', payload);
});
```

Criar `fe/rum/server.js` (ingest Prom):

```js
const http = require('http');
const client = require('prom-client');
const Registry = new client.Registry();
client.collectDefaultMetrics({ register: Registry });
const inp = new client.Gauge({ name: 'web_vitals_inp_ms', help: 'INP p/ página', labelNames: ['page','env']});
Registry.registerMetric(inp);
const ENV = process.env.ENV || 'stage';
const server = http.createServer((req,res)=>{
  if(req.method==='POST' && req.url==='/rum/ingest'){
    let data=''; req.on('data', c=>data+=c); req.on('end', ()=>{
      try{ const p=JSON.parse(data); inp.labels({page:p.page, env:ENV}).set(p.value); res.writeHead(204); res.end(); }
      catch(e){ res.writeHead(400); res.end('bad payload'); }
    }); return; }
  if(req.url==='/metrics'){ res.writeHead(200, {'Content-Type':'text/plain'}); res.end(Registry.metrics()); return; }
  res.writeHead(404); res.end();
});
server.listen(9314, '0.0.0.0', ()=>console.log('RUM ingest @9314'));
```

Export de snapshot no ORR permanece: `EVI/web_inp_snapshot.json` (fetch de `/metrics`).

---

## 5) Observabilidade — Regras adicionais

Criar `ops/prom/decision_gap.rules.yaml`:

```yaml
groups:
- name: decision_gap
  interval: 30s
  rules:
  - record: decision_gap_ratio:5m
    expr: (sum(increase(decision_events_total[5m])) > 0)
      * on() group_left() (1 - (sum(increase(decision_events_total[5m])) / sum(increase(trades_total[5m]))))
  - alert: DecisionGapHigh
    expr: decision_gap_ratio:5m > 0.2
    for: 10m
    labels: { severity: warn, owner: PLAT }
    annotations:
      summary: "Decision gap > 20% (5m)"
      runbook: "docs/runbooks/decision_gap.md"
```

Runbook novo `docs/runbooks/decision_gap.md` com checagens de hooks e backpressure do engine.

---

## 6) Perf Harness, Microbench & Flamegraphs

Manter `tests/perf/dec_120rps_60m.js`.
Criar `scripts/microbench_dec.sh` e `scripts/flamegraph_hotpaths.sh` (com quedas seguras):

```bash
# scripts/microbench_dec.sh
#!/usr/bin/env bash
set -euo pipefail
cargo bench -q -p engine --bench dec_paths -- --warm-up-time 5 --measurement-time 20 --sample-size 30 | tee out/s4_orr/logs/microbench.txt
```

```bash
# scripts/flamegraph_hotpaths.sh
#!/usr/bin/env bash
set -euo pipefail
if ! command -v flamegraph >/dev/null; then cargo install flamegraph >/dev/null 2>&1 || true; fi
if ! command -v sudo >/dev/null; then echo 'sem sudo: pulando flamegraph'; exit 0; fi
RUSTFLAGS='-g' sudo -E flamegraph -o out/s4_orr/evidence/dec_flame.svg -- target/release/engine_bin --scenario dec_hot || echo 'flamegraph skipped'
```

---

## 7) Âncora de Integridade (Merkle) + Tag Git

Criar `scripts/anchor_root.py`:

```python
#!/usr/bin/env python3
import hashlib, sys, json, os

def sha(p):
    h=hashlib.sha256();
    with open(p,'rb') as f:
        for chunk in iter(lambda: f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()

def merkle(hashes):
    cur=[bytes.fromhex(x) for x in hashes]
    if not cur: return hashlib.sha256(b'').hexdigest()
    while len(cur)>1:
        nxt=[]
        for i in range(0,len(cur),2):
            a=cur[i]; b=cur[i+1] if i+1<len(cur) else a
            nxt.append(hashlib.sha256(a+b).digest())
        cur=nxt
    return cur[0].hex()

files = sorted(sys.argv[1:])
leaf = [sha(p) for p in files]
root = merkle(leaf)
print(json.dumps({"root":root, "files":files, "leaf":leaf}, indent=2))
```

Criar `scripts/anchor_integrity.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
OUT="out/s4_orr"; EVI="$OUT/evidence"; mkdir -p "$OUT"
FILES=( "$EVI/dec_p95_5m.json" "$EVI/cdc_lag_p95_5m.json" "$EVI/web_inp_snapshot.json" docs/adr docs/spec schemas ops/prom )
LIST=()
for f in "${FILES[@]}"; do
  if [ -d "$f" ]; then while IFS= read -r -d '' x; do LIST+=("$x"); done < <(find "$f" -type f -print0); else LIST+=("$f"); fi
done
JSON=$(python3 scripts/anchor_root.py "${LIST[@]}")
ROOT=$(echo "$JSON" | jq -r .root)
echo "$JSON" > "$OUT/ANCHOR.json"
echo "$ROOT" > "$OUT/ANCHOR.txt"
TAG="anchor-M2-$ROOT"
if git rev-parse "$TAG" >/dev/null 2>&1; then echo "Tag já existe: $TAG"; else git tag -a "$TAG" -m "Evidence anchor M2"; fi
echo "ANCHOR_ROOT=$ROOT"
```

---

## 8) CI endurecido (concurrency, hardened runner, k6 pin)

Atualizar `.github/workflows/_s4-orr.yml` (trechos relevantes):

```yaml
name: _S4 ORR (Reusable)
on: { workflow_call: { inputs: { ref: { required: false, type: string } }, secrets: {} } }
permissions: { contents: read, actions: write }
concurrency: { group: s4-orr-${{ inputs.ref || github.sha }}, cancel-in-progress: true }
jobs:
  orr:
    runs-on: ubuntu-latest
    timeout-minutes: 90
    env: { PROM: http://127.0.0.1:9090 }
    steps:
      - uses: actions/checkout@v4
        with: { ref: ${{ inputs.ref || github.sha }} }
      - name: Harden Runner
        uses: step-security/harden-runner@v3
        with: { egress-policy: block }
      - uses: actions/setup-python@v5
        with: { python-version: '3.11' }
      - name: System deps
        run: sudo apt-get update && sudo apt-get install -y jq
      - name: Python deps (locked)
        run: pip install -r requirements.lock
      - name: Security tools
        run: |
          curl -sL https://github.com/aquasecurity/trivy/releases/download/v0.53.0/trivy_0.53.0_Linux-64bit.tar.gz | tar xz && sudo mv trivy /usr/local/bin/
          curl -sSL https://github.com/gitleaks/gitleaks/releases/download/v8.18.4/gitleaks_8.18.4_linux_x64.tar.gz | tar xz && sudo mv gitleaks /usr/local/bin/
          pip install semgrep==1.80.0
      - name: Resolve k6 image digest
        id: k6
        run: |
          IMG=grafana/k6:0.52.0
          docker pull "$IMG" >/dev/null
          DIG=$(docker inspect --format='{{index .RepoDigests 0}}' "$IMG")
          echo "image=$DIG" >> $GITHUB_OUTPUT
      - name: ORR (k6 via pinned image)
        env: { K6_IMAGE: ${{ steps.k6.outputs.image }} }
        run: |
          export K6="docker run --rm -i -v $PWD:/work -w /work $K6_IMAGE"
          sed -i '1s/^/export K6="'"$K6"'"\n/' scripts/orr_s4_run.sh
          bash scripts/orr_s4_run.sh
      - name: Upload bundle
        uses: actions/upload-artifact@v4
        with: { name: s4_evidence_bundle, path: out/s4_evidence_bundle_*.zip }
```

---

## 9) Runbooks (degrade/rollback precisos)

Atualizar `docs/runbooks/dec_slo.md` com limites: **pool DB=256**, **HTTP client=512**, **keep‑alive=on**, `upstream_timeout=450ms`, **jemalloc** ativo. Fluxo: confirmar `SLOBudgetBreach` por 10 min → aplicar `degrade` (cache de preço + recorte de features) → se p95>0,8s por 5 min, `rollback` → checar `dec:recovered:10m` → remover `degrade`.

Atualizar `docs/runbooks/cdc_lag.md` e `docs/runbooks/schema_registry.md` com comandos de diagnóstico e reversão de schema MINOR compatível.

---

## 10) Política CE$ SLO‑Aware (estável)

Se `error_budget_burn_rate ≥ 1×/4h` por 2 janelas: suspender rebates CE$ e aplicar **slow‑mode** no par afetado; retomar após 2 janelas verdes. Se `twap_divergence_percent > 1,0%`: congelar matching, acionar revisão de oráculo e anexar evidências ao bundle.

---

## 11) Evidence Pack (acréscimos v1.3)

Além do conteúdo v1.2, incluir: `docs/spec/invariants.md`, `docs/spec/tla/dec_pre_ga.tla`, `ops/prom/decision_gap.rules.yaml`, `out/s4_orr/ANCHOR.{json,txt}`, `notebooks/perf/dec_post_run.html`, `microbench.txt`, `dec_flame.svg`, print do digest da imagem k6 usada (`K6_IMAGE`).

---

## 12) Demo One‑Pager (para Review)

Criar `docs/demo/s4_prega_onepager.md`:

```md
# Demo S4 — Pre‑GA em 7 minutos
1) **One‑command**: `make prega` (mostra saída resumida: SLOs, SHA‑256, ANCHOR_ROOT, tag Git).
2) **Perf**: gráfico DEC p95 (5m) ≤ 0,8 s @ 120 rps (60 min) e 5xx=0.
3) **CDC**: lag p95 ≤ 120 s + runbook ok.
4) **Registry/CI**: drift=0, compat OK; diff de schema no bundle.
5) **dbt**: tests=pass; docs publicadas (artifact).
6) **RUM**: INP p75 ≤ 200 ms; série `web_vitals_inp_ms{page}`.
7) **Âncora**: raiz Merkle exibida; tag `anchor-M2-<root>` no repositório.
```

---

## 13) Gate Pre‑GA (M2) — Checklist Final

Perf (`dec:p95_seconds:5m ≤ 0,8` por 60 min @ 120 rps; 5xx=0; `dec:recovered:10m` OK) • Dados/CDC (dbt pass; `schema_drift=0`; `contract_break=false`; `cdc:lag_p95 ≤ 120`) • Governança (Hook ≥ 98%, Audit ≥ 99%) • ADRs 001–003 publicados e ancorados • Segurança (0 críticos) • Change (Pre‑GA Plan) • **Âncora (ANCHOR_ROOT + tag)** • Assinaturas: PO, Eng (ST), Data (DC), SRE, FE, SEC/RSK, INT.

---

## 14) Ação imediata (v1.3)

1. Commitar arquivos novos/atualizados desta versão.
2. Rodar `make prega`.
3. Publicar Evidence Pack + SHA‑256 + ANCHOR_ROOT e coletar assinaturas do Gate M2.
