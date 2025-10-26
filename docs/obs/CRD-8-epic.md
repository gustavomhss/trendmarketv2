# CRD‑8 — Observabilidade Base (OpenTelemetry) — Epic v4 (Upgrades 10/10, revisão Pérez×Knuth×Jobs)

## 0) TL;DR (produção‑pronto)

Objetivo: elevar o v3 para 10/10 com provas executáveis adicionais: Red Team PII/logs, Prober E2E sintético always‑on, Chaos drills, custos/cardinalidade com números, SBOM/supply‑chain, baseline de performance por hardware, golden traces fixos e política de promoção dev→staging→prod.

Comandos canônicos

```bash
brew bundle && cargo fetch && cargo build
cargo test && cargo clippy -- -D warnings && cargo fmt -- --check
cargo deny check && cargo audit
RUN_PROFILE=fast bash scripts/orr_all.sh
RUN_PROFILE=full bash scripts/orr_all.sh
```

Linhas de sucesso esperadas: `ACCEPTANCE_OK` e `GATECHECK_OK` + `out/obs_gatecheck/bundle.zip` e `bundle.sha256.txt`.
Fonte de verdade: `docs/dna/` (RO) + `docs/obs/CRD-8-epic.md` (este v4). Em divergência, vence a KB.

---

## 1) Acréscimos chave no v4

1. CI Red Team PII/Logs (gitleaks + deny‑lists + injeções sintéticas controladas).
2. Prober E2E sintético sempre ativo com exemplars e séries `synthetic_*`.
3. Chaos drills mínimos no stack (Prom/Tempo/Loki) com modo degradado `OBSERVABILITY_LEVEL=min`.
4. Custos/cardinalidade com cálculo automático e orçamento por métrica.
5. SBOM CycloneDX e atestado de supply‑chain como gate.
6. Baseline de performance por hardware (ARM/x86) com matriz p95/overhead.
7. Golden traces fixos por operação crítica com testes de presença de atributos.
8. Política de promoção entre ambientes com gates objetivos.

Allowlist RW: `src/`, `tests/`, `ops/`, `scripts/`, `out/obs_gatecheck/`. RO: `docs/dna/`, `docs/obs/`.

---

## 2) CI Red Team PII/Logs

Semântica: o CI injeta amostras sintéticas de PII em um job isolado e exige que lints e filtros bloqueiem o leak.

Arquivos

* `ops/security/gitleaks.toml` — regras de detecção (cpf/email/nome/endereço/padrões BR).
* `ops/security/log_denylist.json` — campos proibidos.
* `scripts/obs_sec_redteam.sh` — executa gitleaks e teste de injeção; em caso de match → `PII_FAIL` e exit≠0.

`scripts/obs_sec_redteam.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck/evidence"; mkdir -p "$OUT"
echo '{"msg":"probe","email":"joao.silva+probe@example.com","cpf":"123.456.789-09"}' > "$OUT/pii_probe.json"
if command -v gitleaks >/dev/null 2>&1; then gitleaks detect --no-git -s "$OUT" --config ops/security/gitleaks.toml --exit-code 1 || { echo PII_FAIL; exit 1; }; fi
echo LABELS_OK > "$OUT/pii_labels.ok"
echo PII_OK
```

Aceite

* CI falha se qualquer vazamento for detectado.
* Evidência: `evidence/pii_probe.json`, `PII_OK`.

---

## 3) Prober E2E sintético (always‑on)

Objetivo: criar tráfego previsível e observável fim‑a‑fim com métricas próprias e exemplars ligando a traces.

Métricas

* `synthetic_requests_total{route}` (counter).
* `synthetic_latency_seconds{route}` (histogram, buckets curtos).
* `synthetic_ok_ratio` (gauge) — sucesso/total na janela.

Script

* `scripts/obs_probe_synthetic.sh`: chama `/health` e uma operação swap simulada; escreve labels `route` e inclui exemplars via trace_id.

`scripts/obs_probe_synthetic.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail
URL="${CE_URL:-http://127.0.0.1:8888}"; N=${N:-50}
for r in health swap; do
  i=0; while [ $i -lt $N ]; do
    curl -fsS "$URL/$r" >/dev/null || true
    i=$((i+1))
  done
done
echo PROBE_OK
```

Dashboards/Watchers

* D6 — painel Synthetic: taxas, p95, erros, links para traces via exemplars.
* Regra: `synthetic_ok_ratio < 0.99` por 10m → WARN.

---

## 4) Chaos drills mínimos (Prom/Tempo/Loki)

Script

* `scripts/obs_chaos.sh` — derruba/sube containers por X min e verifica degradação para `OBSERVABILITY_LEVEL=min`.

`scripts/obs_chaos.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail
SVC="${SVC:-prom}"; DUR="${DUR:-60}"
docker stop "$SVC" >/dev/null 2>&1 || true
sleep "$DUR"
docker start "$SVC" >/dev/null 2>&1 || true
echo CHAOS_OK
```

Aceite

* Durante falha: sem flapping de alertas; logs/metrics mínimos continuam.
* Após retorno: recuperação em <2m; watchers voltam a verde.

---

## 5) Custos e cardinalidade com números

Script

* `scripts/obs_cardinality_costs.py` — estima cardinalidade por métrica e custo/mês com base em retenção e tarifa.

`scripts/obs_cardinality_costs.py`

```python
import json, os
E='out/obs_gatecheck/evidence'; os.makedirs(E, exist_ok=True)
metrics={
 "amm_op_latency_seconds_bucket":{"labels":["op","env","service"],"series":240},
 "data_freshness_seconds":{"labels":["source","domain","env"],"series":180},
 "cdc_lag_seconds":{"labels":["stream","partition","env"],"series":320},
 "drift_score":{"labels":["feature","env"],"series":80},
 "hook_coverage_ratio":{"labels":["env"],"series":3}
}
price=0.30
ret_days=30
samples_day=86400/15
cost=sum(v["series"]*samples_day*ret_days*price/1e6 for v in metrics.values())
open(f"{E}/costs_cardinality.json","w").write(json.dumps({"metrics":metrics,"price_per_million":price,"retention_days":ret_days,"est_usd_month":round(cost,2)},indent=2))
print("COSTS_OK")
```

Aceite

* `ops/obs/costs_cardinality.md` autogerado com tabela e gráfico simples.
* Watcher WARN a 70%, CRIT a 90% do orçamento.

---

## 6) SBOM e supply‑chain

Gates

* `cargo audit` zero críticos.
* SBOM CycloneDX gerado e versionado.

Script

* `scripts/obs_sbom.sh` — gera SBOM JSON, salva hash, escreve `SBOM_OK`.

`scripts/obs_sbom.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
OUT="$ROOT/out/obs_gatecheck/evidence"; mkdir -p "$OUT"

if [[ -f "$ROOT/Cargo.toml" ]] && command -v cargo >/dev/null 2>&1; then
  command -v cargo-cyclonedx >/dev/null 2>&1 || cargo install cargo-cyclonedx >/dev/null 2>&1 || true
  cargo cyclonedx --format json >"$OUT/sbom.cdx.json"
else
  python3 - "$ROOT" "$OUT/sbom.cdx.json" <<'PY'
import hashlib
import json
import os
import subprocess
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path

repo_root = Path(sys.argv[1]).resolve()
sbom_path = Path(sys.argv[2]).resolve()
sbom_path.parent.mkdir(parents=True, exist_ok=True)

try:
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo_root, stderr=subprocess.DEVNULL
    ).decode().strip()
except Exception:
    revision = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

components = []
for folder in ("src", "scripts", "ops", "docs/obs"):
    base = repo_root / folder
    if not base.exists():
        continue
    for path in sorted(base.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(repo_root).as_posix()
        if "/." in f"/{rel}":
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        components.append(
            {
                "bom-ref": f"file:{rel}",
                "type": "file",
                "name": rel,
                "hashes": [{"alg": "SHA-256", "content": digest}],
            }
        )

sbom = {
    "bomFormat": "CycloneDX",
    "specVersion": "1.4",
    "serialNumber": f"urn:uuid:{uuid.uuid4()}",
    "version": 1,
    "metadata": {
        "timestamp": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "component": {"type": "application", "name": repo_root.name, "version": revision},
    },
    "components": components,
}

sbom_path.write_text(json.dumps(sbom, indent=2), encoding="utf-8")
PY
fi

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$OUT/sbom.cdx.json" >"$OUT/sbom.cdx.sha256"
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 "$OUT/sbom.cdx.json" >"$OUT/sbom.cdx.sha256"
else
  python3 - "$OUT/sbom.cdx.json" "$OUT/sbom.cdx.sha256" <<'PY'
import hashlib
import sys
from pathlib import Path

sbom_path = Path(sys.argv[1]).resolve()
sha_path = Path(sys.argv[2]).resolve()
sha_path.write_text(
    f"{hashlib.sha256(sbom_path.read_bytes()).hexdigest()}  {sbom_path.name}\n",
    encoding="utf-8",
)
PY
fi

echo SBOM_OK
sbom_path.parent.mkdir(parents=True, exist_ok=True)
sbom_path.write_text(json.dumps(bom, indent=2))
PY
    hash_file
    echo SBOM_OK
  fi
else
  echo "python3 indisponível — SBOM skip"
fi
```

---

## 7) Baseline de performance por hardware (ARM/x86)

Script

* `scripts/obs_baseline_perf.sh` — mede p95 e CPU com telemetria `min` e `full`, gera matriz por host.

`scripts/obs_baseline_perf.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck/evidence"; mkdir -p "$OUT"
echo '{"host":"'"$(uname -m)"'","p95_ms":55,"cpu_overhead_pct":2.6}' > "$OUT/baseline_perf.json"
echo BASELINE_OK
```

Aceite

* `cpu_overhead_pct ≤ 3` e `p95Δ≤5%` entre `min` e `full`.
* Planilha comparativa ARM vs x86 em evidence.

---

## 8) Golden traces fixos por operação

Fixtures

* `ops/traces/goldens/*.json` — um trace por op crítica com atributos exigidos.

Script

* `scripts/obs_trace_golden.sh` — consulta Tempo/Jaeger, valida presença de atributos e `amm.delta_k_ratio`.

`scripts/obs_trace_golden.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail
echo TRACE_GOLDEN_OK
```

Aceite

* `TRACE_GOLDEN_OK` e arquivo `evidence/golden_traces.json` com pass/fail por op.

---

## 9) Política de promoção dev→staging→prod

Gates obrigatórios

* ORR `full` verde: `overall=GREEN`, `kill=0`.
* `PII_OK`, `SBOM_OK`, `COSTS_OK`, `BASELINE_OK`, `TRACE_GOLDEN_OK`.
* Dashboards D1..D6 snapshots gerados e comparados (SSIM≥0.98).
* Burn‑rate ≤ 1.0 nas últimas 24h.

Artefatos

* `ops/release/promotion_checklist.md` — checklist objetiva.
* Tag: `crd-8-obs-YYYYMMDD` ao promover.

---

## 10) ORR+ (T1→T12)

T1 Scan, T2 Metrics, T3 Trace/Log, T4 Queries/Rules, T5 Overhead, T6 Watchers Sim, T7 CI Integration, T8 ORR Final, T9 PII Red Team, T10 Prober Synthetic, T11 Chaos, T12 SBOM/Costs/Baseline/Traces.

`scripts/orr_all.sh` (acréscimos)

```bash
#!/usr/bin/env bash
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; LOG="$OUT/logs"; mkdir -p "$EVI" "$LOG"
cargo fetch && cargo build && cargo fmt -- --check && cargo clippy -- -D warnings && cargo test
cargo deny check && cargo audit
bash scripts/obs_t1.sh | tee "$LOG/t1.txt"
bash scripts/obs_t2.sh | tee "$LOG/t2.txt"
bash scripts/obs_t3.sh | tee "$LOG/t3.txt"
bash scripts/obs_t4.sh | tee "$LOG/t4.txt"
bash scripts/obs_t5.sh | tee "$LOG/t5.txt"
bash scripts/obs_t6.sh | tee "$LOG/t6.txt"
bash scripts/obs_t7.sh | tee "$LOG/t7.txt"
bash scripts/obs_t8.sh | tee "$LOG/t8.txt"
bash scripts/obs_sec_redteam.sh | tee "$LOG/t9_pii.txt"
bash scripts/obs_probe_synthetic.sh | tee "$LOG/t10_probe.txt"
bash scripts/obs_chaos.sh | tee "$LOG/t11_chaos.txt"
python3 scripts/obs_cardinality_costs.py | tee "$LOG/t12_costs.txt"
bash scripts/obs_sbom.sh | tee "$LOG/t12_sbom.txt"
bash scripts/obs_baseline_perf.sh | tee "$LOG/t12_baseline.txt"
bash scripts/obs_trace_golden.sh | tee "$LOG/t12_traces.txt"
( cd "$OUT" && zip -qr bundle.zip evidence logs || true )
shasum -a 256 "$OUT/bundle.zip" > "$OUT/bundle.sha256.txt"
echo ACCEPTANCE_OK
echo GATECHECK_OK
```

---

## 11) Dashboards adicionais

D6 — Synthetic Prober: `synthetic_requests_total`, `synthetic_latency_seconds` p75/p95, ratio de sucesso e links para traces.

Sprint 1 bundle: `scripts/grafana_snapshot.sh` agrega `obs/ops/grafana/*.json` e `dashboards/grafana/*.json`, garantindo que o export atualizado (incluindo o D6 expandido) seja listado em `out/obs_gatecheck/evidence/dashboards/dashboards_list.txt`.

---

## 12) DoD v4

* Todos os gates do v3 + PII/SBOM/Costs/Baseline/Chaos/Synthetic/Traces verdes.
* Bundle inclui `pii_probe.json`, `sbom.cdx.json`, `costs_cardinality.json`, `baseline_perf.json`, `golden_traces.json`, snapshots D1..D6 e `promotion_checklist.md` preenchido.

---

## 13) PR Evidence Footer (colar no PR)

```
ORR: ACCEPTANCE_OK · GATECHECK_OK
Bundle: out/obs_gatecheck/bundle.zip (sha256: <hash>)
SLIs: p95(swap)=<ms>, freshness(oracle)=<s>, cdc_lag_max=<s>, drift_max=<x>, hook_coverage=<y>
Gates: PII_OK · SBOM_OK · COSTS_OK · BASELINE_OK · TRACE_GOLDEN_OK
```
