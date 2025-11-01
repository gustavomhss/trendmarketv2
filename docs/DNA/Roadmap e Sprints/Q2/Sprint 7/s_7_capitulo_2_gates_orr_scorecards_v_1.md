# Sprint Q2 — S7 (Stabilize)
## Capítulo 2 — GATES ORR & Scorecards (Blueprint para o Codex)
Versão: v4 (2025-10-31)  
Owner: PO • Eng: Codex • ORR: SRE  
Escopo: somente Cap.2. Cap.1 está **travado** (v7.1 FINAL). Cap.3 (Filemap) virá após sua aprovação deste capítulo.

Changelog v4 (revisão final com micro‑patches):
- **T0_ruleset_sanity** adicionado (fecha o loop): valida via **GitHub API/gh** se o ruleset ativo exige **exatamente** os 8 checks (agora 9, com T0) por **contexto**.
- **Schemas JSON com `$id` e `version`** (scorecard, MANIFEST e T0..T7) publicados em `/schemas/v1/*.schema.json` e validados no CI.
- **ZIP reprodutível endurecido**: compressão **DEFLATE nível fixo 6**, `SOURCE_DATE_EPOCH=0`, ordem lexicográfica, sem *extra fields*; teste que recalcula sha256 de **cada entrada** do ZIP e confere com `MANIFEST.json`.
- **Scorecard enriquecido**: `warnings_by_gate` e `waivers_by_gate` (por gate) + campo `gating` com `hard_fail` e `warn_count`.
- **Pins (T3) anti‑spoof**: verificação por API de que cada SHA pertence ao **repositório/owner esperado** (novo EXIT 32).

---

### 0) Normas de redação (Playbook + RFC‑2119)
Termos **MUST/SHOULD/MAY** são normativos. Este capítulo define **o que mede e bloqueia merge**; não redefine entregáveis do Cap.1.

---

### 1) North Star dos GATES
Garantir que a S7 seja **determinística, segura e auditável** com **regras objetivas de aprovação** (merge‑blocking) e **evidências reprodutíveis**.

---

### 2) Integração GitHub — Checks obrigatórios (normativo)
**Nomes de jobs (estáveis)** → **MUST** ser exatamente: `t0_ruleset_sanity`, `t1_yaml`, `t2_security`, `t3_pins`, `t4_tests`, `t5_props`, `t6_determinism`, `t7_append_only`, `t8_pack`.

**Workflow reutilizável:** `.github/workflows/_s7-orr.yml`  
**Wrapper:** `.github/workflows/s7-exec.yml`

**Branch Protection/Rulesets (UI):**
- **MUST** habilitar *Require status checks to pass* para `main`/`release/*` e **listar os 9 checks** acima (inclui T0).
- **MUST** habilitar *Require a pull request before merging* + *Require approvals* (≥1) + *Dismiss stale reviews*.
- **SHOULD** bloquear *Force pushes* e *Bypass* exceto admins.

**2.1) Branch Protection via CLI (gh api) — exemplo**
Crie `ruleset_s7.json` com (resumo):
```json
{
  "name": "S7 Required Checks",
  "target": "branch",
  "enforcement": "active",
  "conditions": {"ref_name": {"include": ["main","release/*"]}},
  "rules": [
    {"type": "required_status_checks", "parameters": {"strict_required_status_checks": true,
      "required_status_checks": [
        {"context": "S7 ORR Exec / t0_ruleset_sanity"},
        {"context": "S7 ORR Exec / t1_yaml"},
        {"context": "S7 ORR Exec / t2_security"},
        {"context": "S7 ORR Exec / t3_pins"},
        {"context": "S7 ORR Exec / t4_tests"},
        {"context": "S7 ORR Exec / t5_props"},
        {"context": "S7 ORR Exec / t6_determinism"},
        {"context": "S7 ORR Exec / t7_append_only"},
        {"context": "S7 ORR Exec / t8_pack"}
      ]}}
  ]
}
```
Aplicar:
```
OWNER=youruser REPO=trendmarketv2
gh api -X POST repos/$OWNER/$REPO/rulesets --input ruleset_s7.json
# atualizar: gh api -X PUT repos/$OWNER/$REPO/rulesets/{id} --input ruleset_s7.json
```

---

### 3) Ambiente CI (normativo)
- Runner: `ubuntu-22.04`  
- Env: `TZ=UTC LC_ALL=C LANG=C.UTF-8 PYTHONUTF8=1 SOURCE_DATE_EPOCH=0`  
- **Matrix Python (determinismo multi‑ambiente):** `3.11.14` e `3.11.9`.
- Timeouts sugeridos: `t0:2m, t1:2m, t2:5m, t3:2m, t4:10m, t5:12m, t6:5m, t7:3m, t8:3m`.  
- Retenção de artefatos: **≥ 7 dias** (`s7-orr-evidence`).

---

### 4) Gating por SLO (normativo)
- Cada gate T* **mede** `duration_ms`.  
- **FAIL (merge‑blocking)** se `duration_ms > Hard`.  
- **WARN** se `Warn < duration_ms ≤ Hard` → registrar em `scorecard.warnings_by_gate[Ti]` e **opcionalmente** exigir *waiver*; 3 WARNs consecutivos no mesmo gate **devem** abrir issue de performance.

---

## T0 — Ruleset Sanity (fecha o loop)
**Explicação simples:** garante que o **ruleset ativo** realmente exige os 9 checks (inclui T0).  
**Como funciona:** usa **gh api** para listar rulesets ativos do repo; encontra a regra de `required_status_checks` e verifica a presença **exata** dos contextos "S7 ORR Exec / tX_*".  
**Finalidade:** evita drift manual na UI quebrar o gating.  
**Entradas/Saídas:** rulesets → `out/evidence/T0_ruleset_sanity/ruleset_check.json`.  
**Comandos:** `python -m scripts.ci.ruleset_sanity --out out/evidence/T0_ruleset_sanity/ruleset_check.json` (usa `gh` sob o capô).  
**Critérios:** `ok=true` e lista de contexts **cobre exatamente** os 9 checks.  
**Evidências:** `ruleset_check.json` (schema abaixo).  
**EXIT:** `01 ruleset_missing`, `02 checks_missing`, `03 api_error`.  
**SLO Warn/Hard:** 3s / 10s.  
**Schema (T0):**
```json
{
  "$id": "https://trendmarket/schemas/v1/t0_ruleset_sanity.schema.json",
  "version": "1.0.0",
  "type": "object",
  "required": ["ok","required_contexts","missing","extra","duration_ms"],
  "properties": {
    "ok": {"type":"boolean"},
    "required_contexts": {"type":"array","items":{"type":"string"}},
    "missing": {"type":"array","items":{"type":"string"}},
    "extra": {"type":"array","items":{"type":"string"}},
    "duration_ms": {"type":"integer","minimum":0}
  },
  "additionalProperties": false
}
```

---

## T1 — YAML & Repo Hygiene
**Critérios:** exit=0; estrutura MUST existir; SLO 5s / 15s; negativo: tabulação → `yaml_invalid`.  
**Evidências:** `T1_yaml/{yamllint_report.txt,repo_structure.json}`.  
**EXIT:** `10 yaml_invalid`, `11 structure_missing`.  
**Schema (T1):**
```json
{"$id":"https://trendmarket/schemas/v1/t1_yaml.schema.json","version":"1.0.0","type":"object","required":["ok","issues","duration_ms"],"properties":{"ok":{"type":"boolean"},"issues":{"type":"integer"},"duration_ms":{"type":"integer","minimum":0}},"additionalProperties":false}
```

---

## T2 — Segurança (Gitleaks)
**Critérios:** zero HIGH/CRIT; LOW/MED apenas via allowlist em fixtures; SLO 20s / 60s; negativo: chave fora de fixtures → `secrets_found`.  
**Evidências:** `T2_security/gitleaks_report.json`.  
**EXIT:** `20 secrets_found`, `21 allowlist_missing`.  
**Schema (T2):**
```json
{"$id":"https://trendmarket/schemas/v1/t2_security.schema.json","version":"1.0.0","type":"object","required":["ok","findings_total","high","critical"],"properties":{"ok":{"type":"boolean"},"findings_total":{"type":"integer"},"high":{"type":"integer"},"critical":{"type":"integer"}},"additionalProperties":false}
```

---

## T3 — Pins de Dependências (Actions & Tools)
**Critérios:** 100% pinado por SHA; `pins_report.json.ok=true`; **anti‑spoof** via API: para cada `owner/repo@sha`, checar `GET /repos/{owner}/{repo}/commits/{sha}` **ok**; SLO 5s / 15s; negativo: `@v4` sem SHA → `pin_mismatch`.  
**Evidências:** `T3_pins/{actions.lock,pins_report.json,sha_origin_report.json}`.  
**EXIT:** `30 pins_missing`, `31 pin_mismatch`, `32 sha_owner_mismatch`.  
**Schema (T3):**
```json
{"$id":"https://trendmarket/schemas/v1/t3_pins.schema.json","version":"1.0.0","type":"object","required":["ok","unpinned","drift","spoof_alerts"],"properties":{"ok":{"type":"boolean"},"unpinned":{"type":"integer"},"drift":{"type":"integer"},"spoof_alerts":{"type":"integer"}},"additionalProperties":false}
```

---

## T4 — Testes Funcionais (pytest)
**Critérios:** 100% verde; constantes presentes; negativos: domain_tag sem `
` e assinatura Base64 inválida → `EXIT 51`; SLO 60s / 120s.  
**Evidências:** `T4_tests/pytest_report.json`, `verify.json`.  
**EXIT:** `40 tests_failed`, `41 missing_constant`.  
**Schema (T4):**
```json
{"$id":"https://trendmarket/schemas/v1/t4_tests.schema.json","version":"1.0.0","type":"object","required":["ok","tests","passed","failed"],"properties":{"ok":{"type":"boolean"},"tests":{"type":"integer"},"passed":{"type":"integer"},"failed":{"type":"integer"}},"additionalProperties":false}
```

---

## T5 — Propriedades & Invariantes
**Critérios:** todas as propriedades true; negativo: embaralhar ordem mantendo hash → falha; SLO 90s / 180s.  
**Evidências:** `T5_props/properties_summary.json`.  
**EXIT:** `50 property_failed`.  
**Schema (T5):**
```json
{"$id":"https://trendmarket/schemas/v1/t5_props.schema.json","version":"1.0.0","type":"object","required":["ok","properties"],"properties":{"ok":{"type":"boolean"},"properties":{"type":"array","items":{"type":"object","required":["name","result"],"properties":{"name":{"type":"string"},"result":{"type":"boolean"},"counterexample":{"type":"object"}}}}},"additionalProperties":false}
```

---

## T6 — Determinismo & Reprodutibilidade (multi‑ambiente)
**Critérios:** igualdade byte‑a‑byte; hashes esperados (Cap.1 §9); **ZIP idêntico** entre execuções/versões Python; SLO 20s / 60s; negativo: newline final → `determinism_mismatch`.  
**Evidências:** `T6_determinism/{compare.json,hash_match.json,zip_compare.json}`.  
**EXIT:** `60 determinism_mismatch`, `61 hash_unexpected`.  
**Schema (T6):**
```json
{"$id":"https://trendmarket/schemas/v1/t6_determinism.schema.json","version":"1.0.0","type":"object","required":["ok","byte_equal","zip_equal","hash_match"],"properties":{"ok":{"type":"boolean"},"byte_equal":{"type":"boolean"},"zip_equal":{"type":"boolean"},"hash_match":{"type":"boolean"}},"additionalProperties":false}
```

---

## T7 — Append‑Only Guard
**Critérios:** `ok=true`; negativos: `prev_root` divergente (62), **reorder**/`created_at` regressivo (63); SLO 5s / 15s.  
**Evidências:** `T7_append_only/append_only_report.json`.  
**EXIT:** `62 prev_root_mismatch`, `63 reorder_detected`.  
**Schema (T7):**
```json
{"$id":"https://trendmarket/schemas/v1/t7_append_only.schema.json","version":"1.0.0","type":"object","required":["ok","violations","details"],"properties":{"ok":{"type":"boolean"},"violations":{"type":"integer"},"details":{"type":"array","items":{"type":"object"}}},"additionalProperties":false}
```

---

## T8 — Empacotamento & Scorecard (ZIP reprodutível)
**ZIP reprodutível (normativo):** arquivos em **ordem lexicográfica**, timestamps fixos (`SOURCE_DATE_EPOCH`), compressão **DEFLATE nível 6** (`zipfile.ZIP_DEFLATED`, `compresslevel=6`), sem *extra fields*; `MANIFEST.json` MUST listar `{path,size,sha256}` de **cada** entrada.  
**Verificação:** `scripts.evidence.verify_manifest` recalcula sha256 de **todas** as entradas do ZIP e confere com `MANIFEST.json` (FAIL se divergir).  
**Critérios:** ZIP presente; `MANIFEST.json` e `scorecards/s7.json` válidos no schema; SLO 10s / 30s.  
**Evidências:** `s7-evidence.zip`, `MANIFEST.json`, `out/scorecards/s7.json`.  
**EXIT:** `80 evidence_missing`, `81 duplicate_artifact`, `82 scorecard_invalid`.  
**Schema (MANIFEST):**
```json
{"$id":"https://trendmarket/schemas/v1/manifest.schema.json","version":"1.0.0","type":"object","required":["version","generated_at","entries"],"properties":{"version":{"type":"integer","const":1},"generated_at":{"type":"string","format":"date-time"},"entries":{"type":"array","items":{"type":"object","required":["path","size","sha256"],"properties":{"path":{"type":"string"},"size":{"type":"integer","minimum":0},"sha256":{"type":"string","pattern":"^[a-f0-9]{64}$"}}}}},"additionalProperties":false}
```

---

## Scorecards — Schema v1 (normativo) & Gating por SLO
**Schema v1 (atualizado):**
```json
{
  "$id": "https://trendmarket/schemas/v1/scorecard.schema.json",
  "version": "1.0.0",
  "type": "object",
  "required": ["sprint","commit_sha","started_at","finished_at","gates","hashes","slo_p95_ms","gating"],
  "properties": {
    "sprint": {"type":"string","const":"Q2-S7"},
    "commit_sha": {"type":"string","pattern":"^[a-f0-9]{40}$"},
    "started_at": {"type":"string","format":"date-time"},
    "finished_at": {"type":"string","format":"date-time"},
    "gates": {"type":"object","required":["T0","T1","T2","T3","T4","T5","T6","T7","T8"]},
    "hashes": {"type":"object","required":["entries_hash","root","batch_sha256","evidence_zip"]},
    "slo_p95_ms": {"type":"object","required":["normalize","build_batch","merkle","sign","verify","append_guard","pack","total"]},
    "warnings_by_gate": {"type":"object","additionalProperties":{"type":"integer","minimum":0}},
    "waivers_by_gate": {"type":"object","additionalProperties":{"type":"array","items":{"type":"string"}}},
    "slo_violations": {"type":"array","items":{"type":"string"}},
    "gating": {"type":"object","required":["hard_fail","warn_count"],"properties": {"hard_fail": {"type":"boolean"}, "warn_count": {"type":"integer","minimum":0}}}
  },
  "additionalProperties": false
}
```
**Regra de aprovação (normativa):**
- **FAIL** se algum gate `status=fail` **ou** `gating.hard_fail=true` (estouro SLO Hard).  
- **PASS com WARN** se `warn_count>0` (estouro Warn), com rastreio em `warnings_by_gate` e *waivers* opcionais em `waivers_by_gate`.

---

## 4.x) Matriz CI & Convergência
**Matrix mínima:** `os:[ubuntu-22.04]`, `python:[3.11.14,3.11.9]`.  
**Estratégia:** `needs` encadeia T0→T1..T7→T8; falha em qualquer T* **cancela** T8.  
**Publicação artefatos:** `actions/upload-artifact@<sha>` nome `s7-orr-evidence` com `out/**`.  
**Nomes de checks:** devem corresponder **exatamente** aos jobs (ver §2), para Branch Protection reconhecer.

---

## Skeleton CI (normativo — nomes estáveis)
```yaml
name: "S7 ORR Exec"
on: { workflow_dispatch: {} }
jobs:
  t0_ruleset_sanity:
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: python -m scripts.ci.ruleset_sanity --out out/evidence/T0_ruleset_sanity/ruleset_check.json
  t1_yaml:
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: yamllint .
  t2_security:
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: gitleaks detect --source . --no-banner --report-format json --report-path out/evidence/T2_security/gitleaks_report.json
  t3_pins:
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: |
          python -m scripts.ci.generate_actions_lock > actions.lock
          python -m scripts.ci.validate_actions_lock --lock actions.lock --out out/evidence/T3_pins/pins_report.json
          python -m scripts.ci.verify_action_commit_owners --workflows .github/workflows --out out/evidence/T3_pins/sha_origin_report.json
  t4_tests:
    runs-on: ubuntu-22.04
    strategy: { matrix: { python-version: ["3.11.14","3.11.9"] } }
    steps:
      - uses: actions/checkout@<sha>
      - uses: actions/setup-python@<sha>
        with: { python-version: ${{ matrix.python-version }} }
      - run: pytest -q tests/test_normalizer.py tests/test_merkle.py tests/test_signature.py --json-report --json-report-file=out/evidence/T4_tests/pytest_report.json
  t5_props:
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: pytest -q tests/test_properties.py --json-report --json-report-file=out/evidence/T5_props/properties_summary.json
  t6_determinism:
    runs-on: ubuntu-22.04
    strategy: { matrix: { python-version: ["3.11.14","3.11.9"] } }
    steps:
      - uses: actions/checkout@<sha>
      - uses: actions/setup-python@<sha>
        with: { python-version: ${{ matrix.python-version }} }
      - run: python -m scripts.det.check_determinism --out out/evidence/T6_determinism/compare.json
  t7_append_only:
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: python -m scripts.merkle.append_only_guard --log data/log/log.jsonl --out out/evidence/T7_append_only/append_only_report.json
  t8_pack:
    needs: [t0_ruleset_sanity,t1_yaml,t2_security,t3_pins,t4_tests,t5_props,t6_determinism,t7_append_only]
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@<sha>
      - run: |
          python -m scripts.scorecard.write --out out/scorecards/s7.json
          python -m scripts.evidence.manifest --root out/ --out out/MANIFEST.json
          python -m scripts.evidence.pack --out out/s7-evidence.zip --reproducible --manifest out/MANIFEST.json --compression deflate --level 6
          python -m scripts.evidence.verify_manifest --zip out/s7-evidence.zip --manifest out/MANIFEST.json
      - uses: actions/upload-artifact@<sha>
        with: { name: s7-orr-evidence, path: out/ }
```

---

## Publicação de Schemas (normativo)
Todos os schemas deste capítulo **MUST** residir em `/schemas/v1/` no repo e serem validados em CI:
- `t0_ruleset_sanity.schema.json` … `t7_append_only.schema.json`  
- `manifest.schema.json`  
- `scorecard.schema.json`
> Cada schema inclui `$id` em `https://trendmarket/schemas/v1/<nome>.schema.json` e `version` SemVer (`1.0.0`).

---

## Política de *Waivers* (exceções)
(inalterada) — ver Cap.2 v3; agora com rastreio fino via `waivers_by_gate` no scorecard.

---

## Tabela‑resumo (merge‑blocking)
| Gate | Descrição | Aprovação (MUST) | Evidências | SLO Warn/Hard |
|---|---|---|---|---|
| T0 | Ruleset Sanity | contexts **exatos** presentes | `T0_ruleset_sanity/*` | 3s / 10s |
| T1 | YAML & Repo | yamllint=0; estrutura OK | `T1_yaml/*` | 5s / 15s |
| T2 | Segurança | Sem HIGH/CRIT; fixtures allowlisted | `T2_security/*` | 20s / 60s |
| T3 | Pins | 100% por SHA; lock válido; **anti‑spoof OK** | `T3_pins/*` | 5s / 15s |
| T4 | Testes | 100% verde; constantes presentes | `T4_tests/*` | 60s / 120s |
| T5 | Propriedades | Todas verdadeiras | `T5_props/*` | 90s / 180s |
| T6 | Determinismo | Bytes/hashes/ZIP idênticos & esperados | `T6_determinism/*` | 20s / 60s |
| T7 | Append‑only | `ok=true`; negativos falham | `T7_append_only/*` | 5s / 15s |
| T8 | Evidence/Score | ZIP+MANIFEST+scorecard válidos | `s7-evidence.zip`, `MANIFEST.json`, `scorecards/s7.json` | 10s / 30s |

---

## Runbook Local (dev)
```
bin/preflight
pytest -q tests/test_* --json-report --json-report-file=out/evidence/T4_tests/pytest_report.json
python -m scripts.det.check_determinism --out out/evidence/T6_determinism/compare.json
python -m scripts.merkle.append_only_guard --log data/log/log.jsonl --out out/evidence/T7_append_only/append_only_report.json
python -m scripts.evidence.manifest --root out/ --out out/MANIFEST.json
python -m scripts.evidence.pack --out out/s7-evidence.zip --reproducible --manifest out/MANIFEST.json --compression deflate --level 6
python -m scripts.evidence.verify_manifest --zip out/s7-evidence.zip --manifest out/MANIFEST.json
```

---

## Critérios de Aceite (DoD do Cap.2)
- **GATES T0..T8** com critérios **objetivos** e **merge‑blocking** (checks obrigatórios e nomes estáveis).  
- **Gating por SLO** documentado e aplicado no scorecard (inclui `warnings_by_gate`/`waivers_by_gate`).  
- **Schemas JSON** normativos com `$id`/`version` para scorecard, MANIFEST e T0..T7.  
- **Determinismo multi‑ambiente** (matrix 3.11.14/3.11.9) com igualdade de bytes e ZIP reprodutível.  
- **ZIP reprodutível** (DEFLATE nível 6) com `MANIFEST.json` verificado.  
- **CLI de ruleset** (gh api) e **T0** fechando o loop contra drift da UI.

