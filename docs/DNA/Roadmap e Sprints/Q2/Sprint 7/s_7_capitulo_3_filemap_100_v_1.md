# Sprint Q2 — S7 (Stabilize)
## Capítulo 3 — FILEMAP 100% (Blueprint para o Codex)
Versão: v2 (2025-10-31)  
Owner: PO • Eng: Codex • ORR: SRE  
Referências normativas: Cap.1 **v7.1 FINAL**, Cap.2 **v5** (travados)

Changelog v2 (revisão da equipe — 100/10):
- **Manifesto NDJSON verificado**: `s_7_filemap_v_7.json` agora alimenta diretamente o Gate T0 (`t0_spec`) do workflow `s7-validator.yml` — divergência bloqueia merge.
- **Filemap exaustivo (100%)** com inventário *linha‑a‑linha* de arquivos → finalidade → consumidores → GATES → regras de conteúdo.
- **Checker de conformidade do filemap** (`scripts/ci/filemap_check.py`) com EXIT `12 filemap_mismatch` (executado em T1).
- **Rastreabilidade**: matrizes (Arquivo→Gate; Arquivo→Entregável E1..E7; Gate→Evidência).  
- **RACI por pasta** (Owner/Responsible/Consulted/Informed).  
- **Pinos e versões cruzadas** (docs ↔ schemas ↔ scripts).  
- **Requisitos do `pyproject.toml`** e **CODEOWNERS** normativos.  
- **Validação dos Schemas `/schemas/v1/*.schema.json`** no CI (T8) com `jsonschema`.  
- **Hashes esperados** (onde aplicável) referenciados do Cap.1 §9 e Cap.2.

---

### 0) Princípios do Filemap (normativo)
1) **Nomes e caminhos são normativos.** Qualquer divergência = FAIL em T1 (`filemap_check`).  
2) **Tudo em `out/` é gerado** e **MUST NOT** ser versionado (exceto `actions.lock`, que é versionado após T3).  
3) **UTF‑8 sem BOM**, **NFKC**, **sha256 hex lowercase (64)**, **sem newline final** nos bytes canônicos (§Cap.1 §8).  
4) **Jobs estáveis e Ruleset ativo** cobrindo T0..T8 (Cap.2 v4).  
5) **Sem placeholders.** Arquivos marcados MUST conter o conteúdo mínimo descrito abaixo.

---

## A) Top‑level do repositório
```
.
├─ .github/
│  ├─ workflows/
│  │  ├─ s7-validator.yml                  # MUST (workflow único; jobs `t0_spec` + `s7_exec`)
│  │  ├─ s7-exec.yml                       # SHOULD (wrapper legado)
│  │  └─ _s7-orr.yml                       # MUST (reutilizável)
│  ├─ CODEOWNERS                           # MUST (RACI→Owner)
│  └─ dependabot.yml                       # SHOULD (segurança)
├─ bin/
│  ├─ preflight                            # MUST (runbook)
│  └─ setup_preflight_tools.sh             # SHOULD
├─ data/
│  ├─ raw/                                 # MUST (entradas)
│  └─ log/
│     └─ log.jsonl                         # MUST (append-only)
├─ docs/
│  └─ specs/s7/
│     ├─ cap1_spec.md                      # MUST (Cap.1 v7.1)
│     ├─ cap2_gates.md                     # MUST (Cap.2 v4)
│     └─ cap3_filemap.md                   # MUST (este doc)
├─ out/                                    # gerado (gitignored)
├─ schemas/v1/
│  ├─ scorecard.schema.json                # MUST ($id/version)
│  ├─ manifest.schema.json                 # MUST ($id/version)
│  ├─ t0_ruleset_sanity.schema.json        # MUST ($id/version)
│  ├─ t1_yaml.schema.json                  # MUST ($id/version)
│  ├─ t2_security.schema.json              # MUST ($id/version)
│  ├─ t3_pins.schema.json                  # MUST ($id/version)
│  ├─ t4_tests.schema.json                 # MUST ($id/version)
│  ├─ t5_props.schema.json                 # MUST ($id/version)
│  ├─ t6_determinism.schema.json           # MUST ($id/version)
│  └─ t7_append_only.schema.json           # MUST ($id/version)
├─ scripts/
│  ├─ ci/
│  │  ├─ generate_actions_lock.py          # MUST (T3)
│  │  ├─ validate_actions_lock.py          # MUST (T3)
│  │  ├─ verify_action_commit_owners.py    # MUST (T3 anti-spoof)
│  │  ├─ ruleset_sanity.py                 # MUST (T0)
│  │  └─ filemap_check.py                  # MUST (T1)
│  ├─ crypto/
│  │  ├─ sign_batch.py                     # MUST (constantes/domain-tag) 
│  │  └─ verify_batch.py                   # MUST
│  ├─ det/
│  │  └─ check_determinism.py              # MUST
│  ├─ evidence/
│  │  ├─ manifest.py                       # MUST
│  │  ├─ pack.py                           # MUST (DEFLATE-6/repro)
│  │  └─ verify_manifest.py                # MUST
│  ├─ s7/
│  │  ├─ __init__.py                       # MUST (namespace)
│  │  ├─ generate_filemap_manifest.py      # MUST (Gate T0 — regenerar NDJSON)
│  │  ├─ t0_spec_check.py                  # MUST (Gate T0 — validar NDJSON)
│  │  └─ build_orr_bundle.py               # MUST (Bundle determinístico + RESUMO)
│  ├─ merkle/
│  │  ├─ merkle_build.py                   # MUST
│  │  └─ append_only_guard.py              # MUST
│  ├─ normalizer/
│  │  └─ normalize_batch.py                # MUST
│  └─ scorecard/
│     └─ write.py                          # MUST
├─ tests/
│  ├─ fixtures/
│  │  ├─ crypto/test_ed25519_priv.pem      # MUST (allowlist)
│  │  ├─ crypto/test_ed25519_pub.pem       # MUST
│  │  ├─ data/dataset-a.json               # MUST
│  │  ├─ data/dataset-a.csv                # SHOULD
│  │  ├─ data/dataset-neg-domain-tag.json  # MUST (negativo)
│  │  ├─ data/log-invalid-prev-root.jsonl  # MUST (negativo)
│  │  ├─ expected/hashes_dataset_a.json    # MUST (Cap.1 §9)
│  │  └─ expected/batch_sha256.txt         # MUST (Cap.1 §9)
│  ├─ test_normalizer.py                   # MUST
│  ├─ test_merkle.py                       # MUST
│  ├─ test_signature.py                    # MUST
│  └─ test_properties.py                   # MUST
├─ .editorconfig                            # SHOULD
├─ .gitleaks.toml                           # MUST (allowlist)
├─ .gitignore                               # MUST
├─ .yamllint.yml                            # MUST
├─ actions.lock                             # MUST (versionado; gerado por T3)
├─ CODEOWNERS                               # MUST
├─ LICENSE                                  # MAY
├─ Makefile                                 # MAY
├─ pyproject.toml                           # MUST
└─ README.md                                # SHOULD
```

**Regras de conteúdo essenciais:**
- `.gitleaks.toml` **MUST** conter allowlist apenas para `tests/fixtures/crypto/*`.  
- `pyproject.toml` **MUST** fixar `python = "3.11.*"` e dependências mínimas (`jsonschema`, `pynacl`/`cryptography`, etc.) com *upper bounds* estáveis.  
- `CODEOWNERS` **MUST** mapear:
  - `scripts/crypto/*` → `@sre @security`
  - `.github/workflows/*` e `scripts/ci/*` → `@sre`
  - `scripts/s7/*` → `@sre @qa`
  - `schemas/v1/*` → `@po @sre`
  - `tests/**` → `@qa`  
- `dependabot.yml` **SHOULD** cobrir `github-actions` (diário) e `pip` (semanal).

---

## B) Workflows CI (nomes estáveis) — conteúdo mínimo
- `s7-exec.yml` (wrapper) **MUST** chamar `./.github/workflows/_s7-orr.yml` e **NÃO** conter lógica de gates.  
- `_s7-orr.yml` **MUST** definir **exatamente** os jobs: `t0_ruleset_sanity`, `t1_yaml`, `t2_security`, `t3_pins`, `t4_tests`, `t5_props`, `t6_determinism`, `t7_append_only`, `t8_pack`; publicar artefato `s7-orr-evidence` com `out/**`.

---

## C) scripts/* — contratos mínimos por arquivo
- `scripts/crypto/sign_batch.py` **MUST** exportar:
  - `SIGNATURE_PATH = "out/signatures/latest.sig.json"`
  - `BATCH_PATH     = "out/normalized/batch.json"`
  - `PUBKEY_PATH    = "tests/fixtures/crypto/test_ed25519_pub.pem"`
  - `PRIVKEY_PATH   = "tests/fixtures/crypto/test_ed25519_priv.pem"`
  e usar **domain‑tag exata** `tm.s7.batch.v1
` (Base64 padrão c/ padding `=`).  
- `scripts/normalizer/normalize_batch.py` **MUST** aplicar **NFKC**, trimming, case rules (`currency` UPPER; `unit/source` lower), schema v1 e **comparador formal** (Cap.1 §6.A).  
- `scripts/merkle/merkle_build.py` **MUST** construir folhas `sha256(JSON(record))`, duplicar folha ímpar e raiz por `sha256(left||right)`.  
- `scripts/det/check_determinism.py` **MUST** comparar bytes (sem `
` final) e hashes com os **esperados** do Cap.1 §9; comparar ZIP reprodutível.  
- `scripts/evidence/pack.py` **MUST** gerar ZIP com **DEFLATE nível 6**, ordem lexicográfica e `SOURCE_DATE_EPOCH=0`.  
- `scripts/ci/filemap_check.py` **MUST** validar presença/nomes do inventário desta seção; EXIT `12 filemap_mismatch`.
- `scripts/s7/generate_filemap_manifest.py` **MUST** gerar NDJSON estável (4 linhas) usando `git hash-object` e `json.dumps(..., separators=(", ", ": "))`.
- `scripts/s7/t0_spec_check.py` **MUST** validar o NDJSON linha a linha, produzir `out/obs_gatecheck/T0_discovery.json` e garantir `checked=4` no PASS.
- `scripts/s7/build_orr_bundle.py` **MUST** montar `out/s7-orr-evidence.zip` determinístico + `out/orr_s7/filelist.txt` e `RESUMO_ORR_S7.json` com watchers/versões.

---

## D) tests/* — cobertura mínima
- `test_normalizer.py` **MUST** validar schema v1, normalizações e **idempotency_key**.  
- `test_merkle.py` **MUST** validar folhas/raiz determinísticos.  
- `test_signature.py` **MUST** validar round‑trip e **negativos** (domain‑tag errado; Base64 inválido).  
- `test_properties.py` **MUST** validar propriedades (determinismo, ordenação, idempotência, invariantes append‑only).

**Fixtures mínimas (conteúdo exigido):**
- `expected/hashes_dataset_a.json` **MUST** conter:  
  `entries_hash = f830ec4f7b468dc569c56d6b4a18e7379a4958ea8789f36dcaf13f44ff472112`  
  folhas = `["1ada972b1985ad3270335bf121a4644b0c67705dcf2c864eb7f21643c7beeec0","56089c09c07ef28609edfcec038123f1a25dd090c31cd371f7170ad520ae0703","3460bf3d6e1fad050236f94b2925505c46a2e0439b0f444a94bc10a72f0e911a"]`  
  `root = cc1fd0ae131fd0c78e111655ae057b282327f896f19e8bf38f862f901dda0793`  
- `expected/batch_sha256.txt` **MUST** conter:  
  `514b3a78aa5883cdb899bb4e9b442657e7213704c2652673956b364f46184ceb`

---

## E) schemas/v1/* — publicação & validação
- Todos os schemas **MUST** ter `$id` e `version` `1.0.0`, hospedados em `https://trendmarket/schemas/v1/<nome>.schema.json`.  
- T8 **MUST** validar `scorecards/s7.json` e `MANIFEST.json` contra os schemas; T0..T7 **SHOULD** validar seus relatórios mínimos.

---

## F) Rastreabilidade (matrizes)
### F.1) Arquivo → Gate(s)
(Ver §L consolidado — mantido e expandido.)

### F.2) Arquivo → Entregável (E1..E7)
| Caminho | Entregável |
|---|---|
| `scripts/normalizer/normalize_batch.py` | **E1 — Normalizador** |
| `scripts/scorecard/write.py` | **E7 — Evidências/Scorecard** |
| `scripts/merkle/merkle_build.py` | **E3 — Merkle** |
| `scripts/crypto/sign_batch.py` | **E4 — Assinatura** |
| `scripts/crypto/verify_batch.py` | **E4 — Verificação** |
| `scripts/merkle/append_only_guard.py` | **E5 — Append‑only** |
| `scripts/evidence/{manifest,pack,verify_manifest}.py` | **E7 — Empacotamento** |
| `scripts/det/check_determinism.py` | **E6 — Determinismo** |
| `scripts/s7/{generate_filemap_manifest,t0_spec_check,build_orr_bundle}.py` | **S7 — Gate T0/Bundle ORR** |

### F.3) Gate → Evidência (arquivo gerado)
| Gate | Evidência (out/...) |
|---|---|
| T0 | `evidence/T0_ruleset_sanity/ruleset_check.json` |
| T1 | `evidence/T1_yaml/{yamllint_report.txt,repo_structure.json,filemap_check.json}` |
| T2 | `evidence/T2_security/gitleaks_report.json` |
| T3 | `evidence/T3_pins/{actions.lock,pins_report.json,sha_origin_report.json}` |
| T4 | `evidence/T4_tests/pytest_report.json` |
| T5 | `evidence/T5_props/properties_summary.json` |
| T6 | `evidence/T6_determinism/{compare.json,hash_match.json,zip_compare.json}` |
| T7 | `evidence/T7_append_only/append_only_report.json` |
| T8 | `scorecards/s7.json`, `MANIFEST.json`, `s7-evidence.zip` |

---

## G) RACI por pasta (Owner/Responsible/Consulted/Informed)
| Pasta | O | R | C | I |
|---|---|---|---|---|
| `.github/workflows` | PO | SRE | Security | Dev Team |
| `scripts/ci` | SRE | SRE | PO/Security | Dev Team |
| `scripts/s7` | SRE | SRE | QA/PO | Dev Team |
| `scripts/crypto` | Security | Dev | SRE | PO |
| `scripts/normalizer` | PO | Dev | Data | SRE |
| `scripts/merkle` | SRE | Dev | Security | PO |
| `schemas/v1` | PO | SRE | Dev | QA |
| `tests/**` | QA | QA | Dev/SRE | PO |
| `data/**` | Data | Data | Dev | SRE |

> **CODEOWNERS** MUST refletir as colunas **O**/**R** onde aplicável.

---

## H) `pyproject.toml` — requisitos normativos
- `[project]` com `name="trendmarketv2-oracle-s7"`, `requires-python=">=3.11,<3.12"`.  
- `[project.optional-dependencies]` com extras `dev` (pytest, hypothesis, jsonschema, yamllint, gitleaks-installer se usado).  
- `[tool.pytest.ini_options]` com `addopts = "-q"` e `json-report`.  
- `[tool.yamllint]` opcional ou via `.yamllint.yml`.  
- `[tool.ruff]` **MAY** se adotado; não é gating nesta sprint.

---

## I) `CODEOWNERS` — regras mínimas
```
# CI & ORR
.github/workflows/*           @sre
scripts/ci/*                  @sre
schemas/v1/*                  @po @sre
# Core oracle
scripts/crypto/*              @security @sre
scripts/merkle/*              @sre @devs
scripts/normalizer/*          @devs @data
# Tests
tests/**                      @qa
```

---

## J) `README.md` — seções mínimas
1) **Overview S7** (linka Cap.1/2/3).  
2) **Run Local**: `bin/preflight` e comandos §10 do Cap.2.  
3) **Gates e Evidências**: onde achar `out/evidence/` e `scorecards/`.  
4) **Política de chaves de teste** (T2) e *waivers* (Cap.2).

---

## K) actions.lock (T3)
- Versionado após geração; **MUST** refletir SHAs usados em `_s7-orr.yml` e quaisquer outros workflows consumidos pelo wrapper.

---

## L) Matriz de Cobertura (arquivo → Gates) — expandida
| Caminho | MUST/SHOULD | Gates |
|---|---|---|
| `.github/workflows/s7-exec.yml` | MUST | T0..T8 |
| `.github/workflows/_s7-orr.yml` | MUST | T0..T8 |
| `scripts/ci/filemap_check.py` | MUST | T1 |
| `scripts/ci/{generate_actions_lock,validate_actions_lock,verify_action_commit_owners,ruleset_sanity}.py` | MUST | T0,T3 |
| `scripts/normalizer/normalize_batch.py` | MUST | T4,T5,T6 |
| `scripts/merkle/{merkle_build,append_only_guard}.py` | MUST | T4,T6,T7 |
| `scripts/crypto/{sign_batch,verify_batch}.py` | MUST | T4,T6 |
| `scripts/det/check_determinism.py` | MUST | T6 |
| `scripts/evidence/{manifest,pack,verify_manifest}.py` | MUST | T8 |
| `scripts/scorecard/write.py` | MUST | T8 |
| `tests/test_{normalizer,merkle,signature}.py` | MUST | T4 |
| `tests/test_properties.py` | MUST | T5 |
| `tests/fixtures/**` | MUST | T2,T4,T6,T7 |
| `schemas/v1/*.schema.json` | MUST | T0..T8 |
| `data/raw/**` | MUST | T4,T5,T6 |
| `data/log/log.jsonl` | MUST | T7 |
| `out/**` | (gerado) | T0..T8 |

---

## M) Git: ignore, attrs e retenção
- `.gitignore` **MUST** conter: `out/**`, `__pycache__/`, `.pytest_cache/`, `.venv/`, `*.zip`.  
- **Retenção de artefatos CI:** ≥ 7 dias (Cap.2 §3).  
- **Sem segredos reais**; somente fixtures de teste (T2) com allowlist.

---

## N) Invariantes de conteúdo por arquivo (essenciais)
- `scripts/crypto/sign_batch.py` **MUST** exportar as 4 constantes e usar **domain‑tag** `tm.s7.batch.v1
`.  
- `out/normalized/batch.json` **MUST** ser **canonical JSON** (Cap.1 §8).  
- `out/s7-evidence.zip` **MUST** validar contra `out/MANIFEST.json` (Cap.2 T8).  
- `schemas/v1/*.schema.json` **MUST** conter `$id` + `version` `1.0.0`.  
- `scripts/ci/filemap_check.py` **MUST** listar **exatamente** os caminhos desta especificação.

---

## O) DoD — Capítulo 3 (Filemap)
- Repositório contém **100%** dos caminhos/arquivos listados **sem variações**.  
- T1 inclui `filemap_check` e falha se faltar **qualquer** item.  
- `pyproject.toml` e `CODEOWNERS` conformes.  
- Matriz de rastreabilidade completa (Arquivo→Gate, Arquivo→E*, Gate→Evidência).  
- Links e versões entre Cap.1/2/3 e Schemas `/schemas/v1` sincronizados.

---

## P) Checklist de verificação (pré‑merge)
1. T0: `ruleset_check.json.ok=true` e 9 contexts presentes.  
2. T1: `yamllint` exit 0; `repo_structure.json` ok; `filemap_check.json.ok=true`.  
3. T2: `gitleaks` sem HIGH/CRIT; allowlist só em fixtures.  
4. T3: `actions.lock` atualizado; `pins_report.ok=true`; `sha_origin_report.spoof_alerts=0`.  
5. T4: `pytest` 100% verde; constantes de `sign_batch.py` presentes.  
6. T5: todas as propriedades verdadeiras.  
7. T6: bytes/hashes/ZIP idênticos e esperados.  
8. T7: append‑only ok; negativos falham.  
9. T8: `scorecards/s7.json` e `MANIFEST.json` válidos; ZIP verificado.

