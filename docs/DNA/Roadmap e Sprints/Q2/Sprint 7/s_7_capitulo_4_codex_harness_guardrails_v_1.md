# Sprint Q2 — S7 (Stabilize)
## Capítulo 4 — Codex Harness & Guardrails (SOP operacional, sem alterar Cap.1–3)
Versão: v2 (2025-10-31)  
Owner: PO • Eng: Codex • ORR: SRE  
Referências **normativas**: Cap.1 v7.1 (Spec) • Cap.2 v4 (Gates T0..T8) • Cap.3 v2 (Filemap 100%)

> Escopo: **Processo e automação de execução** para o agente Codex cumprir **Cap.1–3** sem atalhos. **Não** cria novos gates, **não** exige novos arquivos no repo.

Changelog v2 (upgrade maciço 4→10):
- **CEC — Codex Execution Contract**: contrato formal de entradas/saídas, estados, EXITs e telemetria do agente.
- **Plan.json (efêmero) — Schema + Exemplo**: estrutural, auditável e verificável na PR.
- **Receitas `gh` e API**: comandos exatos para disparo de workflow, coleta de artefatos e inspeção de rulesets.
- **Anti‑flake rigoroso (3×)** com critérios diferenciais e matriz de decisão.
- **Matriz de Riscos→Controles** (falhas típicas do LLM e contramedidas concretas).
- **Rubrica de revisão (RACI→CODEOWNERS)** com checklists objetivos e razões de recusa prontas.
- **Triage & Rollback SOP** com árvores de decisão e tempos‑alvo.
- **Observabilidade do Harness**: correlação run↔commit↔scorecard, IDs, hashes e logs mínimos exigidos **no corpo da PR**.
- **Modelo de PR canônico** com marcadores verificáveis.

---

# 0) Princípios (Playbook + RFC‑2119)
1) **MUST** obedecer Cap.1–3 literalmente.  
2) **MUST NOT** criar/editar arquivos fora do **Filemap**.  
3) **MUST** abrir PR **só** após T0..T8 **passarem** no branch sandbox **e** Anti‑flake 3× aprovado.  
4) **MUST** registrar telemetria mínima do CEC no corpo da PR.  
5) **MAY** rodar *shadow run* (não‑gating) e anexar métricas.

---

# 1) CEC — Codex Execution Contract (contrato do agente)
## 1.1 Estados
`PLANNING → PATCHING → SANDBOX_PUSH → ORR_RUN[n] → ORR_OK? → (NO) REPLAN | (YES) PR_OPEN → REVIEW → MERGE | REWORK`

## 1.2 Entradas (MUST)
- Repo: `trendmarketv2@<sha>` (HEAD de `main`).  
- Docs: `docs/specs/s7/cap1_spec.md (v7.1)`, `cap2_gates.md (v4)`, `cap3_filemap.md (v2)`.  
- Workflow: `S7 ORR Exec` (Cap.2 §7).  
- Branch sandbox: `q2-s7-codex-<YYYYMMDD>-<HHMM>-<shortsha>`.

## 1.3 Saídas (MUST)
- **Diff único** (apenas caminhos do Filemap).  
- **Runs ORR**: 3 execuções verdes (links).  
- **Scorecard**: `out/scorecards/s7.json` (conteúdo colado na PR).  
- **ZIP**: `out/s7-evidence.zip` (SHA256 colado na PR).  
- **Plan.json (efêmero)** colado na PR.

## 1.4 Telemetria mínima (MUST)
No corpo da PR (ver §7):
- `cec.repo_sha`, `cec.branch`, `cec.run_ids[]` (3 runs), `cec.scorecard_sha256`, `cec.evidence_zip_sha256`, `cec.started_at`, `cec.finished_at`.

## 1.5 EXITs (interpretação uniforme)
- `CEC-10 filemap_violation` — patch toca caminho fora do Filemap (Cap.3).  
- `CEC-20 gates_fail` — qualquer gate T0..T8 FAIL em **qualquer** run.  
- `CEC-30 determinism_diverge` — divergência entre runs na T4–T6.  
- `CEC-40 missing_artifacts` — não há scorecard/ZIP no artefato do run.  
- `CEC-50 pr_template_invalid` — corpo da PR sem campos obrigatórios/códigos.  
- `CEC-60 stale_base` — base não é o HEAD de `main`.

---

# 2) Plan.json — Schema & Exemplo (efêmero)
**Schema (normativo para validação humana):**
```json
{
  "version":"1.0",
  "base_sha":"<40-hex>",
  "tasks":[
    {"id":"T-NORM-01","files":["scripts/normalizer/normalize_batch.py"],"gates":["T4","T5","T6"],"evidence":["out/evidence/T4_tests/pytest_report.json"]},
    {"id":"T-CRYPTO-02","files":["scripts/crypto/sign_batch.py"],"gates":["T4","T6"],"evidence":["out/evidence/T4_tests/pytest_report.json","out/evidence/T6_determinism/compare.json"]}
  ],
  "constraints":{"filemap":"strict","single_patch":true}
}
```
**Exemplo real (colar na PR):** (preencher pelos passos do agente)

---

# 3) Receitas `gh` e API (operacional)
## 3.1 Disparar ORR no sandbox
```
GH_REPO="<owner>/trendmarketv2"
BR="q2-s7-codex-YYYYMMDD-HHMM-<shortsha>"
# Disparo por nome do workflow
gh workflow run "S7 ORR Exec" --ref "$BR" --repo "$GH_REPO"
# (opcional) aguardar e listar últimos runs
gh run list --workflow "S7 ORR Exec" --branch "$BR" --repo "$GH_REPO"
```

## 3.2 Baixar artefato `s7-orr-evidence`
```
RUN_ID=<id>
gh run download $RUN_ID --name s7-orr-evidence --repo "$GH_REPO" -D out/
sha256sum out/s7-evidence.zip > out/sha256_s7_evidence.txt
```

## 3.3 Sanity de Ruleset (Cap.2 T0) — via API
```
# Espera contexts exatos (T0..T8). Ver também T0 ruleset_sanity do CI.
gh api repos/$GH_REPO/rulesets > out/rulesets.json
```

---

# 4) Anti‑flake 3× — critérios e decisão
- **MUST** executar o ORR **3×** no mesmo branch sandbox.
- **Aprovado**: 3/3 verdes **e** hashes/ZIP idênticos (Cap.2 T6).  
- **Rejeitado**: qualquer FAIL **ou** divergência nos comparativos.  
- **Tempo‑alvo**: 20 min total (indicativo) — se excedido, abrir issue de performance (não‑gating nesta sprint).

Matriz de decisão:
| Caso | T0..T8 | Zip/bytes | Decisão |
|---|---|---|---|
| 3 verdes | OK | iguais | Abrir PR |
| 1+ falha | — | — | Replanejar, novo patch |
| 3 verdes | difere | Reinvestigar T6; não abrir PR |

---

# 5) Matriz de Riscos → Controles (LLM‑centric)
| Risco típico | Controle (MUST/SHOULD) | Onde prova |
|---|---|---|
| Criar arquivos fora do Filemap | Filemap Guard (checagem local) | `CEC-10` se violar |
| Ignorar gates e abrir PR cedo | SOP exige ORR PASS 3× antes da PR | Corpo PR + links de run |
| Drift de ruleset | T0 + `gh api` sanity | `out/evidence/T0_ruleset_sanity/*` |
| Falta de constantes crypto | Teste T4 dedicado | `pytest_report.json` |
| Não‑determinismo | T6 + Anti‑flake | `compare.json/zip_compare.json` |
| Segredos vazando | T2 (Gitleaks) | `gitleaks_report.json` |
| Evidência incompleta | T8 + manifesto verificado | `MANIFEST.json` + verificação |

---

# 6) Rubrica de Revisão (RACI→CODEOWNERS)
**Security (scripts/crypto/*):** domain‑tag `tm.s7.batch.v1
`; Base64 padrão; constants presentes; negativos cobertos.  
**SRE (scripts/ci/*, workflows):** nomes de jobs estáveis; pins por SHA + anti‑spoof; ruleset T0 ativo.  
**PO/SRE (schemas/v1/*):** `$id`/`version` corretos; scorecard/manifest válidos.  
**QA (tests/**):** cobertura de negativos; properties sem falsos positivos.

Checklist objetivo (colar na review):
- [ ] Patch dentro do Filemap (Cap.3)  
- [ ] 3 runs verdes + ZIP/bytes idênticos (Cap.2 T6)  
- [ ] Scorecard colado na PR (JSON completo)  
- [ ] SHA256 do ZIP colado  
- [ ] Links dos 3 runs  
- [ ] Constantes/crypto OK (testes)  
- [ ] Pins + anti‑spoof OK  
- [ ] T0 ruleset sanity OK

Motivos padrão de recusa:
- `REFUSE-10`: faltam 1+ campos obrigatórios no corpo da PR.  
- `REFUSE-20`: divergência de determinismo ou anti‑flake não conduzido.  
- `REFUSE-30`: patch tocou caminho fora do Filemap.

---

# 7) Modelo de PR canônico (verificável)
```
# S7 — Codex PR (Plan→Patch→ORR PASS 3×)

## CEC (telemetria)
repo_sha: <40-hex>
branch: q2-s7-codex-YYYYMMDD-HHMM-<shortsha>
run_ids: [<id1>,<id2>,<id3>]
scorecard_sha256: <64-hex>
evidence_zip_sha256: <64-hex>
started_at: <rfc3339>
finished_at: <rfc3339>

## Plan.json (efêmero)
```json
{
  "version":"1.0",
  "base_sha":"<40-hex>",
  "tasks":[...],
  "constraints":{"filemap":"strict","single_patch":true}
}
```

## Scorecard (out/scorecards/s7.json)
```json
{ ... }
```

## Evidências
Artefato: s7-orr-evidence  
SHA256(out/s7-evidence.zip): `<64-hex>`

## Arquivos tocados (todos constam no Filemap)
- scripts/... (listar)

## Checklist
- [x] T0..T8 PASS **3×**
- [x] ZIP/bytes idênticos nos 3 runs (Cap.2 T6)
- [x] Domain‑tag `tm.s7.batch.v1
` intacta
- [x] Constantes `SIGNATURE_PATH|BATCH_PATH|PUBKEY_PATH|PRIVKEY_PATH` presentes
```

---

# 8) Triage & Rollback SOP
**8.1 Árvores de decisão**
- **T3 FAIL** → Corrigir lock/pins/owner; **sem waiver**; repetir ORR.
- **T6 FAIL** → Verificar `SOURCE_DATE_EPOCH`, ordem lexicográfica, `
` final, locale; reproduzir local; repetir 3×.
- **T7 FAIL** → Corrigir `prev_root/index/created_at`; anexar `details` com linha exata do erro.

**8.2 Tempos‑alvo** (indicativos): triagem 15m; patch corretivo 45–90m; novo ORR 20m.

**8.3 Rollback**
- Sem efeitos em produção nesta sprint; rollback = fechar PR e descartar branch sandbox.

---

# 9) Observabilidade do Harness
**IDs & correlação (MUST na PR):** `repo_sha`, `branch`, `run_ids[]`, `evidence_zip_sha256`, `scorecard_sha256`.  
**Métricas de processo (não‑gating):** lead time, churn, pass rate, repetibilidade (hash ZIP idêntico).

---



---

# 11) DoD — Capítulo 4 (v2)
- **CEC** formalizado com estados, EXITs e telemetria mínima.  
- **Plan.json** definido (schema + exemplo) e exigido na PR.  
- **Receitas `gh`** para disparo/artefatos/ruleset.  
- **Anti‑flake 3×** com critérios claros.  
- **Matriz Risco→Controle**, **Rubrica de revisão**, **Triage & Rollback** e **Observabilidade** completas.  
- **Superprompt** operacional pronto para uso.

