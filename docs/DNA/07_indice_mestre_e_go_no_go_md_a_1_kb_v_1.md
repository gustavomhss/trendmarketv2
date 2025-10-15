---
file: 07-Indice-Mestre-e-GoNoGo.md
version: v1.0 (A1 KB — Padrão Ouro)
date: 2025-09-09
author: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: index-canonical
---

# 07) Índice Mestre & Go/No-Go de Release — A1
> **Propósito:** costurar os Arquivos **01→06** em uma visão única de **estado, dependências, gates de promoção e plano D0→D30 para Produção**. Documento de **coordenação executável**: seção de **checklists machine‑readable**, **matriz de readiness**, **RACI** e **pacote de evidências**.

---

## 0) Escopo & Premissas
- Timezone **America/Bahia**; datas/hora em **UTC** + offset local quando aplicável.  
- NSM alvo: **Time‑to‑Preço‑Válido p95 ≤ 800 ms** (Arquivo 01).  
- Regras de promoção: **SemVer**, **watchers→hooks** (A110), **Evidence JSON** (Arquivos 03–05), **segurança/privacidade** (Arquivo 06).  
- **Fonte de verdade**: os **canvases** listados na §1.

---

## 1) Inventário de Artefatos Canônicos (com versões)
| ID | Nome no Canvas | Versão | Dono | Status |
|---|---|---|---|---|
| **01** | Contexto & Product Engine | **v2.0 TURBO** | A1 | ✅ Canon |
| **02** | Domínios — PM/Oráculos/FX | **v1.2 Deepdive Supremo** *(target)* / **v1.0** *(editado por você — canvas `02-dominios-a1-pm-oraculos-fx`)* | A1 | ⚠️ **Alinhar workspace → v1.2** |
| **03** | Contratos & APIs | **v1.1 Deepdive Ilustres** | A1 ↔ A2 ↔ A3 | ✅ Canon |
| **04** | Hooks, Policies & Runbooks | **v1.1 Deepdive Ilustres** | A1 ↔ A5 | ✅ Canon |
| **05** | Observabilidade, Testes & Evidências | **v1.0 Padrão Ouro** | A1 ↔ A5 | ✅ Canon |
| **06** | Segurança, Privacidade & On‑Chain | **v1.1 Deepdive Supremo** | Security ↔ A1 ↔ A5 | ✅ Canon |

> **Ação imediata:** publicar **02 v1.2** como versão ativa e arquivar **02 v1.0** como histórico (cherry‑pick de edits, se houver). Dono: **A1**. Prazo: **D+1**.

---

## 2) Dependências & Ordem de Promoção (grafo lógico)
```text
01 Contexto
 ├─ 02 Domínios (PM/Oráculos/FX)
 │   ├─ 03 Contratos & APIs (JSON Schema, OpenAPI)
 │   │   ├─ 04 Hooks/Policies/Runbooks (A110)
 │   │   │   ├─ 05 Observabilidade/Testes/Evidence
 │   │   │   └─ 06 Segurança/Privacidade/On‑Chain
 │   └─ (opcional) On‑chain commitments
└─ 07 Índice & Go/No‑Go (este)
```
**Ordem de promoção recomendada:** 01 → 02 → 03 → 06 → 04 → 05 → 07.

---

## 3) Matriz de Readiness (RAG)
| Área | Critério | Fonte | Meta | Status | Notas |
|---|---|---|---:|:--:|---|
| NSM | p95 ≤ 800 ms | 05 | ≤800 | 🟩 | *evidence.exemplo p95=770* |
| PM | `clearing_latency_ms.p95` | 05/02 | ≤150 | 🟩 | testes E2E ok |
| Oráculos | `staleness_ms.p95` | 05/02 | <30000 | 🟩 | failover testado |
| FX | `route_latency.p95` | 05/02 | ≤1500 | 🟨 | ladder L1→L3 ok; L4 não exercitado |
| CDC | `lag_p95_s` | 05/03 | ≤120 | 🟩 | watchers ok |
| Web/API | `INP_p75`/breaking | 05/03 | ≤200/==0 | 🟩 | FE rollback ensaiado |
| Security | SBOM/ass. imagem/keys | 06 | ==OK | 🟩 | cosign+gatekeeper |
| Hooks | cobertura 100% must‑have | 04 | ==100% | 🟩 | hooks‑coverage PASS |

**Ação:** executar **L4** da política `pack_lite` em simulação (04 §6). Dono: **A1**. Prazo: **D+3**.

---

## 4) SemVer & Compatibilidade — Matriz 03↔Consumidores
| Contrato | Produtor | Consumidores críticos | Janela aceita | Breaking? |
|---|---|---|---|---|
| `pm_bid_submitted` | A1 | A3 (FE/API) | [1.0.0, 2.0.0) | **Não** (gate) |
| `pm_clearing_result` | A1 | A3/A2 | [1.0.0, 2.0.0) | **Não** |
| `oracle_price_update` | A1 | A2 | [1.0.0, 2.0.0) | **Não** |
| `fx_quote` | A1 | A3 | [1.0.0, 2.0.0) | **Não** |

**Gate:** `schema_breaking==0` + `contract_tests==PASS` (03 §6/§10).

---

## 5) Cobertura Watchers → Hooks → Runbooks (04)
| Watcher | Hook(s) | Runbook | Coberto |
|---|---|---|:--:|
| `oracle_staleness_watch` | `a1_oracle_staleness_guard` | 04 §5.1 | ✅ |
| `oracle_divergence_watch` | `a1_oracle_divergence_guard` | 04 §5.1 | ✅ |
| `fx_route_latency` | `a1_fx_router_latency_guard` + ladder `pack_lite` | 04 §5.3 | ✅ |
| `fx_cip_delta` | `a1_cip_delta_guard` | 04 §5.4 | ✅ |
| `auction_invariant_breach` | `a1_auction_invariant_guard` | 04 §5.2 | ✅ |
| `cdc_lag_watch` | `a2_cdc_lag_guard` | 04 §5.5 | ✅ |
| `schema_registry_drift_watch` | `a2_schema_drift_guard` | 04 §5.5 | ✅ |
| `ab_srm_watch`/`model_drift_watch` | `a4_ab_srm_guard`/`a4_model_drift_guard` | 04 §5.6 | ✅ |
| `cls_payin_cutoff_watch` | `a1_cls_cutoff_guard` | 04 §5.7 | ✅ |
| `image_vuln_regression_watch`/`idp_keys_rotation_watch` | `a5_image_vuln_guard`/`a5_idp_keys_rotation_guard` | 04 §5.8 | ✅ |

---

## 6) RACI — Governança Operacional
```yaml
R: A1 (domínio PM/Oráculos/FX)
A: A1 lead
C: A2 (dados/registry), A3 (API/FE), A5 (SRE), Security
I: Stakeholders (statusboards em 05)
```

**On‑call:** A1 semanal; A5 follow‑the‑sun. **Escalonamento:** conforme 04 §5.

---

## 7) Road to Prod — **D0→D30** (checklist executável)
```yaml
road_to_prod:
  D0:
    - align_02_version: publish v1.2 as active (archive v1.0)
    - contract_tests: PASS (03)
    - hooks_dry_run: PASS (04)
    - obs_dashboards: deployed (05)
    - security_gates: SBOM==OK & images_signed (06)
  D7:
    - load_test: PM p95<=800ms; FX p95<=1500ms
    - chaos_lite: 1 feed & 1 venue with jitter
    - evidence_json: generated (05 §8)
  D14:
    - ladder_L4_simulation: executed & cleared (04 §4)
    - cls_tabletop: done (04 §9)
  D21:
    - DR_restore_test: pass (06 §9)
    - hooks_drift_watch: green
  D30:
    - go_nogo_board: all gates GREEN
    - release_candidate: tag & sign (rc1)
```

---

## 8) Go/No‑Go — **Gates Objetivos** (agregados 01–06)
**Go somente se:**
1) **SemVer/Contracts (03):** `schema_breaking==0` • `openapi_lint==OK` • `contract_tests==PASS`.  
2) **Hooks/Policies (04):** `hooks_a110==READY` • cobertura watchers=100% • `dry_run_passed==true`.  
3) **Observabilidade/Testes (05):** `evidence.json` anexado • NSM p95≤800ms • staleness p95<30s • FX p95≤1500ms.  
4) **Segurança (06):** `mtls_all==true` • RBAC mínimo • `high_vulns==0` • imagens assinadas • `keys_rotation<=90d`.  
5) **Operação:** on‑call definido; runbooks publicados; statusboards atualizados.  
**No‑Go se:** qualquer métrica crítica sem coleta; PII em logs; drift entre `hooks/a1.yaml` e produção; ausência de DR test ≤90d.

**Painel de decisão (preencher no dia da promoção):**
```yaml
go_nogo_board:
  contracts: GREEN
  hooks: GREEN
  observability: GREEN
  security: GREEN
  operations: GREEN
  decision: GO
  signed_by: [A1-lead, A5-SRE, Security]
```

---

## 9) Pacote de Evidências (conteúdo mínimo)
```text
/pack-evidence/
  evidence.json                 # 05 §8 (NSM, Oracles, FX, tests)
  evidence.security.json        # 06 §13
  contracts/                    # 03 (schemas + examples)
  openapi/a1.yaml               # 03
  hooks/a1.yaml                 # 04
  dashboards/*.yaml             # 05
  statusboards/snapshot.yaml    # 05 §9
  sbom/*.spdx                   # 06 §6
  signatures/*.sig              # imagens/artefatos assinados
  CHANGELOG.md                  # §11
```

---

## 10) Plano de Release, Rollback & Comunicação
**Release:** tag `a1-<AAAA>-<MM>-<DD>-rcN` + *sign*; janela off‑peak **America/Bahia**.  
**Rollback:** `rollback plan` nos hooks/policies (04) + revert de **schemas** (03) + freeze de deploys.  
**Comunicação (ChatOps):** templates 04 §10; statuspage interna com NSM/alertas verdes.

---

## 11) Riscos & Mitigações (resumo)
| Risco | Impacto | Prob. | Mitigação | Dono |
|---|---|:--:|---|---|
| Divergência oracle | Preço inválido | M | Hooks + TAU/K semanal | A1 |
| Rota FX lenta | NSM > alvo | M | Ladder L1→L4 + alternate_venue | A1 |
| Breaking de schema | Paralisa consumidores | B | Gate SemVer + contract tests | A2 |
| Falha de segurança (supply) | Bloqueio de release | B | SBOM==0 high vulns + assinatura | Security |
| DR não ensaiado | RTO/RPO não cumprido | B | Restores trimestrais | A5 |

---

## 12) Change Log (vivo)
- **2025‑09‑09** — Criação do **Índice Mestre (v1.0)** com RAG, Road‑to‑Prod D0→D30 e pacotes de evidência.

---

## 13) Anexos — Templates Executáveis
### 13.1 Gerador de **Release ID** (padrão)
```yaml
release_id: "a1-${YYYY}-${MM}-${DD}-rc${N}"
```

### 13.2 Check de Alinhamento do Workspace (Arquivo 02)
```yaml
workspace_alignment:
  target_version: "02 v1.2"
  current: ["02 v1.0 (canvas: 02-dominios-a1-pm-oraculos-fx)"]
  action: "promover v1.2 e arquivar v1.0"
  owner: A1
  due: D+1
```

---
**Conclusão:** Este **Índice Mestre** consolida **estado, dependências, gates e plano D0→D30**, servindo de **fonte operacional** para a promoção a produção. Com **02 v1.2 ativo**, os artefatos 01–06 atendem ao **padrão ouro** e habilitam um **GO** com segurança.

