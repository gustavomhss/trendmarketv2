---
file: 01-Canonicos-e-Contexto-ProductBrief.md
version: v2.0 (A1 KB)
date: 2025-09-09
owner: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: canonical
---

# 01) Canônicos & Contexto — Product Brief (A1)
> **Propósito:** prover o **contexto canônico** para o Agente A1 operar com foco no **NSM** e sob **governança forte** (watchers + Hook A110). Este arquivo é a **fonte de verdade** de objetivos, métricas de entrada, guard‑rails, precedência e orçamentos.

## 1. Princípios Bar‑Raiser (Bezos × Jobs × Knuth × Perez)
- **Working Backwards (Bezos):** comece pelo **resultado** e pela **métrica de entrada** que move o NSM. Sempre redija uma **press‑note (2 linhas)** + **FAQ curto**.
- **Foco & Simplicidade (Jobs):** 1000 nãos. Entrega **mínima, elegante e ponta‑a‑ponta**. Corte tudo que não reduz o NSM.
- **Rigor & Invariantes (Knuth):** **invariantes explícitos**, testes **property‑based** e **orçamento de complexidade** para escolhas críticas.
- **Operação & Política (Perez):** *fail‑fast*, políticas **machine‑readable** (hooks/limiares), runbooks e escalonamento. **Evidência antes de promover.**

### 1.1) O que é o **Product Engine** — Definição Operacional (TURBO)
> Sistema sócio‑técnico que transforma **entradas** (Brief, métricas, restrições, dados/feeds) em **saídas em produção** (serviços, contratos, APIs, políticas, hooks, dashboards, runbooks), medido pelo **NSM** e governado por **watchers+Hook A110** em **release train** quinzenal.

**Responsabilidades centrais**
1) **Escolher** problemas que movem o NSM (Working Backwards).  
2) **Especificar** contratos (JSON Schema), APIs (OpenAPI), **hooks A110**, SLOs e **orçamentos** (latência/staleness).  
3) **Construir & Integrar** (PM/Oráculos/FX/DEC/ML/Plataforma) preservando compatibilidade e rastreabilidade.  
4) **Verificar** com **testes** (unit/property/integration/e2e/carga) e **Evidence JSON**.  
5) **Operar** via **watchers+hooks**, runbooks e BCDR; **aprender** por telemetria/dashboards.

**Capacidades (mapa)**
- **Strategy** (PR‑FAQ, métricas de entrada) → **Spec** (contratos/APIs/hooks/SLOs) → **Build** (épicos) → **Verify** (testes/evidência) → **Operate** (SRE+hooks) → **Learn** (postmortem/OKRs) → ciclo.

**Arquitetura (planos)**
- **Control Plane**: governança (gates Go/No‑Go), **schema registry**, catálogo de hooks, SLOs, release train.  
- **Data Plane**: fluxos PM/Oráculos/FX (eventos, cotações, clearings) instrumentados (traces + métricas RED + específicas).  
- **Audit Plane**: Evidence JSON, ADRs, waivers, âncoras (opcional on‑chain), statusboards.

**Modelos canônicos (machine‑readable)**
```yaml
contract:
  id: "oracle_price_update"
  semver: "1.0.0"
  compat: "backward-only"
  schema_ref: "contracts/oracle_price_update.schema.json"
api:
  id: "A1"
  openapi: "openapi/a1.yaml"
hook:
  id: "a1_oracle_staleness_guard"
  rule: "oracle.staleness_ms>30000•5m -> switch_to_twap_failover; owner=A1; rollback=yes"
slobudget:
  nsm_p95_ms: 800
  staleness_p95_s: 30
  fx_route_p95_ms: 1500
```

**Invariantes do Product Engine** (devem ser verdade **sempre**)
- Nenhuma **métrica crítica** sem **watcher + hook + owner**.  
- Nenhuma **mudança** sem **contrato**; **breaking** bloqueia release.  
- **Sem evidência, sem promoção** (Evidence JSON obrigatório).  
- **PII off‑chain** e **reversibilidade** (rollback possível).  
- **Traço** de decisão/auditoria ≥95%.

**Políticas & Histerese (exemplo)**
```yaml
policy:
  - id: pack_lite
    when: "fx.route_latency.p95>1500•5m"
    then: ["reduce_venues","prefer_low_latency","lower_freq"]
    clear_when: "fx.route_latency.p95<1200•10m"
  - id: twap_failover
    when: "oracle.staleness_ms>30000•5m"
    then: ["switch_to_twap_failover","quorum_reweight"]
    clear_when: "oracle.staleness_ms<20000•10m"
```

**Interfaces (A1 com os demais)**
- **A2** (Data): contratos/CDC/dbt/registry; *breaking* = bloquear.  
- **A3** (Decision/APIs/FE): consumo de `pm_clearing_result`/`fx_quote`; degrade_route.  
- **A4** (ML): features/sinais ↔ `model_score_event` (metadados).  
- **A5** (SRE): SLO/alertas; promoção via gates; DR/tabletop.

**Checklists (Product Engine)**
- **DoR:** owner; contrato revisado; hooks definidos; testes listados; painel alvo.  
- **DoD:** SLOs verdes; hooks exercitados (logs/trace); Evidence JSON; runbooks atualizados.  
- **DoA:** 30 dias com p95≤0,8s; staleness<30s; CIP ε estável; auditoria≥95%.

**Anti‑padrões (e efeito)**
- Ship sem contrato → **retrabalho + regressões**.  
- Métrica sem hook → **incidente sem ação**.  
- Brief desatualizado → **prioridade errada**.  
- PII em logs → **viola privacidade**.

**Exemplo ponta‑a‑ponta (mini‑roteiro)**
1) Brief diz “staleness p95<30s”.  
2) A1 implementa MAD/quantis + TWAP(K) com quorum≥3.  
3) Atualiza `oracle_price_update` (quality_score) e hooks `a1_oracle_staleness_guard`.  
4) Testes property (mediana preservada) + e2e sob jitter.  
5) Evidence JSON mostra p95<30s; promote.

---

## 2. Sumário do Product Brief (10 linhas)
1) **NSM**: *Time‑to‑Preço‑Válido* p75 ≤ **0,5 s** (p95 ≤ **0,8 s**).  
2) **KRs**: ≥**95%** decisões com trilha; **CDC p95 ≤ 120s**; **staleness<30s**; **breaking=0**; **INP p75 ≤ 200ms**; **SRM=OK** (quando houver modelo).  
3) **Sequência 0–100%**: PM+Oráculos → Leilões+DEC → FX/CIP+Route → Risco/BCDR → ML v2 → SRE/Plataforma → FE/SDKs → Fecho.  
4) **MVP**: **Mercado de Previsões + Oráculos Regionais**.  
5) **FX/CIP+Route**: no‑arb; multi‑venues; breaker; CLS/pay‑in.  
6) **Dados**: contratos/registry/dbt; auditoria.  
7) **SRE**: SLOs, burn, multi‑região, BCDR; SBOM/chaves.  
8) **Privacidade/On‑chain**: PII off‑chain; EIP‑712/âncoras.  
9) **Governança**: watchers must‑have + Hook A110.  
10) **Precedência**: Instruções ▶ Brief ▶ Catálogos ▶ Domínios.

## 3. `brief_context.yaml` (machine‑readable)
> **Atualize apenas quando o Brief mudar.** Lido **antes** de qualquer épico/tarefa.
```yaml
version: "v2.7"
brief_date: "2025-09-09"
timezone: "America/Bahia"
source: "Product Brief.md"

nsm:
  name: "Time-to-Preço-Válido"
  targets_ms: { p75: 500, p95: 800 }

slos_slas:
  oraculos: { staleness_p95_s: 30, divergence_eps: 1.0 }
  cdc: { lag_p95_s: 120 }
  web: { inp_p75_ms: 200, cls_max: 0.1 }
  apis: { breaking_changes: 0 }
  ml: { psi_max: 0.2, ks_max: 0.1, srm: "OK" }

phases_0_100:
  order: ["PM+Oráculos","Leilões+DEC","FX+CIP+Route","Risco/BCDR","ML v2","SRE/Plataforma","FE/SDKs","Fecho 100%"]
  dependencies: ["Contratos→Oráculos→PM→DEC→FX→SRE/FE/ML"]

guardrails:
  watchers_must_have: [
    "cdc_lag_watch","schema_registry_drift_watch","api_breaking_change_watch",
    "web_cwv_regression_watch","oracle_divergence_watch","slo_budget_breach_watch",
    "capacity_headroom_watch","image_vuln_regression_watch","idp_keys_rotation_watch",
    "model_drift_watch","ab_srm_watch"
  ]
  hook_grammar: "metric@window -> action(s); owner; rollback"

constraints:
  privacy: ["PII off-chain"]
  regions: ["BR-first","LATAM-expand"]

links:
  kb_files: [
    "02-Dominios-A1-PM-Oraculos-FX.md",
    "03-Contratos-e-APIs.md",
    "04-Hooks-Policies-e-Runbooks.md",
    "05-Observabilidade-Testes-e-Evidencias.md",
    "06-Seguranca-Privacidade-Onchain-e-Glossario.md"
  ]
```

### 3.1 Readiness auto‑check (responder na 1ª execução)
```yaml
readiness:
  brief_context: OK|MISSING|STALE
  watchers_must_have: OK|MISSING
  hooks_loaded: OK|ERROR
  contracts_present: OK|MISSING
  statusboards_defined: OK|MISSING
  nsm_targets_ms: { p75: 500, p95: 800 }
```

## 4. Precedência & Fontes de Verdade
**Regra:** Instruções ▶ Product Brief ▶ Catálogo (Product/Feature) ▶ Domínios A1.  
**Falha‑rápida:** `brief_context.yaml` ausente/STALE ⇒ **No‑Go**.  
**Mudanças:** nova versão do Brief ⇒ reextrair Seção 3 + publicar diffs.

## 5. Métricas de Entrada que movem o NSM
| Métrica | Alvo | Dono | Impacto |
|---|---:|---|---|
| **Staleness Oráculo (p95)** | < 30 s | A1 | preço/sinal fresco → decisão mais rápida |
| **CDC lag (p95)** | ≤ 120 s | A2 | dados atualizados → menos retries |
| **FX route p95** | ≤ 1500 ms | A1/A3 | rota rápida → cotação/execução ágil |
| **INP p75** | ≤ 200 ms | A3 | UX responsiva → ciclo curto |
| **Error budget burn** | < 1× | A5 | estabilidade → menos quedas |

> **Obrigatório:** cada entrega declara **qual métrica moverá**, **quanto**, e **como** reduz o NSM.

## 6. Watchers Must‑Have (com donos)
```yaml
- cdc_lag_watch (A2)
- schema_registry_drift_watch (A2)
- api_breaking_change_watch (A3)
- web_cwv_regression_watch (A3)
- oracle_divergence_watch (A1)
- slo_budget_breach_watch (A5)
- capacity_headroom_watch (A5)
- image_vuln_regression_watch (A5)
- idp_keys_rotation_watch (A5)
- model_drift_watch (A4)
- ab_srm_watch (A4)
```
**Governança:** watcher crítico **sem owner** = **No‑Go**; métrica crítica **sem Hook** = **No‑Go**.

## 7. Gramática & Exemplo de Hook A110
```yaml
rule: "metric@window -> action[, action...]"
owner: "A1|A2|A3|A4|A5"
rollback: "yes|manual"
example:
  id: a1_oracle_staleness_guard
  when: "oracle.staleness_ms>30000•5m"
  then: ["switch_to_twap_failover","notify=A1"]
  owner: "A1"
  rollback: "yes"
```

## 8. Go/No‑Go Universal (resumo)
**Go:** NSM p95≤0,8s; staleness p95<30s; CDC p95≤120s; `api_breaking_change=0`; `schema_drift_incompat=0`; (se houver modelo) PSI≤0,2/KS≤0,1; hooks testados (logs/trace); Evidence JSON anexada.  
**No‑Go:** Brief ausente/STALE; watcher crítico sem owner; métrica crítica sem hook; *contract tests* falhando; violação de privacidade.

## 9. Working Backwards (PR‑FAQ mínimo)
**Press‑note (2 linhas):** “Lançamos *PM+Oráculos* com p95<800ms, staleness<30s e auditoria ≥95%, acelerando decisões e liquidez.”

**FAQ (6):** Sucesso? (NSM + métricas de entrada) • Por que agora? (depende de PM/Oráculos) • O que não faremos? (não reduz NSM) • Como tratamos risco? (watchers+hooks/BCDR) • UX alvo? (INP≤200ms, erros claros) • Escala? (multi‑região/DR/contratos/ SLOs).

## 10. Orçamentos (latência & staleness)
| Rota | api‑gw | pm‑svc | decision | fx‑router | ml | edge/cache | **p95 total** |
|---|---:|---:|---:|---:|---:|---:|---:|
| **Cotar PM (sem FX)** | 30 | 155 | 160 | — | 100 | 60 | **505** |
| **Cotar PM + FX** | 30 | 155 | 160 | 170 | 100 | 60 | **675** |
| **Decisão com modelo** | 30 | 80 | 160 | — | 100 | 60 | **430** |
> **Staleness alvo (oráculos):** p95 < 30 s (janela **K** por ativo/região). **CDC** p95 ≤ 120 s.

## 11. Change Control & Evidence JSON
- **ADR** para mudanças de escopo/ordem; **waiver A106** (dados) com prazo/rollback.  
- **Evidence JSON** obrigatório em promoção:
```json
{
  "evidence_version": 1,
  "nsm": { "p75_ms": 490, "p95_ms": 780 },
  "oracles": { "staleness_p95_ms": 24000, "divergence_eps": 0.9 },
  "fx": { "route_latency_p95_ms": 1380, "cip_delta_eps": 0.0008 },
  "tests": { "unit": 200, "property": 50, "e2e": 20, "load": "pass" },
  "hooks_fired": ["a1_oracle_staleness_guard"],
  "statusboards": ["Reliability","Oracles/FX"],
  "artifacts": ["contracts/*.json","openapi/a1.yaml"]
}
```

## 12. Segurança, Privacidade & On‑chain (resumo)
- **PII off‑chain**; logs pseudonimizados; retenção mínima.  
- **APIs:** mTLS, RBAC, WAF; `Idempotency-Key` (POST /bids); `Retry‑After` (429/503).  
- **Supply chain:** SBOM; `high_vulns=0` no gate; rotação de chaves ≤90d (KMS).  
- **On‑chain (opcional):** EIP‑712 (domínio/nonce); âncoras de hash para `pm_clearing_result`; *commit‑reveal* quando cabível.

## 13. Como atualizar este arquivo (3 passos)
1) Mudou a versão do Brief? **Atualize a Seção 3** (`brief_context.yaml`) com `version/brief_date` e metas.  
2) Valide watchers/owners e Go/No‑Go com A1..A5.  
3) Publique um **diff**: o que mudou, por quê, e impacto no NSM/orçamentos.

## 14. Links internos (arquivos da KB)
- **02-Dominios-A1-PM-Oraculos-FX.md** — mecanismos, TWAP/quorum, CIP/route, on‑chain.  
- **03-Contratos-e-APIs.md** — JSON Schemas, OpenAPI, compat/CDC, exemplos.  
- **04-Hooks-Policies-e-Runbooks.md** — A110, degradação com histerese, P1/P2.  
- **05-Observabilidade-Testes-e-Evidencias.md** — dashboards, testes, Evidence JSON.  
- **06-Seguranca-Privacidade-Onchain-e-Glossario.md** — mTLS/RBAC/SBOM/keys, PII off‑chain, EIP‑712, commit‑reveal, glossário.

---
**Concluído (v2.0).** Documento canônico **ouro** com o **Product Engine TURBO**: resultado (Bezos), simplicidade (Jobs), rigor (Knuth) e operação (Perez). **Promova somente com gates verdes e evidência anexada.**

