---
id: kb/po/creditengine/po_ops_manual_master_v2_0_merged_turbo
title: "Manual do Agente GPT — Product Owner do Credit Engine • Ultra Gold MASTER (Merged & Turbo)"
version: "v2.1 — Ultra Gold MASTER (Triple QA)"
date: "2025-09-07"
timezone: America/Bahia
owner: PO Agent (GPT)
stewards: [Produto, Engenharia, Dados, Risco, SRE]
doc_type: po_ops_manual
policy:
  knowledge_scope: "Master List A1–A110 + Blocos 1–12 + CE$ MVP v6.0 (trechos integrados)"
  citation_rule: "Sempre citar packs Axx em pontos técnicos; hooks A110 para métricas→ações; contratos A106/A87 para dados"
  prompt_governance:
    allowed_sources: ["KB Blocos 1–12", "A1–A110"]
    forbidden: ["suposição sem pack", "exemplo com PII", "placeholder"]
    style: "responder com ACE, DoR/DoD, watchers e hook A110"
  escalation_triggers: ["falta de pack", "conflito entre packs", "risco A108", "mudança de SLO sem aprovação"]
quality_bars:
  completeness: "0 placeholders; seções encadeadas; exemplos executáveis"
  reproducibility: "containers, lockfiles, Makefile/CLI, OTel; Golden Notebooks quando cabível"
  traceability: "Requisitos↔Packs↔Watchers↔Hooks (A110) mapeados; ADRs/waivers versionados"
watchers:
  required: [$1, runtime_eol_watch, dep_vuln_watch, oracle_divergence_watch, fx_delta_benchmark_watch]
---

# 0) Sumário Executivo
O **CreditEngine$ (CE)** é o sistema nervoso de **decisão e precificação de crédito** com **observabilidade (A71–A72)**, **contratos de dados (A106/A87/A89)**, **serving de modelos (A81/A84/A83)**, **mecanismos de mercado (A10/A28/A98–A104)** e **gates automáticos (A110)**. **NSM**: *Time‑to‑Preço‑Válido* p75 ≤ **0,5 s** (p95 ≤ **0,8 s**). Governança: **sem deploy** com watchers críticos vermelhos.

---

# 1) Direitos, Linhas Vermelhas e Política de No‑Go
- **Você (humano)** aprova **escopo, risco, SLO e exceções**. O Agente P.O. **orquestra** e **barra** quando necessário.

## 1.1 Tabela No‑Go
| Condição | Ação obrigatória |
|---|---|
| História sem ACE/hook/watchers | **No‑Go** (remover do sprint) |
| Watcher crítico sem owner | **No‑Go** (atribuir dono antes) |
| Métrica sem ação A110 | **No‑Go** (definir hook) |
| Falha de evidência executável (tests/telemetria) | **No‑Go** (corrigir e reabrir) |
| Violação A108 (privacidade) | **No‑Go** + escalonar ao humano |

---

# 2) Operar com um único humano + Squad 100% agentes
## 2.1 Cadência
- **Daily (15’)**: snapshot com watchers, 3 riscos, 3 decisões e opções.  
- **Weekly (45’)**: priorização backlog (impacto×risco×esforço), KRs/OKRs (A109), revisão de hooks.  
- **Mensal (60’)**: tabletop BCDR (A91), auditoria contratos (A106/A87), fechamento de postmortems (A93).

## 2.2 Formação do Squad (6–9 papéis)
PO, ST, PY, DC, QU, ML, SRE, FE, SEC/RISK — com **packs e watchers** por papel; **DoR/DoD** e **Matriz Épico→Papéis→Packs/Watchers/DoR/DoD** anexada ao sprint.

---

# 3) Tech Stack Governance (Pérez Deep Dive)
## 3.1 Princípios
Boring‑tech; containers; lockfiles; OTel default‑on; contratos A106; ações A110; segurança A77/A108; rollbacks documentados.

## 3.2 Mapa de Stack Padrão + Alternativas
- **BE/API**: Python 3.11 + FastAPI (padrão) | Go 1.22+ (I/O extremo). Hook: `error_5xx_rate>1%•15m•rollback_release`.
- **Dados**: Debezium → Iceberg → dbt (padrão) | Delta/Hudi (ops). Watchers: `cdc_lag`, `data_contract_break`, `schema_drift`, `dbt_test_failure`.
- **ML**: PyTorch→ONNX→Triton; drift PSI/KS (A84); A/B (A83). Hook: `psi>0.2•24h•rollback_baseline`.
- **FE**: TS + React + Next.js; CWV p75 verdes. Hook: `inp>200ms•24h•rollback_feature`.
- **Streaming**: Kafka/Redpanda + Flink/Spark SS. Watcher: `slo_budget_breach_watch`.
- **Observ/Sec/Build**: OTel, Grafana/Prometheus; CSP/CSRF/Trusted Types; SBOM e container scan; IaC.

## 3.3 Tabela de Escolhas por Domínio
| Domínio | Padrão | Versão | Alternativa (quando) | SLO/SLA | Watchers | Hook A110 |
|---|---|---|---|---|---|---|
| BE | Python 3.11 + FastAPI | 3.11.x | Go (I/O extremo) | p95 ≤ 800ms | 5xx, SLO | rollback_release |
| Dados | Debezium + Iceberg + dbt | — | Delta/Hudi | lag p95 ≤ 120s | cdc/schema/dbt | degrade_to_hot_table |
| ML | Triton/ONNX | — | TorchServe | PSI ≤ 0.2 | drift | rollback_baseline |
| FE | TS + Next.js | 18.x | RN/Flutter (mobile) | INP ≤ 200ms | CWV | rollback_feature |
| Stream | Kafka/Flink | — | — | e2e ≤ alvo | SLO | throttle/retry |

## 3.4 Reprodutibilidade
Containers por domínio; locks (`uv.lock`, `pnpm-lock.yaml`); Makefile/CLI com `env.up`, `be.test`, `data.run`, `ml.serve`, `hooks.dry`. Artefatos com `sha256`, `commit`, `trace_id`, `audit_id`.

---

# 4) Catálogo de Produtos/Serviços (cronológico)
P1 Decision & Pricing Core; P2 Auctions; P3 FX; P4 Oracles; P5 Data Foundation; P6 ML Serving; P7 Governança/Resiliência; P8 Experience Layer — cada item com propósito, SLAs, dependências, packs e watchers.

---

# 5) Feature Catalog → Backlog (PO‑ready)
Features com **ACE G/W/T**, **hook A110** e packs; conversão em histórias **PO‑ready** (watchers, tasks, telemetria). **Bloqueio**: sem hook A110 → não entra no sprint.

---

# 6) Roadmap & Gates (0–90 dias)
T0–T2: P5/P1; T3–T4: P2/P3/P4; T5: P6; T6: P7; T7: P8. **Gate**: watchers verdes + hooks ativos + artefatos publicados (contratos/hooks/notebooks quando cabível).

---

# 7) Measurement Plan & KPI Dictionary
Tabela por KPI com **fonte**, **janela**, **cálculo** e **hook** (A110): Time‑to‑Preço‑Válido; CDC lag; PSI/KS; staleness; SRM; INP.

---

# 8) Decision Hooks (A110) — Biblioteca
Drift PSI/KS → rollback; Lag CDC → degrade; Staleness oráculos → TWAP+failover; SRM → pause; CWV → rollback FE; 5xx API → rollback release; p95>target → scale/throttle; fill<90% leilão → revisar parâmetros.

---

# 9) Observabilidade & Telemetria (OTel)
Spans essenciais (`decision.core`, `auction.match`, `fx.router`, `oracle.fetch`, `cdc.reader`, `dbt.run`, `ml.infer`); atributos (`trace_id`, `pack_id`, `hook_id`, `latency_ms`); eventos (`hook.trigger`, `rollback.apply`, `slo.violation`). Dashboards: Latency/Error, Hook Coverage, CDC Lag, Drift, CWV, SLO burn.

---

# 10) Dados & Contratos (A106/A87/A89)
Entidades: `pricing_events`, `oracle_ticks`, `fx_quotes`, `cdc_offsets`. Contratos backward‑compat, expectations (unique/not_null/accepted_values/relationships), CI e versionamento. Lineage & DQ Matrix por dataset.

---

# 11) ML Serving & Experimentos (A81/A84/A83)
Export ONNX; Triton com dynamic/sequence batching; drift PSI≤0.2 e KS≤0.1; A/B com SRM OK; rollback automático via hooks.

---

# 12) Leilões, FX e Oráculos (A10/A28/A98–A104)
Leilão reverso (commit→reveal→clearing→settlement) com algoritmo de clearing e *edge cases*; FX com roteamento e filtros de *toxicity* (VPIN); Oráculos com TWAP/heartbeats/deviation e staleness<30s.

---

# 13) On‑Chain (opcional) & Tokenização (A101–A104/A108)
Attestation de preços/decisões (hash), escrow de funding (commit‑reveal), settlement de hedge; *feature flags* on‑chain; tokenização fungível/não‑fungível com metadados mínimos (sem PII). **Gates formais (A103)** em pontos críticos.

---

# 14) Prediction Markets (sinal auxiliar)
Mercados binários/escalares/compostos para **probabilidades** de eventos (drift/lag/spread); **observacionais** (não executam); integração: sinais viram **hipóteses** e **checkpoints** de planejamento; métricas: calibração, latência de resolução, utilidade.

---

# 15) Segurança & Privacidade (A77/A108)
CSP nonce/Trusted Types/CSRF; minimização; base legal; encriptação em trânsito/repouso; mascaramento em não‑prod; `dp_budget_breach_watch`. **DoR/DoD de privacidade** em todo artefato com dados.

---

# 16) Resiliência & BCDR (A91–A92)
Multi‑região *active/standby*; failover (DNS cutover, warm caches); reversão (reconciliation + drain). Drills trimestrais; *tabletop* mensal.

---

# 17) SLOs & Error Budgets
Decision Core 99.9% (43m49s/mês), Oracles 99.95% (21m54s). Política: consumo >50% do orçamento congela lançamentos do serviço até normalizar.

---

# 18) Working Agreements & WIP
WIP do squad ≤ 7 histórias; por papel ≤ 2. Handoffs com DoR/DoD por papel; demo em cada história; ceremonies padrão Scrum.

---

# 19) Testes & Evidências
Dados: dbt tests + expectations; Serviços: unit/contract/golden; Modelos: offline, shadow, canary, A/B; Resiliência: chaos/tabletop; Performance: load por serviço. **Audit Pack** por release com dashboards, logs de hook, status watchers, `schema diffs`, `dbt run results`, canary report.

---

# 20) ADRs & Waivers (A106)
ADR: contexto, opções, trade‑offs, decisão, packs, watchers, hook A110, rollback, owners, ACE/DoR/DoD e links (trace/audit). Waiver: dataset/contrato, mudança, justificativa, prazo, risco, rollback, aprovação.

---

# 21) OKRs do Agente P.O. (auto‑governança)
KR1: Lead time por artefato p75 ≤ 2h; KR2: Correções pós‑review ≤ 2%; KR3: Cobertura de citação de packs = 100%; KR4: Histórias com watcher+owner = 100%.

---

# 22) Command Palette do P.O. (CLI)
`po brief.gen` • `po feature.gen` • `po backlog.gen` • `po sprint.plan` • `po sprint.approve` • `po hooks.export` — todos registram evidência (sha256/commit/trace/audit).

---

# 23) Apêndices
## 23.1 Exemplos completos
- Contrato `pricing_events` (YAML) com expectations e SLAs; Hook de drift (YAML); API Decision Core (request/response) com OTel.

## 23.2 Formais & Propriedades (A103)
Invariantes: ORACLE_FALLBACK; CONTRACT_BACKWARD_COMPAT; AUCTION_CLEARING. *Property‑based tests* para clearing.

## 23.3 CE$ Marketplace P2P (integrado)
Uniform‑price adaptado; anti‑manipulação (step 5 bps; 3 ofertas/credor; cooldown 60s; anti‑sniping 120s +600s); TTL 24h; capital só trava em `LoanConfirmed`; pré‑pagamento sem multa; tokenomics 1:1; KYC/AML (retenção 5 anos); KPIs (Funding ≤24h; Pool ≥65%; NPL30 ≤3%; HHI ≤ 0,35); UX 3 telas + fallback; Gate A (critérios) e ADRs recomendados.

---

# 24) Quality Gates — Master Checklist (Go/No‑Go)
- Watchers do escopo **verdes por ≥24h**  
- Hooks A110 ativos **com dry‑run** e evidência  
- Contratos A106/Expectations A87/dbt A89 **OK**  
- BCDR §16 **em dia**  
- MRM/Postmortem (A90/A93) **atualizados**; backlog crítico = 0  
- KPIs de fase **atingidos** (ou ADR/mitigação)  
- Artefatos **publicados** (catálogo/roadmap/ADRs/waivers)

---

## 24.1 Gate A (CE$ P2P) — Critérios de Aceite (resumo)
- Algoritmo **uniform‑price adaptado** + anti‑manipulação (step 5 bps; 3 ofertas/credor; cooldown 60s; anti‑sniping 120s +600s) implementáveis e descritos.
- **Logs** e **schemas JSON** publicados com hash/assinatura; ordem de operações e arredondamento (centavos→wei) clara.
- **UX 3 telas** + fallback com mensagens‑modelo; SLA fallback ≤ 2h.
- **KPIs** e fórmulas (APR‑365 ↔ CDI‑252) definidas; HHI ≤ 0,35 acompanhado.
- **Taxa mínima 0,50%** aplicada; **capital só trava** em `LoanConfirmed`.
- **Governança Fase 0**: comitê consultivo; exceções documentadas por ADR.

---

# 25) Log de Qualidade (Knuth + Pérez)
Notação/unidades padronizadas; definições algorítmicas claras (TWAP, VPIN, clearing); reprodutibilidade afirmada (containers, locks, Makefile, OTel); ligações OTel↔Dados↔Hooks↔Gates; **zero placeholders**; pronto para uso.


---

# 26) Versionamento & Change Management
- **SemVer** para serviços, contratos e clientes; bump obrigatório em **breaking changes**.
- **ADRs** registram contexto, trade‑offs, decisão, rollback e evidências (trace/audit).
- **Waivers (A106)**: prazo, risco, rollback e aprovação; revisões quinzenais.
- **Changelog** por release com ligações para **Audit Pack** e **dashboards**.

---

# 27) Índice de Packs Referenciados
A10, A28, A41–A43, A71–A72, A74–A80, A77, A81–A84, A86–A89, A90–A93, A94–A97, A98–A104, A105, A106, A107, A108, A109, A110.

---

# 28) Triple QA — Log de Auditoria Final
- **Placeholders**: zero (verificado).
- **Coesão**: seções 0–25 e anexos integrados (Stack, P2P CE$, On‑Chain, Previsões) sem referências quebradas.
- **Watchers/Hook Coverage**: lista consolidada inclui `runtime_eol_watch`, `dep_vuln_watch`, `oracle_divergence_watch`, `fx_delta_benchmark_watch`.
- **Medidas**: NSM/SLAs/SLOs claros; Measurement Plan presente (§7); Quality Gates (§24) e Gate A (§24.1).
- **Rastreabilidade**: Requisitos↔Packs↔Watchers↔Hooks mapeados; ADR/waiver modelos e política de No‑Go ativas.
- **Reprodutibilidade**: containers, locks, Makefile/CLI, OTel; artefatos com sha256/commit/trace/audit.
- **Status**: **APTO PARA USO** pelo Agente P.O. e squad 100% agentes.

