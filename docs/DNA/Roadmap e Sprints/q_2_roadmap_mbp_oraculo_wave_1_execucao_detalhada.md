# Q2 Roadmap — MBP + Oráculo (Wave 1) — Execução Detalhada — **v2 com melhorias do comitê**

Contexto: Masterplan v9 (Ultra‑Expanded). Este Q2 cobre **S7–S12** e entrega **R‑1.0** (Oráculo 1.5 + MBP v1 binário + Status/API públicas v1 + Antimanipulação v1), pronto para **Beta Fechado**. **Todas as melhorias solicitadas pelo comitê foram incorporadas abaixo sem alterar o cut‑line.**

---

## Δ Deltas incorporados em Q2 (resumo)
1) **Build gates (CI)** com **invariantes I1..I7** e **harness de append‑only (Merkle)**.
2) **Limites de exposição** publicados (por mercado/usuário) e **kill‑switch por categoria** com runbook e testes.
3) **Status page** com **monitor externo**, link de **abuso/appeals** e **template público de post‑mortem**.
4) **A11y/UX**: microcopy final (PT‑BR/ES) e **acessibilidade de teclado/ARIA** nas telas de **Disputes** e **Status**.
5) **Shadow backtests** da função de **fees** (sem efeito no preço) + **relatório semanal** para embasar Q3.

---

## 0) Objetivos e Resultados‑chave de Q2 (ajustados)
**Objetivo macro:** provar tecnicamente o oráculo BR/LatAm 0→1 em produção **e** operar o MBP binário com governança de risco (exposição/kill‑switch), transparência pública e trilhas de evidências, reduzindo risco tecnológico e operacional para Q3.

**KR até R‑1.0:**
- Oráculo: `staleness p95 ≤ 20s`, `divergence p95 ≤ 1,0%` (meta interim), uptime ≥ 99,5% (Q2).  
- Resolução automática: ≥ 95% dos mercados binários resolvidos sem intervenção; `override ≤ 5%`.  
- Antimanipulação v1: ataques simulados não elevam `divergence p95 > 1%` e `staleness p95 > 20s`.  
- **Risco/mercado**: **limites de exposição publicados** (mercado/usuário) e **kill‑switch por categoria operacional**.  
- Transparência: **status público** (incl. **monitor externo**, **error budgets agregados**, **abuso/appeals**, **post‑mortem template**) e **API v1** + **SDK verify**.  
- Confiabilidade: **0 P1** por 14 dias consecutivos antes do corte; painéis de integridade publicados. 

---

## 1) Plano de Sprints (S7→S12) — com melhorias

### S7 — Modelo de Evento & Normalização (Semana 1–2)
**Objetivo:** definir o contrato canônico do oráculo e normalizar entradas multi‑idioma, com cadeia de evidências e assinatura de lotes **com prova simples de append‑only**.

**Entregáveis (atualizados):**
- Esquema canônico `contracts/data/event_v1.json`.
- Normalizador `services/oracle/normalizer/*` (canonização PT/ES, datas ISO, entidades, equivalenceHash).
- Dedup inicial (hash + heurística lexical).
- **Writer de lote com Merkle tree (`B_t`) + timestamp + assinatura Ed25519** e **harness de verificação append‑only** (gera `proof_append_only.json`).
- ADRs: `ADR-Event-Model.md`, `ADR-Event-Signing.md` (inclui política de relógio e drift).
- Painel “Oracle Pipeline”; regras Prometheus de frescor por fonte; **teste automático de drift NTP**.

**DoD:** parsers 100% em goldens; p95 normalização ≤ 150ms; evidence `out/evidence/S7_event_model/` **contendo `proof_append_only.json`**.

---

### S8 — Adapters Tier‑1 BR/LatAm & Health (Semana 3–4)
**Objetivo:** integrar ~15 fontes (APIs/RSS/HTML) com idempotência, retries, rate‑limits e health por fonte, respeitando robots/ToS.

**Entregáveis (atualizados):**
- Adapters com DSL; idempotência; retries; rate‑limit; circuit breaker; compliance robots/CSP.
- Health endpoints por fonte; painel “Oracle Sources”.
- Política **nível‑0** (rascunho) e **segregação de funções** no pipeline (rodízio entre **2 operadores**; logs assinados).

**DoD:** staleness p95 por‑fonte ≤ 15s (staging); falha isolada não derruba pipeline; evidence `S8_sources_health/`.

---

### S9 — Consenso v1 (2/3 + median) & Watchers (Semana 5–6)
**Objetivo:** consolidar consenso jornalístico e ativar watchers bloqueantes, **com build gates de invariantes**.

**Entregáveis (atualizados):**
- Engine `services/oracle/consensus/v1/*` (estados, quorum 2/3, mediana ponderada por `trust_0`).
- Watchers: staleness global, divergence por categoria, uptime; painel “Oracle Integrity v1”.
- **Build gates (CI) executando invariantes I1..I7 (safety)** como pre‑checks; falha de gate bloqueia merge.
- ADR: `ADR-Consensus-v1.md`.

**DoD:** `divergence p95 ≤ 1%`; finalização ≤ 90s; **CI verde com gates de invariantes ativos**; evidence `S9_consensus_v1/`.

---

### S10 — MBP v1: Settlement Binário + Disputa v1 (Semana 7–8)
**Objetivo:** ligar oráculo ao MBP binário e automatizar resolução/payout, **publicando limites de exposição** e **A11y/UX completas nas telas de Disputes**.

**Entregáveis (atualizados):**
- Settlement binário; ledger; reconciliação D+1.
- Disputa v1: contest window; stake; override auditado; **microcopy final PT‑BR/ES**; **acessibilidade de teclado/ARIA** (WCAG AA) para fluxos de disputa.
- **Limites de exposição publicados:** documento `docs/econ/exposure_policy_q2.md` (mercado/usuário) + validações no backend para MBP v1.
- Painel “Settlement & Disputes”.

**DoD:** ≥ 95% auto‑resolução; override ≤ 5%; **A11y (teclado/ARIA) validada**; evidence `S10_end_to_end_settlement/`.

---

### S11 — Antimanipulação v1 + Simulador (Semana 9–10)
**Objetivo:** elevar resiliência contra spam/poisoning, **habilitando kill‑switch por categoria com runbook** e testes.

**Entregáveis (atualizados):**
- Guardas: outlier; semantic‑dedup; clusterização; **kill‑switch por categoria** (API interna + flag de runtime + banner na UI).
- Simulador de ataques; KPIs; **runbook de kill‑switch** (`docs/runbooks/kill_switch_category.md`).
- Painéis de ataque; relatório público no evidence.

**DoD:** sob ataques simulados, `divergence p95 ≤ 1%` e `staleness p95 ≤ 20s`; **kill‑switch testado (ativação/reversão) em staging**; evidence `S11_attack_sims/`.

---

### S12 — Transparência Pública v1 (Status, API v1, SDK v0) (Semana 11–12)
**Objetivo:** expor o estado do oráculo com **monitor externo**, **abuso/appeals**, **post‑mortem template** e **shadow backtests** de fee (sem impacto de preço).

**Entregáveis (atualizados):**
- **Status público**: staleness/divergence/uptime; **monitor externo third‑party** ativo; **link de abuso/appeals**; **template de post‑mortem público** (`docs/public/postmortem_template.md`); **error budgets agregados**.
- **API v1** estável; quotas/chaves; webhooks HMAC; docs e exemplos.
- **SDK v0 (read/verify)**.
- **Shadow backtests**: pipeline que reprocessa trades/telemetria sob a função de fee v1.2 em modo sombra; relatório **semanal** `out/reports/fees_shadow_Q2/week_*.pdf`.

**DoD:** API p95 ≤ 200ms; **monitor externo reportando “UP” por 7 dias**; **primeiro relatório semanal de shadow backtest publicado**; evidence `S12_api_status/`.

---

## 2) Release Train de Q2 — **R‑1.0 (Beta Fechado)**
**Cut‑line:** após S12, com watchers estáveis, status público ativo e resolução binária automatizada.

**Go/No‑Go (atualizado):**
- [ ] `staleness p95 ≤ 20s`, `divergence p95 ≤ 1%` por 7 dias.
- [ ] ≥ 95% auto‑resolução; 0 P1 por 14 dias.
- [ ] Status page ativa com **monitor externo**, **abuso/appeals** e **post‑mortem template**.
- [ ] **Política de exposição** publicada e **kill‑switch por categoria** testado em staging.
- [ ] Evidence bundles S7..S12 assinados; painéis públicos.
- [ ] **Relatório semanal #1 de shadow backtests** disponível.

**Rollout do Beta Fechado:** convidados; termo de uso; feedback estruturado; limites de mercados/volume; observabilidade reforçada.

---

## 3) Observabilidade, SRE e Operações em Q2 (ajustes)
- **SLO waterfall p95:** ingest ≤150ms; agg ≤200ms; consenso ≤400ms; API ≤200ms.  
- **Monitor externo** do status; **alertas de burn‑rate** (1h/6h/24h); **MTTR p95 ≤ 6h** (Q2).  
- **DR**: backup horário; restore test 1×; RPO≤10m, RTO≤45m (Q2). 

---

## 4) Segurança, Privacidade e Compliance (reforços)
- **CSP/Trusted Types strict** desde a PWA; OAuth2+PKCE/HMAC; rotação de chaves 90d.  
- **LGPD**: PII mínima (lista de espera/beta); DSRs; **link de appeals** no status.  
- **Pentest interno leve** em Q2; bug bounty ativa em Q3.

---

## 5) RACI/Streams e WIP (inalterado)
- **Streams**: Oráculo (S7–S9, S11, S12), MBP (S10), Plataforma (S12).  
- **Dono por sprint**: S7 Oráculo; S8 Oráculo; S9 Oráculo+SRE; S10 MBP+Produto/UX; S11 Oráculo+Segurança; S12 Plataforma+DevRel.  
- **WIP**: máx. 2 sprints simultâneas.

---

## 6) Riscos de Q2 e Mitigações (ajustados)
1) Mudança de layout → validadores + fallback; correção 24–48h.  
2) Divergência persistente > 1% → ajuste `trust_0` + triagem temporária auditada.  
3) Disputas frívolas → depósito mínimo + heurística anti‑spam.  
4) Falhas API → WAF/rate‑limits; modo leitura; health externo.  
5) Dados/PII → isolamento/rotação/notificação/RCA; **template de post‑mortem** público.

---

## 7) Entregáveis do Repositório (Q2) — **acrescidos**
- Código: (`S7`) writer + **harness append‑only**; (`S9`) **CI gates de invariantes I1..I7**; (`S10`) **exposure policy** + validações; (`S11`) **kill‑switch categoria** + runbook; (`S12`) **monitor externo** + **shadow backtests**.
- Docs: `docs/econ/exposure_policy_q2.md`, `docs/runbooks/kill_switch_category.md`, `docs/public/postmortem_template.md`, `docs/public/status_api_v1.md` (abuso/appeals), ADRs S7..S12.
- Evidence: incluir em cada bundle artefatos dos deltas (ex.: `proof_append_only.json`, `ci_gates_report.json`, `exposure_policy.pdf`, `kill_switch_test.log`, `monitor_external_report.json`, `fees_shadow_report.pdf`).

---

## 8) Comunicação e Investor Update (ajustes)
- Mensagem‑chave: “Oráculo verificável + resolução automática **com governança de risco e transparência operacional** (monitor externo, appeals, post‑mortem)”.
- Métricas: staleness/divergence, % auto‑resolução, disputas, uptime, incidentes/tempo de resposta, **policy de exposição e kill‑switch**.

---

## 9) Pós‑Q2 (preparação para Q3) — reforçado
- Consolidar **Tier‑2 fontes** e metas de cobertura (S13).  
- Preparar **reputação dinâmica** (S15) com pesos iniciais derivados dos dados de Q2.  
- Usar **shadow backtests** para estimar {k1,k2,k3} e cenários de halts; relatório final de Q2 como insumo para S16.

---

**Conclusão:** Q2 v2 mantém o corte **R‑1.0** e adiciona controles críticos (gates formais, exposição/kill‑switch, transparência operacional, A11y, e backtests sombra) sem estourar prazo. Pronto para execução e reporte."}]}

