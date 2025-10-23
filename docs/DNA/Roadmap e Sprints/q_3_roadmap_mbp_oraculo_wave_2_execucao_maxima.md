# Q3 Roadmap — MBP + Oráculo (Wave 2) — Execução Máxima (S13–S18) — **v2 com melhorias do comitê**

Contexto: Masterplan v9 (Ultra‑Expanded). Este Q3 cobre **S13–S18** e entrega o **R‑2.0 (Beta Aberto Controlado)** com: **Oráculo 2.0** (failover econômico + reputação dinâmica), **MBP v2** (mercados categórico/escalar, **ordens limite/TIF**, **fees dinâmicos v1.2 + halts**), **Liquidez & Creator Studio v1**, **PWA mobile‑first**, **STRIDE completo** e **bug bounty**. Documento **sem prompts**.

Comitê envolvido nesta edição: Vitalik (incentivos/fees/limites), Jobs (UX/DS hi‑fi), Lamport (TLA+/halting), Juels (oráculo/atestações/auditoria), Chitra (qualidade de mercado/liquidez/risco), Forsgren (SRE/SLO/burn-rate), Moxie (segurança/abuso).

---

## 0) Objetivo macro e KRs do Q3 — **atualizados**
**Objetivo macro:** levar o MBP ao **Beta Aberto robusto**, com oráculo redundante (failover + reputação), **catálogo completo** de mercados, **qualidade de mercado mensurável**, UX de produção, **governança operacional pública** e segurança reforçada.

**KRs (atingidos até o corte R‑2.0):**
- **Oráculo 2.0**: `staleness p95 ≤ 18s`, `divergence p95 ≤ 0,5%`, failover < 1% real; **reputação dinâmica** ativa; **política de rotação de chaves por fonte (90d)** publicada; **logs de roll do failover assinados** e exportados.
- **Qualidade de mercado**: spread p95 ≤ 2,0%; slippage p95 ≤ 1,5% (≤ CE$100); **depth@2% p50 ≥ CE$50k** top‑20; **curvas‑alvo por categoria** (σ, depth) e **limites de OI por fase de vida do mercado** publicados.
- **Liquidez/Creators**: creators/semana ≥ 120; TVL ↑ ≥ 40% vs Q2; churn LP ≤ 15%/mês; **política de incentivos de LP (cliff/decay)** e **anti‑sybil de creators** vigentes.
- **Plataforma/UX**: PWA mobile‑first; **Design System** publicado; **protótipos hi‑fi completos** para categórico/escalar e telas de limit/TIF; **skeleton/empty states** e **microcopy de halts** (PT‑BR/ES); INP p75 ≤ 200ms; WCAG 2.2 AA nas jornadas.
- **Operação/SRE**: uptime ≥ 99,9% (30d); burn < 0,5×; 0 P1 no mês anterior; **monitoria sintética multi‑região (2 provedores)**; **ORR definido como gate** do Beta Aberto; baseline mensal publicado na status page.
- **Segurança**: **bug bounty** live; checklist anti‑phishing (OAuth/PKCE) e **rate‑limits por endpoint v2** publicadas.

---

## 1) Plano de Sprints (S13→S18) — **com melhorias incorporadas**

### S13 — Expansão de Fontes, Cobertura e Capacidade (Semanas 1–2)
**Objetivo:** ampliar cobertura BR/LatAm e preparar o throughput para picos do Beta Aberto.

**Entregáveis (atualizados):**
- **Adapters Tier‑2** e consolidadores por país/tema; budgets por domínio; storage quente (90d)/frio (≥1y).  
- **Métricas de cobertura** por categoria/país; staleness/latência p95 por domínio.  
- **Capacity Planning v1** para ≥ **2k eventos/min** pico; headroom ≥ 30%; plano de custos.  
- **SLO waterfall (draft)** atualizado.  
- **Dataset BR/LatAm consolidado**.  
- **Política de rotação de chaves por fonte (90d)** (`docs/oracle/key_rotation_policy.md`) + playbook de rotação.

**DoD (S13):** cobertura topo ≥ 95%; `staleness_global p95 ≤ 18s` (staging); capacity v1 aprovado por Forsgren; **key rotation policy publicada**; evidence `S13_coverage/`.

---

### S14 — Failover Econômico v1.5 + Roll Policies (Semanas 3–4)
**Objetivo:** fallback TWAP/median robust com **histerese**, trilha auditável e **não‑arbitragem** na troca de modos.

**Entregáveis (atualizados):**
- Automação de failover (consenso↔fallback) com **histerese**; rollforward/rollback.  
- **Provas empíricas de não‑arbitragem**; limites superiores de erro.  
- **Logs de roll assinados** (hash + assinatura) publicados em `out/evidence/S14_failover/roll_logs/`.  
- Watchers dedicados; runbook de operação; **shortlist de auditores independentes** anexada (`docs/audit/custody_auditors_shortlist.md`).

**DoD (S14):** failover real < 1%; desvio médio em fallback ≤ 1%; **roll logs assinados**; evidence `S14_failover/`.

---

### S15 — Reputação Dinâmica de Fontes & Pesos Adaptativos (Semanas 5–6)
**Objetivo:** reduzir TTF e disputas com **pesos dinâmicos** e **alarmes de drift**.

**Entregáveis (atualizados):**
- Engine `services/oracle/reputation/*` com `trust_f(t)`; smoothing; limites de variação/semana; penalidade por correções tardias.  
- Painel “Source Reputation”; diffs semanais auditáveis.  
- **Alarmes de drift** (mudança abrupta de `trust_f`) + runbook; ligação com watchers de consenso.  
- **Curvas‑alvo por categoria** (`docs/econ/market_curves_targets_q3.md`): σ alvo, depth@2% alvo; **limites de OI por fase de vida do mercado** (lifecycle: criação/early/mid/late).

**DoD (S15):** TTF ↓ ≥ 25% vs Q2; disputas ↓ ≥ 50%; `staleness p95 ≤ 18s`; **curvas‑alvo publicadas**; evidence `S15_reputation/`.

---

### S16 — MBP v2: Categórico/Escalar + Limit/TIF + Fees v1.2 + Halts (Semanas 7–9)
**Objetivo:** lançar catálogo completo e mecanismos pró‑nível com UX de produção.

**Entregáveis (atualizados):**
- **Mercados categóricos/escalars**; validações; projeção p/ simplex; payouts; fechamento seguro.  
- **Orders/Matching**: limite/mercado; **TIF (GTC/IOC)**; **batcher anti‑sniping**; slippage guard.  
- **Fees v1.2** com **calibração contínua**: 
  • **_Sweeps_ semanais automatizados** dos `k1/k2/k3` usando dados do **shadow** de Q2;  
  • rollback automático se Δ>2σ;  
  • **relatório semanal** `out/reports/fees_calibration_Q3/week_*.pdf`.
- **Volatility Halts**: FSM `Warn→Soft→Hard→Recovery` com histerese; banners e microcopy.  
- **UX/DS hi‑fi**: **protótipos hi‑fi completos** para fluxos **categórico/escalar** (criar→preview→publicar), **telas de limit/TIF**, **skeleton/empty states** e **microcopy de halts** (PT‑BR/ES).  
- **Market Quality**: regras Prometheus (spread/slippage/depth@2%).

**DoD (S16):** spread p95 ≤ 2%; slippage p95 ≤ 1,5%; depth@2% p50 ≥ CE$50k; INP p75 ≤ 200ms; WCAG AA; **relatório de calibração #1** publicado; evidence `S16_mbp_v2/`.

---

### S17 — Liquidez & Creator Studio v1 (Semanas 10–11)
**Objetivo:** fortalecer TVL e qualidade de mercados com incentivos e lint.

**Entregáveis (atualizados):**
- **Vaults de LP** (add/remove/shares/auto‑rebalance/cooldown) + PnL.  
- **Política de incentivos de LP (cliff/decay)** publicada (`docs/econ/lp_incentives_policy_q3.md`); cofre de fees; anti‑wash‑liquidity.  
- **Creator Studio v1**: templates; preview; lint; **anti‑sybil de creators** (limiares de criação, reputação, detecção de clusters) com critérios e apelação.  
- Painéis: creators/semana; qualidade por categoria; TVL; churn LP.

**DoD (S17):** creators ≥ 120/sem; TVL +40% vs Q2; churn LP ≤ 15%/mês; **policy de LP e anti‑sybil ativas**; evidence `S17_liquidity_creators/`.

---

### S18 — Beta Aberto Controlado + PWA + Bug Bounty + STRIDE (Semanas 12–13)
**Objetivo:** abrir o **Beta Aberto** com segurança e governança de operação públicas.

**Entregáveis (atualizados):**
- **PWA**: caching; fila de ordens; banners de halt; modo leitura; INP p75 ≤ 200ms.  
- **Rollout**: flags; canário 0,5→10%; watchers; **Status Page** com **error budgets por serviço**, **baseline mensal** e incident reports.  
- **Monitoria sintética multi‑região (2 provedores)** para API e web; relatórios arquivados.  
- **ORR (Operational Readiness Review)** como **gate** do Beta (checklist publicado).  
- **Bug bounty** em produção; STRIDE revisado; checklist **anti‑phishing** (OAuth/PKCE) e **rate‑limits por endpoint v2** (`docs/platform/api_v2_rate_limits.md`).  
- **Incident drill** antes do corte R‑2.0.

**DoD (S18):** 30 dias sem P1; uptime ≥ 99,9%; burn < 0,5×; **ORR aprovado**; **monitoria sintética** ativa; evidence `S18_beta_open/`.

---

## 2) Release Train de Q3 — **R‑2.0 (Beta Aberto)**
**Cut‑line:** após S18, com **Oráculo 2.0**, **MBP v2**, **Liquidez/Creators v1**, **PWA**, **bug bounty**, **SLO waterfall v1**, **monitoria multi‑região** e **ORR**.

**Go/No‑Go (R‑2.0) — atualizado:**
- [ ] `staleness p95 ≤ 18s` e `divergence p95 ≤ 0,5%` por 14 dias.  
- [ ] spread p95 ≤ 2%, slippage p95 ≤ 1,5%, depth@2% p50 ≥ CE$50k; **curvas‑alvo por categoria publicadas**.  
- [ ] creators ≥ 120/sem; TVL +40%; churn LP ≤ 15%/mês; **policy de LP e anti‑sybil** vigentes.  
- [ ] PWA (INP p75 ≤ 200ms); WCAG AA; status page com **error budgets por serviço** e **baseline mensal**.  
- [ ] **Monitoria sintética** operante; **ORR aprovado**; 0 P1 no mês; burn < 0,5×.  
- [ ] Evidence S13..S18 assinados; docs públicas atualizadas; **rate‑limits por endpoint v2** vigentes.

---

## 3) Observabilidade & SRE — reforços Q3
- **Waterfall p95**: ingest 150ms; aggregation 200ms; consensus 400ms; API 180ms; TTFB 200ms; INP 200ms.  
- **Regras Prometheus**: spread/slippage/depth; staleness/divergence; burn‑rate 1h/6h/24h; **alarmes de drift de `trust_f`**; saturação/quotas; **ORR gate**.  
- **Status Page**: budgets por serviço; **baseline mensal**; incident reports; changelog.  
- **Monitoria sintética multi‑região** (2 provedores) com relatórios arquivados.

---

## 4) Segurança, Privacidade e Compliance — reforços
- **Bug bounty** (produção); divulgação responsável.  
- **Checklist anti‑phishing** (OAuth/PKCE), **origin isolation**, CSP/Trusted Types strict; **rate‑limits por endpoint v2**.  
- **Privacidade (LGPD)**: revisão trimestral; DSRs; anonimização; appeals.  
- **Compliance**: termos/privacidade; trilhas; preparação para KYC/AML (execução plena em Q4/S20).

---

## 5) Dados, Backtests e Calibração — reforços
- **Shadow backtests** de Q2 alimentando **_sweeps_ semanais** de `k1/k2/k3` (relatório e rollback).  
- **Experimentos**: thresholds de halts (soft/hard) por categoria; impacto em spread/slippage/volume.  
- **Curvas‑alvo por categoria** e **limites de OI por lifecycle** publicados e monitorados.

---

## 6) Riscos principais & Mitigações (atualizado)
1) **Halts excessivos** → histerese + janela de confirmação; monitor de FP; rollback de thresholds.  
2) **Gaming da reputação** → limites de variação; penalidades; auditoria amostral; alarmes de drift.  
3) **Déficit de depth** → incentivos LP (policy) + Creator Studio com lint/allowlist.  
4) **Perf web/API** → budgets; monitoria sintética; drill de incidentes; modo leitura.  
5) **Abuso/phishing** → CSP strict; OAuth/PKCE reforçado; rate‑limits por rota; appeals.

---

## 7) Entregáveis do Repositório (Q3) — **acrescidos**
- **Código**: reputação (`services/oracle/reputation/*`), failover com **roll logs assinados**, _sweeps_ de fees, halts com histerese, anti‑sybil de creators, monitoria sintética, rate‑limits por endpoint v2.  
- **Docs**: `docs/oracle/key_rotation_policy.md`, `docs/audit/custody_auditors_shortlist.md`, `docs/econ/market_curves_targets_q3.md`, `docs/econ/lp_incentives_policy_q3.md`, `docs/platform/api_v2_rate_limits.md`, `docs/runbooks/{failover.md,halts.md,incident_drill.md}`.  
- **Evidence**: incluir `roll_logs/*`, `fees_calibration_Q3/*`, `monitor_synthetic_reports/*`, `curves_targets/*`, `anti_sybil_creators/*` em `out/evidence/S13..S18`.

---

## 8) Comunicação e Investor Update (Q3)
- **Mensagem‑chave:** “Produto **robusto** para Beta Aberto: oráculo com failover e reputação, mercados completos, **qualidade/liq** sob metas explícitas e **operação transparente** (status + ORR + monitores multi‑região).”  
- **Métricas a reportar:** staleness/divergence; spread/slippage/depth; creators/semana; TVL/churn LP; uptime/burn; drill; bug bounty; _sweeps_ de fees; ORR.

---

## 9) Pós‑Q3 → Preparação para Q4 (R‑3.0, GA)
- **TLA+ e auditorias** (S19): formalizar transições de failover e **liveness sob halts repetidos**; bound de filas/ordens no model checking; auditoria de custódia #1.  
- **KYC/AML e payouts** (S20): integrar/avaliar; appeals; privacy review.  
- **SRE/DR/Chaos** (S21): DR 2×; chaos‑tests; capacity v2; DORA.  
- **Plataforma pública** (S22): API/SDK v2 final; status v2; parceiros piloto.  
- **Canário e GA** (S23–S24): reconciliação D+1; ancoragem externa; 30+ dias verdes.

---

**Conclusão:** Q3 v2 mantém o corte **R‑2.0** e adiciona políticas/artefatos críticos (rotação de chaves, logs assinados, curvas‑alvo/OI por lifecycle, _sweeps_ de fees, incentivos LP e anti‑sybil, monitores multi‑região e **gate ORR**), elevando robustez sem estourar prazo.

