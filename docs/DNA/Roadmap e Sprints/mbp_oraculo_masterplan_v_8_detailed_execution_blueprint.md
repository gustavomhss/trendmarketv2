# MBP + Oráculo — Masterplan v9 (Ultra‑Expanded, 10× Depth / 20× Volume)

Comitê: Vitalik Buterin (lead, criptoeconomia/governança), Steve Jobs (produto/UX), Leslie Lamport (verificação formal/TLA+), Ari Juels (oráculos/segurança), Tarun Chitra (mecanismos/liquidez/risco), Nicole Forsgren (SRE/medição), Moxie Marlinspike (segurança/abuso). Facilitador/redação: GPT‑5 Thinking.

> Status do comitê: **Confiança 9,8/10**. Este masterplan consolida **todos** os deltas anteriores e aprofunda cada área com especificações técnicas, critérios de aceite operacionais e artefatos padronizados **sem prompts**. 

---

## PARTE I — Visão, Âncoras e North Star
### 1. Objetivo final (DoD 110%)
MBP público para BR/LatAm com **oráculo próprio 0→1**, catálogo de mercados **binário/categórico/escalar**, **ordens limite/TIF**, **fees dinâmicos** calibrados, **vaults LP**, **resolução/disputa** integrada ao oráculo, **PWA mobile‑first**, **API/SDK v2**, **KYC/AML & payouts**, **SRE** com **status page e error budgets por serviço**, **verificação formal** (incl. halts sob semi‑sincronia), **ancoragem externa** das provas e **30+ dias verdes pós‑GA**.

### 2. Princípios
1) **MBP‑first** (nenhum SKU financeiro fora do MBP antes do Gate).  
2) **Transparência mensurável** (SLAs públicas de oráculo e qualidade de mercado).  
3) **Segurança por desenho** (assina‑tudo, minimização de dados, CSP strict, verificação formal).  
4) **Confiabilidade com gates** (error‑budget governa rollout, halts graduais, DR).  
5) **Evolução com evidência** (evidence bundles por sprint; ADRs, métricas e dashboards versionados).

### 3. MBP Maturity Gate (bloqueante)
- **Adoção/Receita**: MAU ≥10k; DAU/MAU ≥22% (60d); D30 ≥35%; creators ≥120/sem; take‑rate 1,5–3,0%; volume p50 ≥ CE$500k/dia.  
- **Mercado**: depth@2% p50 ≥ CE$75k; p10 ≥ CE$35k; spread p95 ≤2%; slippage p95 ≤1,5% (≤CE$100).  
- **Oráculo**: staleness p95 ≤20s; divergence p95 ≤0,5%; uptime ≥99,9% (60d); failover <1% real.  
- **SRE**: lat p95 ≤800ms; INP p75 ≤200ms; burn <0,5×/30d; 0 P1/60d; DR RPO≤5m/RTO≤30m (2×).  
- **Segurança**: 2 pentests sem críticos; 0 PII; disputas p95 ≤72h.  
- **Rollout governance**: watchers A110; kill‑criteria (staleness>30s/48h; divergence>1%/24h; burn>1×/24h) ⇒ freeze/rollback.

---

## PARTE II — Oráculo BR/LatAm (Especificação 0→1)
### 4. Fontes e Cobertura
- **Tier‑0 (primárias)**: Diários oficiais, agências de governo, tribunais eleitorais, IBGE/Bacen, reguladores setoriais, árbitros esportivos oficiais.  
- **Tier‑1 (nacionais)**: Grandes jornais/TV/radio com histórico de correção; APIs pagas quando disponíveis.  
- **Tier‑2 (regionais/LatAm)**: Portais regionais confiáveis (ES/PT), agências LATAM; boletins setoriais (energia, saúde, transporte).  
- **Matriz de cobertura** por categoria (política, macro, clima, esportes, segurança pública, cultura, tecnologia). Target: **≥95%** das categorias alvos do MBP.

### 5. Adapters e Ingestão
- **Adapter DSL**: YAML declarativo (selectors, auth, rate‑limit, retries, parsing rules); plugin de execução sandbox (timeouts; mem‑caps).  
- **Política de robots/ToS**: cache respeitando TTL; user‑agent identificado; backoff exponencial com jitter; circuit breaker por fonte.  
- **Assinatura de lotes**: cada batch `B_t` selado com `MerkleRoot(B_t)` + timestamp; assinatura Ed25519 do operador; rotação 90d.

### 6. Normalização, Dedup e Equivalência
- **Canonização**: lowercase com preservação de entidades; normalização de datas (ISO‑8601/Z), numéricos, nomes próprios.  
- **Dedup semântica**: SimHash + Jaccard; verificação semântica (mini‑LM local) para near‑duplicates multi‑idioma (PT/ES).  
- **Equivalência de evento**: cálculo de `equivalenceHash(e)` a partir de título, entidades, local, janela temporal e tipo de desfecho; conflito resolve por consenso (sec. 7).

### 7. Consenso v1/v2
- **v1 (Q2)**: quorum 2/3 de fontes Tier‑0/1 ponderadas por `trust_0` (estático); agregação por **median ponderada**; estados: `Observed → Proposed → Confirmed → Finalized`.  
- **v2 (Q3)**: **trust dinâmico** por fonte: `trust_f = w1·uptime + w2·latency_score + w3·accuracy + w4·corrections(−)`, com clamp [0,1].  
- **Divergência**: distância robusta (median absolute deviation) entre reportes; metas `divergence p95 ≤0,5%`.  
- **Fallback econômico** (Q3): TWAP/median robust com **histerese** e circuit‑breakers se consenso jornalístico não finaliza em `Δt_max`.

### 8. Anti‑manipulação e Suborno
- **Detecção**: outlier estatístico (Z‑score robusto), **semantic‑dedup** agressivo, clusterização por similaridade de fonte.  
- **Política nível‑0**: peso mínimo reservado a fontes primárias; operadores independentes; segregação de funções.  
- **Atestações**: assinatura por fonte quando disponível (open signing); verificação (cadeia de chaves) e carimbo de tempo.  
- **Simulador**: spam coordenado, atraso intencional, poisoning; KPIs: `Δdivergence`, `staleness` e taxa de disputas; **kill‑switch por categoria**.

### 9. Transparência, Evidência e Auditoria
- **Status público**: `stalenessP95`, `divergenceP95`, `uptime90d`, error‑budgets (oracle/api/web/payout).  
- **Evidence store**: batches imutáveis com Merkle proofs; **ancoragem externa** do hash‑raiz por release em blockchain pública.  
- **Auditorias 2×/ano**: checklist de chaves/integração; relatório público.

---

## PARTE III — Motor de Mercado (MBP)
### 10. Modelos de Mercado
- **Binário**: outcomes {Sim, Não}; probabilidade `p`.  
- **Categórico**: outcomes {O₁…Oₙ}; soma de shares = 1; projeção para simplex.  
- **Escalar**: discretização em buckets [aᵢ,bᵢ); mapeamento para outcomes categóricos, payout proporcional (opcional) com quantização clara na criação.

### 11. AMM & Ordem
- **CPMM**: Invariante `x·y=k` (binário); para N outcomes, generalização **LMSR/CPMM híbrida** (configurável por mercado).  
- **Preço⇄Probabilidade**: `p = x/(x+y)` (binário); `pᵢ = qᵢ/Σq` (cat).  
- **Ordens**: `market` e **`limit` com `TIF` (`GTC`, `IOC`)**; batcher p/ reduzir frontrun; proteção de slippage por usuário/ordem.  
- **Anti‑sniping**: delays mínimos no batcher; ajuste dinâmico de fee por burst.

### 12. Fees Dinâmicos v1.2 (detalhes)
`fee_t = clamp(f0 + k1·σ_t + k2·(1 / (D_t + ε)) + k3·VIX_mbp, f_min, f_max)`  
- **σ_t**: EWMA intradiário; **D_t**: depth@2%; **VIX_mbp**: volatilidade agregada (top markets).  
- Parâmetros base: `f0=0,30%`, `f_min=0,10%`, `f_max=1,25%`; guardas `|Δfee|≤0,15pp/dia`.  
- **Calibração contínua** (job noturno) com rollback se Δ>2σ; relatório semanal (governança econômica).  
- **Limites de risco**: `OI_max = α·TVL (α∈[2,4])`, `exposure_net ≤ β·TVL_market (β∈[0,2])`, `imbalance_ratio > θ` → taxação incremental + **halts graduais**.

### 13. Vaults de LP e Incentivos
- **Vault simples**: provisionamento proporcional; auto‑rebalance; retirada com cool‑down.  
- **Incentivos**: curva com **cliff** e **decay**; rejeição automática de wash‑liquidity; KPIs: TVL, churn LP, revenue/TVL.

### 14. Resolução e Disputa
- **Integração nativa** ao oráculo; **contest window**; override humano com **auditoria assinada**; payout automático; reconciliação D+1.  
- **Métricas**: tempo‑até‑resolução (p50/p95), taxa de disputas, taxa de override.

### 15. Halts e Reabertura
- **Estados**: `Normal → Warn → Soft → Hard → Recovery → Normal`.  
- **Triggers**: `σ_t > σ_max`, `D_t < D_min`, `divergence > θ`, `oracle_staleness > ψ`.  
- **Histerese**: reabertura condicionada a `recovery_score = wD·D_norm + wσ·(1−σ_norm) + wδ·(1−div_norm)` acima do limite por 3 janelas.

---

## PARTE IV — Plataforma, API/SDK, UX e Design System
### 16. PWA & Performance Budgets
- **Meta**: INP p75 ≤200ms; TTFB ≤200ms; LCP ≤2,0s; CLS ≤0,1.  
- **Offline/Erro**: cache estratégico; fila de ordens com retry; banners de estado; modo leitura durante `Halt_Active`.

### 17. APIs (v2) — Especificação
- **Versionamento**: header `X‑API‑Version: 2.x`; compatibilidade estável + rotas `/v2/…`.  
- **Idempotência**: `Idempotency‑Key`; retries seguros.  
- **Erros**: catálogo `E_MBP_…` (códigos, http, mensagem, ação sugerida).  
- **Endpoints principais**:  
  • Oracle: `GET /api/v2/oracle/events`, `GET /api/v2/oracle/status`, webhooks `HMAC`.  
  • Markets: `POST /api/v2/markets`, `GET /api/v2/markets/:id`, filtros por categoria/país/estado.
  • Orders: `POST /api/v2/orders` (limit/market, TIF), `GET /api/v2/orders/:id`.  
  • Liquidity: `POST /api/v2/liquidity`, `GET /api/v2/vaults/:id`.  
  • Disputes/Settlement: `POST /api/v2/disputes`, `GET /api/v2/settlements/:id`.  
  • Portfolio: `GET /api/v2/portfolio` (posições, PnL, exposição).  
- **Auth**: OAuth2+PKCE (usuários), **HMAC** (parceiros), mTLS opcional; quotas e rate‑limits por plano.

### 18. Design System (DS) e Acessibilidade
- **Tokens**: cor (paleta contrastada), tipografia (escalas), espaçamento, raios, sombras, z‑index.  
- **Componentes**: inputs, selects, tabelas, cards, chips, gráficos de probabilidade, banners de halt/risco, modais de disputa.  
- **WCAG 2.2 AA**: foco visível; navegação teclado; rótulos/ARIA; validação e mensagens claras (microcopy PT‑BR/ES).  
- **Inventário de telas**: marketplace, detalhe (bin/cat/escalar), trade, portfólio, LP/vault, criar mercado (templates), disputa, payouts/KYC, status do oráculo.

---

## PARTE V — Observabilidade, SRE e Operações
### 19. Métricas e Painéis
- **Oracle**: staleness por‑fonte, divergência, uptime, backlog; tempo de consenso; taxa de falha de adapters.  
- **Mercado**: spread efetivo, slippage, depth@2%, volume/TVL, halts; ordens por TIF; taxa de falha.  
- **Web**: INP, LCP, TTFB, CLS; erros por rota; uso offline.  
- **SLO waterfall** p95: ingest≤150ms; agg≤200ms; consenso≤400ms; API≤180ms; TTFB≤200ms; INP≤200ms.  
- **Status Page**: **error budgets por serviço** + baseline mensal; histórico 90d; changelog e incident reports.

### 20. Alertas e Oncall
- **Burn‑rate** (1h/6h/24h) por serviço; **rota de escalonamento** definida; severidade P1–P4; **MTTR p95 ≤4h**.  
- **Playbooks**: staleness >30s/48h → freeze; divergence >1%/24h → freeze/rollback; DR acionado se RPO/RTO violados.

### 21. Testes de Carga e Capacidade
- **Alvos**: throughput do oráculo ≥2k eventos/min pico; latências conforme waterfall; 30% headroom.  
- **Planos**: soak (24–72h), spikes (pico 3×), step (degraus), fault‑injection (latência de fontes; falhas regionais).

---

## PARTE VI — Segurança, Privacidade e Compliance
### 22. Threat Modeling (STRIDE)
- **Oráculo**: spoofing (assinaturas e mTLS internos), tampering (Merkle/assinaturas), repudiação (logs com hash), DoS (rate‑limits por fonte), disclosure (minimização/criptografia), elevation (privilégios mínimos).  
- **API/Web**: OAuth2+PKCE/HMAC; **CSP/Trusted Types strict**; proteções anti‑XSS/CSRF/SSRF; scanning de segredos no CI.  
- **Payouts**: segregação, logs de auditoria, reconciliação D+1.

### 23. Privacidade (LGPD)
- **Mapeamento de dados** (PII somente onde necessário: payouts); **retenção** 12m hot/48m cold; anonimização; DSRs; revisões trimestrais; **appeals** e política pública.

### 24. Compliance BR/LatAm (coordenação com jurídico)
- Checklist de **termos/privacidade**, publicidade e disclaimers; limites por jurisdição; trilhas de auditoria; registros de KYC/AML; guarda de evidências oráculo.

---

## PARTE VII — Dados e Governança
### 25. Telemetria & Data Lake
- **Esquemas** de eventos (oráculo, mercado, ordens, liquidez, web perf); catálogo de dados; detecção de qualidade (expectations).  
- **ETL**: ingest streaming → storage quente (90d) → frio (1y+); retenção e acesso para analytics/backtests.

### 26. Backtests e Experimentos
- **Dataset BR/LatAm** rotulado por categoria e impacto; **cenários de cauda**; critérios de aceite v2; comparação A/B de parâmetros (k1,k2,k3,α,β).

---

## PARTE VIII — Entrega, Rollout e Governança
### 27. Ambientes e Releases
- **Ambientes**: dev → staging → canário → produção; feature flags; migrações com rollback.  
- **Canário**: 0,5→5→20% (S23); gates por watchers; rollback ensaiado.

### 28. DR e Chaos
- Backup/restore; simulações regionais; drills trimestrais; auditoria dos resultados.

### 29. Governança Econômica
- Reunião semanal: revisão de métricas e parâmetros `{k1,k2,k3,α,β}`; atas versionadas; **rollback** automático disponível.

---

## PARTE IX — RACI, Staffing e Cronograma
- **Líderes técnicos**: Oracle, MBP, Platform.  
- **Equipes**: FE/DS (2), BE (3–4), SRE (1–2), Sec/Privacy (1), Data/Backtests (1–2), UX (1–2), TPM (1).  
- **Ritos**: governance econômica; privacidade trimestral; post‑mortems; review do comitê a cada sprint.

---

## PARTE X — Checklists de Go/No‑Go
- **Pré‑Beta (S18)**: PWA; status públicos; bug bounty; SLO v1; ataques simulados PASS.  
- **Pré‑Canário (S23)**: payouts/KYC/AML ok; reconciliação D+1 100%; ancoragem ativa; rollback ensaiado.  
- **GA (S24)**: Maturity Gate por 30d; 0 P1; burn <0,5×; auditoria #2 ok.

---

## PARTE XI — Anexos Técnicos (exemplos de alta resolução)
### A. Modelos de dados (trechos)
- **Oráculo**: `event_v1.json` (campos obrigatórios/opcionais; enums de categoria/região; esquema de proof); índices por `equivalenceHash`, `finalizedAt`.  
- **Ordens**: `order_v2.json` (idempotencyKey; tif; slippageMax; estado; métricas de execução) com constraints.  
- **Mercado**: `market_v2.json` (tipo; buckets escalar; riscos; halts; vínculos ao evento oracular).

### B. PromQL (amostra)
```
# Divergência p95 (30m)
quantile_over_time(0.95, oracle_consensus_divergence[30m])
# Depth@2% (top‑20)
quantile(0.5, topk(20, market_depth_2pct))
# INP p75
histogram_quantile(0.75, sum(rate(web_inp_bucket[5m])) by (le))
```

### C. Estados de Halt (FSM textual)
`Normal` → (trigger) → `Warn` → (persistência) → `Soft` → (persistência) → `Hard` → (recovery_score≥θ por 3 janelas) → `Recovery` → `Normal`.

### D. Catálogo de erros (excertos)
- `E_MBP_ORDER_001` (LIMIT_PRICE_INVALID, 422); `E_MBP_HALT_002` (MARKET_HALTED, 409); `E_ORA_004` (EVENT_NOT_FINALIZED, 409); `E_AUTH_401` (TOKEN_EXPIRED, 401).

### E. Políticas de retenção (PII)
- Payouts: 12m hot, 48m cold; logs de acesso; anonimização após expiração; DSRs ≤ 30d.

---

## PARTE XII — Roadmap (Q2→Q4) — Sprints S7..S24
> Mantém os mesmos marcos e DoD por sprint já aprovados; este masterplan adiciona **profundidade** em cada subsistema. (Sem prompts.)

- **Q2 (S7–S12)**: Oráculo 1.5, resolução binária, status/API v1, antimanipulação v1.  
- **Q3 (S13–S18)**: Oráculo 2.0 (reputação/failover), mercados categórico/escalar, fees dinâmicos/limit/halts, liquidez & creators, PWA, beta aberto.  
- **Q4 (S19–S24)**: TLA+ + auditorias, KYC/AML + payouts, SRE/DR/chaos, plataforma pública + status v2, canário, GA + estabilização.

---

## PARTE XIII — Investor Language (densidade)
- **Q2** abate risco tecnológico com **oráculo verificável** e **resolução automática**, gerando **dados proprietários** com âncoras públicas.  
- **Q3** demonstra **robustez** e **qualidade de mercado pró‑nível**, reduz churn de LP e estabiliza receita via **fees dinâmicos** calibrados localmente.  
- **Q4** fecha **segurança/compliance/SRE**, aumenta a confiança regulatória e viabiliza **parcerias** via API/SDK v2, com métricas públicas e **30+ dias verdes**.

---

## PARTE XIV — Entregáveis do Repositório (a criar/atualizar)
- `roadmap/{Q2.md,Q3.md,Q4.md}`  
- `contracts/data/{event_v1.json,market_v2.json,order_v2.json}`  
- `services/oracle/{adapters,normalizer,consensus,reputation,finalizer}/…`  
- `core/mbp/{markets,orders,amm,fees,settlement,disputes}/…`  
- `platform/{api,webhooks,auth}/v2/…`  
- `apps/web/{pwa,disputes,portfolio,lp,creator}`  
- `ops/{prometheus,grafana,loki,otel}/…` + `ops/anchor_job.yml`  
- `specs/tla/{consensus_v1.tla,settlement.tla,disputes.tla,halts_semi_sync.tla}` + CI Apalache  
- `docs/{adr,runbooks,privacy,security,econ,weekly_minutes}`  
- `platform/status/error_budgets.json`  
- Evidence bundles por sprint em `out/evidence/SXX_*`

---

**Conclusão**: Este **v9** é um blueprint de execução de nível comitê para construir, lançar e operar um MBP e um Oráculo BR/LatAm 0→1 com padrões de classe mundial. Pronto para sequenciar no repo e iniciar as sprints S7..S24. Sem prompts; apenas especificações, critérios e artefatos.

