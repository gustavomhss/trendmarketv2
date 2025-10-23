# Q4 Roadmap — MBP + Oráculo (Wave 3) — Execução Suprema (S19–S24)

Contexto: Masterplan v9 (Ultra‑Expanded) + Q2 v2 + Q3 v2. Este Q4 cobre **S19–S24** e entrega **R‑3.0 (GA + 30+ dias verdes)** com: **Verificação Formal end‑to‑end**, **Auditorias de Custódia** e **Ancoragem Externa**, **KYC/AML & Payouts**, **SRE/DR/Chaos v2**, **Plataforma Pública (API/SDK v2 + Status v2)**, **Canário 5→20%**, **Reconciliação D+1=100%**, **Rollback ensaiado**, **GA** e **Estabilização 90d**. Documento **sem prompts**.

Comitê envolvido nesta edição: Vitalik (criptoeconomia/governança), Jobs (produto/UX), Lamport (verificação formal/TLA+), Juels (oráculos/segurança), Chitra (mecanismos/liquidez/risco), Forsgren (SRE/medição), Moxie (segurança/abuso).

---

## 0) North Star de Q4 e KRs finais
**Objetivo macro:** sair de Beta Aberto robusto para **operação pública contínua**, com garantias formais, trilhas de auditoria reproduzíveis, compliance completo e confiabilidade mensurável.

**KRs (até o corte R‑3.0 e 30d pós‑GA):**
- **Formal**: invariantes **I1..I11** e propriedades LTL (L1..L3) **PASS** no CI; **modelo de halts/timeouts em semi‑sincronia** com bound de filas e **transições de failover**; cobertura de transições ≥ 95% em harness.  
- **Custódia/Ancoragem**: auditoria #1 **aprovada** (S19) e #2 **aprovada** (S24); **Merkle roots** por release ancoradas on‑chain; CLI pública de verificação.  
- **KYC/AML & Payouts**: onboarding verificado, listas PEP/sanções atualizadas, **reconciliação D+1=100%**, MTTR p95 ≤ 4h para falhas de payout; apelações operacionais.  
- **SRE**: uptime ≥ **99,95%** (30d pós‑GA), burn < 0,5×; **DR testado 2×** (RPO≤5m, RTO≤30m) com relatório público; **monitoria sintética multi‑região** ativa.  
- **Plataforma**: **API/SDK v2 estáveis**, rate‑limits por rota, 3+ parceiros piloto integrados; Status Page **v2** com **error budgets por serviço** e **baseline mensal** publicados.  
- **Canário/GA**: canário 5→20% **com ORR aprovado**, rollback ensaiado; **GA** com **30+ dias verdes** e KPIs do Maturity Gate sustentados.

---

## 1) Go/No‑Go — Gates executivos
**Go para GA (R‑3.0)** exige checklist **todos verdes**:
1) **Formal**: CI de TLA+ (Apalache) PASS; logs arquivados; nenhum contraexemplo aberto.  
2) **Custódia**: auditoria #1 aprovada; ancoragem on‑chain verificada no canário; script de verificação pública disponível.  
3) **SRE**: ORR aprovado; DR 2× PASS; burn‑rate ≤ 0,5×; monitoria multi‑região **UP**.  
4) **KYC/AML**: fluxos ativos; sanções/PEP horários; reconciliação D+1=100% por 14 dias; appeals SLA definido.  
5) **Plataforma**: API/SDK v2 congelados; docs públicas; 3 pilotos; WAF/quotas; CSP strict.  
6) **Mercado**: spread p95 ≤ 2%, slippage p95 ≤ 1,5%, depth@2% p50 ≥ CE$75k; 0 P1 no mês.  
7) **Segurança**: bug bounty sem críticos pendentes; red‑team interno PASS; rotação de chaves dentro do prazo.

---

## 2) Verificação Formal — “Formal Pack” (S19 foco, S21/S22 regressão)
### 2.1 Especificações TLA+ (arquitetura)
- **Módulos**: `consensus_v1.tla`, `settlement.tla`, `disputes.tla`, `halts_semi_sync.tla`, `failover_modes.tla`, `merkle_append_only.tla`.  
- **Assunções temporais**: semi‑sincronia (δ_fonte, δ_consensus), drift ξ, janela τ; fairness fraca para progressão de eventos.

### 2.2 Invariantes de Segurança (I1..I11)
- I1 Não‑negatividade de saldos/LP.  
- I2 Conservação de valor (exceto fees).  
- I3 Unicidade de resolução.  
- I4 Determinismo de settlement dado `Finalization(e)`.  
- I5 Sem payout antes de finalização.  
- I6 Soma de LP shares == pool.  
- I7 Sem overflow/underflow.  
- I8 Sem trade em `Halt_Active`.  
- I9 Não‑finalização sem quorum.  
- I10 Rollback consistente.  
- I11 **Append‑Only** (Merkle roots).

### 2.3 Propriedades de Liveness (L1..L3)
- L1 Eventual finalização com quorum (mesmo após failover retornando).  
- L2 Eventual disbursal pós‑finalização.  
- L3 Terminação de disputa sob prazos finitos.

### 2.4 Extensões pedidas por Lamport/Chitra
- **Transições de Failover**: `Consensus → Fallback(TWAP) → Consensus` com histerese; prova de ausência de impasses.  
- **Halts repetidos**: liveness sob `Warn↔Soft↔Hard` com bound de reabertura (histerese + cooldown).  
- **Bounds de filas**: ordens e eventos (limites superiores) + progresso garantido.

### 2.5 CI/Processo
- Workflow: `.github/workflows/tla_apalache.yml` (check PRs que tocam `core/mbp/*`, `services/oracle/*`).  
- Artefatos: logs de estado, traces curtos, resumo PASS/FAIL, cobertura de transições; falha **bloqueia merge**.  
- Evidências: `out/evidence/S19_formal_audit/*` com PDFs, hashes e seeds de model checking.

---

## 3) Auditorias de Custódia & Ancoragem — “Custody Pack” (S19, S24)
### 3.1 Cadeia de Custódia (escopo)
- **Chaves**: inventário, rotação 90d, ofuscação/segregação, HSM/TPM opcional; políticas de acesso.  
- **Batches**: Merkle roots por lote; assinaturas de operador; timestamps confiáveis.  
- **Logs**: roll de failover, equivalence/dedup, disputas/resoluções, alterações de pesos de reputação.

### 3.2 Auditoria Independente
- **#1 (S19)**: conformidade das chaves, integridade de batches (amostra), aplicação da política nível‑0, revisão de runbooks; relatório público.  
- **#2 (S24)**: repetição com amostragem maior + verificação cruzada dos anchors on‑chain; cartas de atestação.

### 3.3 Ancoragem Externa & CLI Pública
- **Job** `ops/anchor_job.yml`: publica `MerkleRoot(B_release)` em blockchain pública; armazena txid + prova.  
- **CLI** `tools/verify_anchor`: baixa root, consulta on‑chain, verifica inclusão do evento/mercado; guia público.  
- **Painel**: “Anchors & Custody” com histórico de roots e txids.

---

## 4) KYC/AML & Payouts — “Compliance Pack” (S20 foco)
### 4.1 Fluxos funcionais
- **Onboarding**: coleta mínima de PII, verificação de identidade, prova de vida opcional; aceite de termos; consentimentos LGPD.  
- **Sanções/PEP**: checagens por evento (onboarding, pre‑payout) com provedores; atualização **horária**; auditoria de consultas.  
- **AML**: heurísticas de transação (volume incomum, padrão de wash); flags e revisão manual; SARs (relatos) quando aplicável.  
- **Payouts**: rails locais (pix/transferência) ou integradores; reconciliação D+1=100%; reprocessamento automático.

### 4.2 Segurança/Privacidade
- **Criptografia**: PII em repouso (AES‑GCM) e em trânsito (TLS1.3); chaves com rotação; KMS.  
- **Acesso**: princípio do menor privilégio; registros; DLP; segregação PII vs telemetria.  
- **Retenção**: 12m hot, 48m cold; descarte e anonimização; DSRs (≤30d).  
- **Apelações**: canal e SLA; políticas públicas.

### 4.3 Runbooks & Evidências
- Runbooks: `onboarding.md`, `payouts.md`, `aml_review.md`, `sanctions_updates.md`.  
- Evidências: relatórios de reconciliação diários, amostras de checagens, métricas de falha e MTTR.

---

## 5) SRE/DR/Chaos v2 — “Resilience Pack” (S21 foco, S22/S23 regressão)
### 5.1 SLOs e Error Budgets (v2)
- **Serviços**: oráculo, API, web, payouts.  
- **Metas**: uptime (oráculo 99,95%, API 99,95%, web 99,9%, payouts 99,9%); latências p95 do waterfall; **error budgets públicos** no Status v2.

### 5.2 DR e Failover Regional
- **Objetivos**: RPO≤5m, RTO≤30m.  
- **Execução**: replicação assíncrona; backups; testes **2× no Q4** com relatório público e métricas de recuperação; **chaos‑tests** de falhas regionais e de fontes.

### 5.3 Monitoria, Alertas e ORR
- **Monitores**: sintéticos multi‑região (2 provedores), watchers de staleness/divergence/spread/slippage/depth, burn‑rate (1h/6h/24h).  
- **ORR**: checklist final (infra, segurança, privacidade, oncall, runbooks, rollback, status, comunicação).  
- **Oncall**: escalas; MTTR p95 ≤4h; playbooks e exercícios.

### 5.4 Custo/Capacidade/DORA
- **Capacidade v2**: headroom ≥ 30% sob Beta Aberto; planejamento para GA; limites de custos com alertas.  
- **DORA**: lead time, deployment frequency, change fail rate, MTTR reportados no status interno.

---

## 6) Plataforma Pública — “Dev & Partners Pack” (S22 foco)
### 6.1 API/SDK v2 Final
- **Estabilidade**: contratos congelados; versionamento `/v2`; errors catalogados; idempotência; quotas e rate‑limits por rota.  
- **SDKs**: JS/TS e Python; exemplos end‑to‑end (criar mercado, negociar, consultar oráculo, webhook HMAC).  
- **Segurança**: OAuth2+PKCE/HMAC; mTLS opcional; chaves rotativas; anti‑phishing (verificação de domain binding).  
- **Docs**: portal com guias, referenciais, _try it_, _quickstarts_; exemplos de código; página de mudanças.

### 6.2 Status Page v2
- **Publicações**: **error budgets por serviço**, **baseline mensal** e incident reports; gráficos exportáveis; notificações.  
- **Transparência**: changelog com RCA resumida; política de comunicação de incidentes.

### 6.3 DevRel & Parceiros Piloto
- **Sandbox**: chaves, quotas, datasets fake, simuladores.  
- **Pilotos**: ≥3 integrações; contratos de uso de dados; SLAs; canal técnico.  
- **Exemplos**: apps de portfólio, alertas de mercado, dashboards de risco.

---

## 7) Canário 5→20% & GA — “Launch Pack” (S23 foco, S24 conclusão)
### 7.1 Plano de Canário
- **Fases**: 5% → 10% → 20%; avaliação em cada fase; gates: staleness/divergence, spread/slippage/depth, uptime, burn; **rollback** ensaiado.  
- **Comunicação**: status, release notes, canais internos, comunidade.

### 7.2 Reconciliação & Payouts
- **Reconciliação D+1=100%** obrigatória; discrepâncias tratadas; relatórios arquivados.  
- **KYC/AML** sempre ativos; checagens pre‑payout; appeals.

### 7.3 Ancoragem & Custódia
- **Ancoragem** de Merkle root a cada release; verificação pública; evidências anexas.  
- **Auditoria #2 (S24)**: custódia e anchors.

### 7.4 GA & Estabilização 90d
- **GA** após 20%→100% e **30+ dias verdes**;
- **Plano 90d**: foco em confiabilidade/qualidade (SLO, burn, P1=0), otimizações de custos, backlog de UX/creators, refinamentos de fees/halts.

---

## 8) Segurança/Abuso — “Defense‑in‑Depth Pack” (contínuo; S20/S21/S22 gates)
- **Postura Cliente**: CSP/Trusted Types strict, origin isolation, Subresource Integrity; fechamento de superfícies; sanitização rigorosa.  
- **API**: quotas por rota, WAF, _token binding_, _device fingerprint_ (se permitido), proteção a credencial stuffing.  
- **Supply Chain**: SBOM, assinaturas (Sigstore), SLSA ≥ L3; varredura de dependências; pinning.  
- **Criptografia**: TLS1.3, PFS, KMS; rotação 90d; HSM opcional.  
- **Bounty/Red‑Team**: escopo e SLAs; critérios de severidade; vitrine de correções.

---

## 9) Observabilidade & Métricas Públicas — “Truth Pack”
- **PromQL**: pacotes de regras para Oracle Integrity, Market Quality, Payouts, Web Perf, SLO/Burn.  
- **Export Público**: JSON/CSV diários de staleness/divergence/spread/slippage/depth, uptime, incidentes; hashes; link no status.  
- **Painéis**: Oracle (Integrity, Anchors), Market Quality, Liquidity/Creators, Payouts, SLO/Burn, Web Perf, DR/Chaos.

---

## 10) UX/Produto — “Polimento Final” (Jobs)
- **Microcopy final** (PT‑BR/ES) com consistência de termos;  
- **Empty/skeleton states** em todas as telas;  
- **A11y**: WCAG AA validada por automatizados + teste manual;  
- **Documentação de DS** (tokens, componentes, exemplos);  
- **Comunicação de Halts** clara e contextual.

---

## 11) Sprints S19–S24 — Corte fino (entregáveis, testes, DoD, evidências)
### S19 — **Formal & Auditoria #1** (Semanas 1–2)
**Objetivo:** travar propriedade formal e obter primeira atestação independente da custódia.

**Entregáveis:**
- TLA+: `halts_semi_sync.tla`, `failover_modes.tla`, updates em `consensus_v1.tla`, `settlement.tla`, `disputes.tla`, `merkle_append_only.tla`.  
- CI: `.github/workflows/tla_apalache.yml` com _gates_ obrigatórios; _seeds_ de model checking versionados.  
- Auditoria #1: escopo chaves/batches/política nível‑0/logs; relatório público; correções priorizadas.

**Testes:**
- Harness de transições (≥95% de cobertura de estados/edges);
- Provas de `Append‑Only` com contraexemplos artificiais (esperado FAIL).  

**DoD:**
- Todos invariantes e LTL PASS;
- Sem críticos na auditoria #1;
- Evidence `S19_formal_audit/` com PDFs/hashes/logs.

---

### S20 — **KYC/AML & Payouts** (Semanas 3–5)
**Objetivo:** habilitar compliance e fluxos de pagamento com reconciliação e privacidade.

**Entregáveis:**
- Integração KYC/AML (SDK/vendor); flows: onboarding, review, pre‑payout; políticas e consentimentos LGPD.  
- Payouts: integração rails (PIX/transferência) ou gateway; reconciliação D+1; retries/backoff; relatórios.  
- Segurança: PII criptografada; chaves em KMS; _access reviews_.  
- Appeals: formulários e SLAs; documentação pública.

**Testes:**
- E2E com dados de teste;
- Carga de payouts;
- Falhas de rede/integração;
- Drills de reversão.

**DoD:**
- Reconciliação D+1=100% por 7 dias;
- MTTR p95 ≤4h para falhas de payout;
- Evidence `S20_privacy_compliance/`.

---

### S21 — **SRE/DR/Chaos v2** (Semanas 6–7)
**Objetivo:** provar resiliência de produção com DR 2× e chaos.

**Entregáveis:**
- DR: _runbooks_, backups verificados, restauração 2×;
- Chaos: cenários (fonte regional, perda de AZ, latência persistente);
- SLO finais e _burn rules_;
- DORA tracking.

**Testes:**
- Game day #1 (fonte), #2 (DB primária), #3 (API surge).  
- Monitoria multi‑região ativa.

**DoD:**
- DR PASS 2× (RPO≤5m/RTO≤30m);
- Incident drill PASS;
- Evidence `S21_sre_dr/`.

---

### S22 — **Plataforma Pública v2 + Status v2 + Parceiros** (Semanas 8–9)
**Objetivo:** finalizar a camada de plataforma pública e transparência operacional.

**Entregáveis:**
- API/SDK v2: contratos congelados; exemplos; quotas por rota; docs.  
- Status v2: budgets por serviço; baseline mensal; incident RCA.  
- Component library publicada (npm);
- 3+ parceiros piloto integrados.

**DoD:**
- Latência API p95 ≤180ms;
- Parceiros enviando tráfego real;
- Evidence `S22_platform_public/`.

---

### S23 — **Canário 5→20% + Reconciliação + Ancoragem** (Semanas 10–11)
**Objetivo:** validar em produção com público significativo e controles ativos.

**Entregáveis:**
- Rollout 5→10→20% com watchers;
- Reconciliação D+1=100%;
- Ancoragem on‑chain por release;
- Rollback ensaiado;
- Comunicação pública (status/changelog).

**DoD:**
- Gates verdes por 14 dias;
- Evidence `S23_canary_payouts/` com relatórios.

---

### S24 — **GA 100% + Estabilização 90d + Auditoria #2** (Semanas 12–13 e contínuo)
**Objetivo:** concluir GA, manter 30+ dias verdes e executar auditoria final.

**Entregáveis:**
- Go‑live 100%;
- Plano 90d (SLO, burn, otimizações, backlog);
- Auditoria #2 (custódia + anchors);
- Retro/lessons;
- Relatório público de GA.

**DoD:**
- 30+ dias verdes;
- KPIs sustentados;
- Evidence `S24_ga_public/`.

---

## 12) Evidências & Repositório — “Auditable by Design”
**Código**: `specs/tla/*`, `services/oracle/*`, `core/mbp/*`, `platform/api,v2/*`, `apps/web/*`, `ops/*`, `sdk/*`.  
**Ops/Status**: `ops/prometheus/*.rules.yml`, `ops/grafana/*.json`, `ops/chaos/*`, `ops/backup/*`, `ops/anchor_job.yml`.  
**Docs**: `docs/adr/*`, `docs/runbooks/*`, `docs/public/*`, `docs/privacy/*`, `docs/security/*`, `docs/audit/*`.  
**Evidence**: `out/evidence/{S19_formal_audit,S20_privacy_compliance,S21_sre_dr,S22_platform_public,S23_canary_payouts,S24_ga_public}/` com `manifest.json`, hashes, relatórios e export de métricas.

---

## 13) Investor Language
- **Tese**: Q4 converte robustez em **confiança pública** (formal + auditorias + status/SLAs) e transforma dados e integrações em **vantagem competitiva**.  
- **Pragas eliminadas**: risco técnico (formal), operacional (DR/chaos/ORR), regulatório (KYC/AML/payouts), reputacional (status v2 + bounties).  
- **Sinais**: 3+ integrações ativas; métricas públicas; 30+ dias verdes.

---

## 14) Riscos & Mitigações (Q4)
1) **Falha em auditoria** → foco/quick‑fix; re‑test; comunicação transparente.  
2) **DR falho** → priorizar infra; nova rodada de testes; revisão de arquitetura.  
3) **Payouts/AML** → provedores de backup; _feature flags_; congelamento/appeals.  
4) **Carga/escala** → auto‑scaling; headroom; limites; _backpressure_.  
5) **Ataques** → WAF/quotas/Bot mgmt; _credential stuffing_ mitigado; roteiros de resposta.

---

## 15) Calendário Operacional (Q4)
- **S19**: Formal + Auditoria #1 + correções.  
- **S20**: KYC/AML/Payouts + reconciliação.  
- **S21**: DR/Chaos + SLO finais + drill.  
- **S22**: Plataforma v2 + Status v2 + parceiros.  
- **S23**: Canário + reconciliação + ancoragem.  
- **S24**: GA + 30d verdes + Auditoria #2.

---

**Conclusão**: Este Q4 especifica, em nível de execução, a transição de um Beta Aberto robusto para **operação pública com garantias formais, compliance completo e transparência mensurável**. Ao final, o MBP + Oráculo BR/LatAm opera com **padrões de classe mundial**, pronto para escala e para sustentar novos produtos conectados ao ecossistema.

