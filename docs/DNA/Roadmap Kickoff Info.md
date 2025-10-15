# Roadmap — Kickoff Intake (CE$)

> **Status:** preenchido por mim com base no Manual MASTER, Product Brief e Packs A1–A110. Se algo destoar, eu ajusto no ato e re-executo os gates. 

---

## 1) Objetivo e KRs
- **Objetivo do ciclo (0–90d):** Colocar no ar o **CE$ Foundations → Mercado → Modelos → Governança** (ondas 0–90d), atingindo o **NSM** e liberando somente com **watchers verdes + hooks A110 ativos**.
- **KRs (5):**
  1. ≥ **95%** das decisões com **trilha de auditoria** completa.
  2. **CDC lag p95 ≤ 120s** em tabelas quentes.
  3. **Drift**: **PSI ≤ 0,20** e **KS ≤ 0,10** em modelos produtivos.
  4. **Staleness de oráculo < 30s** (com TWAP/failover)
  5. **SRM = OK** em todos os experimentos de P6.
- **NSM (confirmado):** *Time‑to‑Preço‑Válido* **p75 ≤ 0,5s** (p95 ≤ 0,8s) para a jornada de decisão.

## 2) Escopo & Não‑Objetivos
- **IN (escopo):**
  - **Fundações**: CDC + **A106/A87/A89** (contratos/expectations/tests), **Observabilidade A71–A72**, **Hooks A110**.
  - **Decision & Pricing (DEC)**: pipeline de decisão/precificação com **SLO p95 ≤ 0,8s**.
  - **Mercado (PM)**: **Leilões (A10)**, **FX quoting/roteamento (A98–A100)**, **Oráculos (A104)**.
  - **Modelos (ML)**: serving/monitoramento (**A81/A84**) + **Experimentação A83**.
  - **Governança/XP**: **A90–A93/A109** (MRM, Postmortem/BCDR/OKRs), **Front/Portais A74–A80**.
- **OUT (não‑objetivos no 0–90d):** expansão multi‑país; integrações on‑chain; modelos avançados de risco fora do baseline; catálogos tarifários complexos; features exóticas de mercado.

## 3) Mercados/ICP & SLAs
- **País/Regulatório:** Brasil — **LGPD** (privacidade **A108**), **BCB** quando aplicável.
- **ICP/JTBD prioritário:** originadores de crédito (fintechs/bancos digitais) que precisam **preço válido em < 0,8s** com trilha de auditoria e governança by‑design.
- **SLAs por serviço (iniciais):**
  - **Decision Core (DEC):** latência **p95 ≤ 0,8s**; **erro budget** P1 por trimestre; rollback automático em 5xx/queima de SLO.
  - **Oráculos/FX:** **staleness < 30s** (TWAP/failover/quorum); hooks de divergência/benchmark.
  - **Dados (CDC/ETL/dbt):** **lag p95 ≤ 120s**; contratos **semver** e testes CI obrigatórios.
  - **FE/Portais:** **INP p75 ≤ 200ms**; regressão CWV → rollback FE.

## 4) Dados & Contratos (A106/A87/A89)
- **Fontes/datasets (alvo):** propostas/solicitações, perfil do proponente, eventos de pagamento, limites e taxas, **FX/mercado**, referenciais/regulatórios.
- **CDC alvo:** disponível em fontes transacionais; **lag p95 ≤ 120s**.
- **Contratos & qualidade:** contratos de dados **A106/A87** (Avro/Protobuf), **schema registry** com **semver**, **dbt tests** (unique/not null/fks), monitoração de **drift/expectations** e **documentação ≥95%** por pacote.

## 5) Watchers Must‑Have → Owners
- api_breaking_change_watch → **INT/FE**
- schema_registry_drift_watch → **DATA**
- data_contract_break_watch → **DATA**
- dbt_test_failure_watch → **DATA/PY**
- cdc_lag_watch → **DATA/PY**
- slo_budget_breach_watch → **SRE**
- model_drift_watch → **ML**
- metrics_decision_hook_gap_watch → **DEC/ST**
- formal_verification_gate_watch → **RSK/SEC**
- web_cwv_regression_watch → **FE**
- okr_risk_alignment_watch → **PM/RSK**
- dp_budget_breach_watch → **PRIV/SEC**
- runtime_eol_watch → **PLAT/SRE**
- dep_vuln_watch → **SEC**
- oracle_divergence_watch → **PM/BC**
- fx_delta_benchmark_watch → **RSK/Treasury**

## 6) Hooks A110 — Overrides
- **Padrão:** usar **defaults por domínio** (PM/DEC/ML/DATA/PLAT/FE/SEC/INT/RSK) — com rollback=**yes**.
- **Overrides adotados:**
  - **FE (INP):** manter `inp.p75>200ms•24h->rollback_FE; owner=FE` (sem mudanças).
  - **PM/Oráculos:** reforçar `staleness_ms>30000•5m->switch_to_twap_failover; owner=BC`.
  - **DEC:** `latency.p95>800ms•5m->degrade_route; owner=SRE`.
  - **DATA:** `contract_break->rollback+waiver_timebox; owner=DATA`.

## 7) Stack & Ambientes
- **Serviços:** DEC, PM/Oráculos, ML Serving, DATA (CDC/ETL/dbt), PLAT/SRE, FE/Portais, SEC/PRIV, INT.
- **Ambientes:** dev → stage → prod com **promotion gates** e canary/shadow + rollback.
- **OTel/Tracing:** ativo (amostrar ≥1% em prod); spans adicionais para `decision.explain`, `price.cache`, `sla.router`, `dq.alert`, `feature.drift`, `canary.abort`, `error.budget`, `env.promote`.
- **Acessos:** repositórios (app/infrastr/dados), pipelines CI, observabilidade (tracing/metrics/logs), registry de contratos.

## 8) Capacidades & Papéis (planejamento base)
- **Capacidade inicial (por sprint):** `{PO:0.5, ST:1.0, PY:1.0, DC:0.5, ML:1.0, SRE:0.5, FE:0.5}`.
- **Papéis ativos:** PO, Eng. Staff (ST), Backend/PY, Dados (DC), ML, SRE/Plataforma, FE, Segurança/Risco.

## 9) Dependências & Riscos
- **Dependências externas:** provedores de dados (bureau/FX/oráculos), identidade/KYC, antifraude, gateways de pagamento.
- **Top riscos (→ mitigação via watcher+hook):**
  1) **CDC lag** (DATA) → `cdc_lag_watch` + hook degrade/rollback.
  2) **Staleness/Quórum** (PM) → `oracle_divergence_watch` + TWAP/failover.
  3) **Drift de modelo** (ML) → `model_drift_watch` + PSI/KS→rollback.
  4) **CWV/INP** (FE) → `web_cwv_regression_watch` + rollback FE.
  5) **Privacidade** (SEC) → `dp_budget_breach_watch` + freeze & auditoria **A108**.

## 10) Governança & Aprovação
- **Assinaturas (ADR/Waiver A106):** **PO + Engenharia + Dados + Risco** (stewards). Exceções só com *timebox* e plano de rollback.
- **Releases/Change:** janelas com **Env Promotion Gates**, scorecards, e bloqueio automático em **SLO burn alto** ou falhas de contrato/segurança.

## 11) Evidências & Métricas
- **Dashboards/queries:** statusboards de **SLO burn**, **latência DEC**, **CDC lag**, **staleness oráculos**, **PSI/KS**, **CWV/INP**; relatórios de incidentes/BCDR.
- **Audit pack (como registrar):** anexar **trace_id/commit/sha256** por mudança; exportar CSV **Requisito↔Feature↔Watcher↔Hook↔KPI↔Evidência**; manter **Golden Notebooks** para pacotes críticos (ex.: CIP/A42).

## 12) Outras restrições
- **Compliance:** **LGPD/A108** by‑design; PII somente off‑chain; minimização/coleta necessária.
- **Operação:** **DORA‑MET** acompanhando fluxo de entrega; **Incident Command** ativo.
- **Orçamento/prazos:** operar no **STD** de suporte; upgrades de runtime planejados antes de **EOL**.

---

**Próximos passos:**
1) Gerar **hooks.yaml** consolidado (defaults+overrides acima) e **Backlog CSV canônico** (epic→story→watchers→hook→owner→evidência).
2) Abrir **ADR** para escolhas com trade‑offs (ex.: estratégia de oráculos/roteamento FX; contratos de dados críticos).

---

# Sequência recomendada (0→100) — serviços/produtos/modalidades
> **Owner (A): PO** em todas as frentes. Responsáveis (R) operacionais por domínio permanecem como mapeado (DATA/DEC/ML/FE/SRE/RSK/SEC/PM/INT).

**Onda 0 — Fundações (semanas 0–4)**  
CDC + contratos **A106/A87/A89**; Observabilidade **A71–A72**; **Hooks A110**; Oráculos/FX; **DEC p95 ≤ 0,8s**; Open Finance consent flows.

**Onda 1 — Consignado INSS/SIAPE (PF)**  
Razões: cap regulatório claro, risco menor (desconto em folha), time‑to‑market.  
Necessidades: cálculo **CET**, margem consignável, tetos de juros, trilha de auditoria; integração consignatárias/esteiras.  
Watchers-chave: `slo_budget_breach`, `oracle_staleness`, `contract_break`, `cdc_lag`, `decision_gap`.

**Onda 2 — Antecipação de Recebíveis de Cartão (PJ)**  
Razões: garantia forte (recebíveis), sinergia com oráculos e registradoras, impacto de receita.  
Necessidades: integração **registradoras** (registro/portabilidade/trava), cálculo de alçadas, divergência de recebíveis.  
Watchers: `oracle_divergence`, `fx_delta_benchmark` (se FX), `data_contract_break`.

**Onda 3 — CDC Veículo com Alienação Fiduciária (PF)**  
Razões: garantia real, mercado grande; complexidade média (gravames/DETRAN).  
Necessidades: motor de LTV, verificação de gravame, CET, fluxo de garantia.  
Watchers: `formal_verification_gate`, `web_cwv_regression` (portais), `model_drift`.

**Onda 4 — Pessoal não‑consignado (PF) com Open Finance**  
Razões: TAM alto; maior risco → exigir modelos/antifraude maduros.  
Necessidades: consent management, features de cash‑flow, Cadastro Positivo/SCR; reforço de fraude.  
Watchers: `model_drift`, `metrics_decision_hook_gap`, `dp_budget_breach`.

**Onda 5 — Home Equity / Imóvel em Garantia (PF/PJ)**  
Razões: ticket alto; alta complexidade regulatória/jurídica.  
Necessidades: LTV/LTI/DTI, registro de garantias, CET, gestão de desembolso.  
Watchers: `formal_verification_gate`, `slo_budget_breach`, `contract_break`.

**Onda 6 — Microcrédito Produtivo Orientado (MEI/PF produtiva)**  
Razões: agenda de inclusão; regras/processo orientado digital; tetos de tarifas.  
Necessidades: trilha de orientação, prova de contato/orientação, CET, limites de valor.  
Watchers: `decision_gap`, `data_contract_break`, `dp_budget_breach`.

### Critérios de priorização usados (peso ≥)
1) **Atrito regulatório** (menor é melhor)  
2) **Complexidade de build/integr.** (menor é melhor)  
3) **Risco de crédito/fraude** (menor é melhor)  
4) **TAM/impacto receita** (maior é melhor)  
5) **Reuso de capacidades da plataforma** (maior é melhor)

> Observação: mudanças de regulação podem alterar a ordem fina. Sempre aplicar **Go/No‑Go** com watchers verdes + hooks ativos antes de cada lançamento.

