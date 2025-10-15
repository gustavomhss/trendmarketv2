---
id: CE/SPEC_MASTER_KB
title: "Tudo que um P.O precisa dominar a nivel PHD para construir o CreditEngine"
version: "v4.1.0-kb-gold"
language: "pt-BR"
doc_type: "spec_master"
timezone: "America/Bahia"
authors:
  - Alan Kay
  - Vitalik Buterin
  - Jon von Neumann
  - Jhon Maynard Keynes
  - Donella Meadows
  - Alvin roth
  - Donald Knuth
  - Fernando Perez
  - Judea Pearl
  - Steve Jobs
  - jeff bezos
  - Clayton Christensen
maturity: "NORMATIVO — PhD Edition (com expansões autorizadas além do brief)"
watchers:
  - fx_cls_calendars
  - eips_ercs_oz
  - oracle_feeds_governance
  - sec_vuln_feeds
  - data_libs_core
tags: ["CreditEngine","Leilões","Pools","Oráculos","LMSR","AMM","CIP","FX","Derivativos","Duration","Bootstrapping","SDLC","QA","Data Engineering","Lakehouse","Tokenomics","Segurança"]
links:
  - name: "Pacote ULTRA (código/tests)"
    url: "CE_SPEC_MASTER_v4_ULTRA.zip"
license_notes: "Uso interno. Não constitui aconselhamento financeiro ou jurídico."
provenance: |
  Baseado no Product Brief do CreditEngine (2025-09-01) + autorizações do solicitante (2025-09-07) para expandir além do brief. Este arquivo consolida norma e blocos de tese (D+++) em um único artefato para KB.
---

# Guia de uso para KB (retrieval)
- **Âncoras curtas**: cada seção possui IDs `SP-XX` e subtópicos `D+++`. Use buscas como: `SP-18 oráculos δ_dyn EIP-712`.
- **Tabelas e símbolos** são únicos e globais — consulte `#Tabela de Símbolos Global` para consistência.
- **Bases/Unidades** sempre declaradas; o *lint matemático* rejeita ambiguidades.
- **Exemplos numéricos** usam ACT/365F para pools, ACT/360 para FX, 30E/360 para títulos.
- **Pseudocódigos** estão em blocos `pseudo:`; funções citadas existem no Golden Notebook.

---

## Tabela de Símbolos Global {#simbolos}
| Símbolo | Significado | Unidade | Notas |
|---|---|---|---|
| \(r_d, r_f\) | taxa doméstica/externa | a.a. | ACT/360 (FX) |
| \(S, F\) | spot/forward FX | moeda termo | Par explícito (base/termo) |
| \(T\) | tempo fracionário | anos | Base declarada na seção |
| \(σ\) | volatilidade implícita | a.a. | superfície livre de arb. |
| \(Δ, Γ, \Theta, \rho\) | greeks | — | conforme BSM |
| \(k\) | invariante AMM | — | XYK |
| \(b\) | parâmetro LMSR | moeda | perda máx \(≤ b\ln K\) |
| \(E[L]\) | perda esperada | moeda | slashing oráculos |
| \(m\) | períodos/ano | — | APR↔APY |
| \(D_M, D^*, C\) | duration (Macaulay/mod.) e convexidade | anos, anos, anos² | — |
| \(x_t\) | observação do oráculo | — | valor unitário do feed |
| \(m_t, s_t\) | EWMAs nível/variância | — | δ_dyn |
| \(ρ\) | razão de preços | — | \(ρ=P_1/P_0\) |

**Lint Dimensional (norma):** toda fórmula declara `(base_dias, unidade_saida)`. Ex.: `cupom = Σ(taxa·capital·dias)/Σ(capital·dias)` ⇒ `%` (R$·dia cancela).

---

# SP-00 — Convenções, Unidades, Calendário, Lint {#SP-00}
**Bases:** pools ACT/365F; FX ACT/360; títulos 30E/360. Ajuste: Modified Following (fallback Preceding).  
**APR↔APY:** \( \text{APY}=(1+\text{APR}/m)^m-1 \), \( \text{APR}=m((1+\text{APY})^{1/m}-1) \).  
**Calendários:** BR(B3+BACEN), US(Federal), EU(TARGET2). FX liquida T+2.

> **D+++ (nível tese).** *Teorema (Consistência Dimensional)*: se `t_i = dias_i/365`, `c_i` em R$, `r_i` adimensional, então `cupom = Σ r_i c_i t_i / Σ c_i t_i` é adimensional. *Esboço*: fator \( \text{R$·dia} \) cancela.

---

# SP-01 — Leilões Reversos (Originação) {#SP-01}
**Clearing:** ordenar por custo efetivo asc; desempate por `ts`; pesos ELO/score \(w∈[w_{min}, w_{max}]\) sem excluir novatos; preencher até alvo.  
**Cupom do leilão:** `cupom = Σ(custo·capital·dias·w)/Σ(capital·dias)`.
**Replay:** trilhas (hash, autores, ts).

**pseudo:**
```python
ordenar(bids, chave=(custo, ts))
alocado = 0; num = 0; den = 0
for b in bids:
  take = min(b.capital, alvo - alocado)
  if take <= 0: break
  base = take * (b.dias or 1)
  w = w_ELO(b.elo)
  num += b.custo * base * w
  den += base
  alocado += take
cupom = num/den
```

> **D+++** Propriedades: (i) monotonicidade (custo↓ ⇒ posição não piora); (ii) *budget-balance*; (iii) variação marginal O(1/N). Complexidade O(n log n).

---

# SP-02 — Pools & Cupom capital×tempo (ACT/365F) {#SP-02}
**Fórmula:** `cupom = Σ(taxa·capital·dias)/Σ(capital·dias)` (unidade `%`).  
**Saques:** abertos=FIFO em estresse; fechados=sem resgate.

> **D+++** *Equivalência contínuo↔discreto*: com taxa **piecewise** constante, `cupom_discreto → ∫ r(t) w(t) dt / ∫ w(t) dt` (erro O(Δt²)). Fila M/D/1 para stress: \(W_q \le \frac{ρ}{2μ(1-ρ)}\).

---

# SP-03 — Default & Governança de Credores (CC/RC/LE) {#SP-03}
**Papéis:** CC (ponderado por exposição), RC (bidding; fee+reputação), LE Escrow on-chain.  
**Quóruns:** ordinárias ≥50%; litígio/acordo ≥66,7%; substituir RC ≥60%.

> **D+++** FSM; *Teorema (Prioridade S≽J)* sob rateio proporcional; decisão Bayes: vender se `P(sucesso)*VR_liq < lance_firme`.

---

# SP-04 — Sistema ELO (ELO-P/C) {#SP-04}
**Atualização:** \( R' = R + K(\text{score}-E) \), \( E = \frac{1}{1+10^{(R_{op}-R)/400}} \).  
**Decay:** −1%/semana sem partidas; anti‑farm (cap + detecção de colusão).

> **D+++** |ΔR| ≤ K_max por janela; multi‑oponente via média por exposição; grafo de interações com modularidade.

---

# SP-05 — Scoring CE$ {#SP-05}
**TTLs:** Bureau 180d; Cashflow 30d; Documental 365d; setorial 7d; on‑chain 30d; colateral 90d.  
**Composição:** escore 0–1000 com pesos públicos; contestação auditável.

> **D+++** `S=Σ w_j s_j` com *decay* \(e^{-Δ/τ}\); calibração Bayes; estabilidade p95 ≤ 5 bps.

---

# SP-06 — CE$ Tokens 1:1 (PoR/Pausa/Reconciliação) {#SP-06}
**Pausa:** `supply_onchain > reservas_atestadas*(1+Δ)`; Δ: BRL 0,10%, USD 0,05%.  
**Reconciliação:** D+1 12:00 BRT; *unpause* com 2 PoR consecutivas.

> **D+++** risco de FN/FP da pausa; atestação diária assinada; segregação multi‑moeda.

---

# SP-07 — Integração de Sinais {#SP-07}
**Regra:** preço de leilão prevalece; ELO/score modulam limites; oráculos ajustam spreads.

> **D+++** modulação \(L' = L \cdot g(z)\) (g Lipschitz); impacto ≤ 30 bps p95.

---

# SP-08 — FX & CIP (discreta/contínua) {#SP-08}
**CIP (discreta):** \( F = S\frac{1 + r_d T}{1 + r_f T} \). **Contínua:** \( F = S e^{(r_d-r_f)T} \).  
**FX:** ACT/360; pips conforme par; T de dias úteis.

> **Ex.** S=5,20; r_d=10% a.a.; r_f=4% a.a.; T=0,5 ⇒ \(F≈5,357\).  
> **D+++** |gap| ≤ ε (2 pips, fricções explícitas); reporte: S,F,rd,rf,T,convenção,calendário,side.

---

# SP-09 — Secundário via AMM (XYK/CLMM) {#SP-09}
**XYK:** \(x y = k\), preço \(p = y/x\). **IL:** \(2\sqrt{ρ}/(1+ρ)-1\).  
**CLMM (s=√P):** Δx = L(1/s_b − 1/s_a); Δy = L(s_b − s_a).

> **D+++** no‑arb across‑bins; convexidade do valor do LP em \(\ln P\); hedge Δ/Γ discreto; IL com bandas por bootstrap.

---

# SP-10 — Matemática Financeira Estendida {#SP-10}
**PV:** \( CF/(1+i)^t \) (discreto), \( CF e^{-rt} \) (contínuo).  
**NPV/IRR:** \( \text{NPV} = Σ CF_t/(1+r)^t - I_0 \).  
**Duration/Convexidade:** \( D_M = \frac{Σ t CF_t/(1+y)^t}{P} \), \( D^* = D_M/(1+y) \), \( C = \frac{Σ t(t+1)CF_t/(1+y)^{t+2}}{P} \).  
**Aproximação:** \( ΔP/P ≈ -D^*Δy + \tfrac{1}{2}CΔy^2 \).

> **D+++** Bootstrapping (Newton, tolerância 1 bp); no‑arb: fatores de desconto não crescentes; testes com bonds de referência.

---

# SP-11 — Derivativos & Superfícies de Vol {#SP-11}
**BSM:** \( d_1=\frac{\ln(S/K)+(r+0,5σ^2)T}{σ\sqrt{T}},\ d_2=d_1-σ\sqrt{T} \).  
**Call:** \( C=S N(d_1)-K e^{-rT}N(d_2) \).  
**Greeks:** Δ=N(d₁), Γ=n(d₁)/(Sσ√T), Vega=S n(d₁)√T, etc.

> **D+++** Paridade \(C-P=S-Ke^{-rT}\); interpolação monotone‑convex (K); variância linear no tempo (T); superfície no‑arb.

---

# SP-12 — Prob/Estatística & Experimentação {#SP-12}
**Bayes:** posterior ∝ verossimilhança × prior.  
**A/B (proporções):** \(n ≈ 2(z_{1−α/2}+z_{1−β})^2 p̄(1−p̄)/d^2\).

> **D+++** SPRT (limiares A/B), alpha‑spending (Lan‑DeMets); guardrails e *post‑mortem* automático.

---

# SP-13 — SRE & Segurança Operacional {#SP-13}
**Circuit breakers:** leilão: |z|>5σ/15min ou Δ>300 bps; pool: inadimplência 7d>3σ ou liquidez<10% AUM.  
**Descongelar:** 2 PoR consecutivas + estabilidade 3 janelas.

> **D+++** EWMA/CUSUM; MTTD ≤ 2 min (saltos ≥ 5σ); histerese anti‑flap.

---

# SP-14 — Jurídico Avançado {#SP-14}
**Segregação** por moeda; reconciliação D+1 12:00 BRT com hash público.  
**Dupla PoR** (auditor + oráculo); challenge window 24h; KYC/AML por risco.

---

# SP-15 — Anticolusão & Auditoria {#SP-15}
**Detecção:** features (IP, timing, custo, recorrência) → Mahalanobis + DBSCAN → flags → revisão humana.  
**Replay:** determinístico (seed/hash público).

---

# SP-16 — Métricas & Analytics {#SP-16}
**TTC** (solicitação→liquidação mediana), **PoR Freshness** (%≤24h), **Latency‑to‑Pause** (ms), **OSE** (spread/benchmark), **DGL** (detecção→decisão→ato).  
**Mapa Métricas→Ações**: OSE↓ ⇒ revisar pesos/limites; PoR Freshness↓ ⇒ ↑frequência; TTC↑ ⇒ fairness/SLAs.

---

# SP-17 — Padrões de Dados & Python {#SP-17}
**Schemas (ex.):** `leilao.bid {id,custo,capital,elo,ts}`; `pool.entrada {id,taxa,capital,dias}`; `por.atestacao {moeda,supply,reservas,ts,fonte}`.  
**Snippets:** `cupom_pool`, `forward_discreto/contínuo`, `elo_update`, `il(ρ)`.

> **D+++** Idempotência por `event_id`; `vNext + shadow write`; Great Expectations mínimas; Freshness p95 e Completeness ≥ 99,5%.

---

# SP-18 — Oráculos (Arquitetura, Parâmetros e Governança) {#SP-18}
**Topologia:** feeders assinantes (EIP‑712), agregador on‑chain (*median‑of‑N*), `quorum_min`.  
**Parâmetros:** `heartbeat` (FX 60s; macro 5min), `staleness_max` (≤5×heartbeat), `deviation_threshold δ`, `fallback_order`, `quorum_min` (5/9).  
**Validação:** assinaturas válidas, staleness, desvio, quorum; escrever *round* (mediana).

> **D+++** Robustez (mediana/trimmed/MoM), δ_dyn via EWMA, provas de má conduta (double‑sign/out‑of‑bounds/latency), *slash* \(E[L]=p_{det}S-(1-p_{det})G\). SLOs: liveness≥99,9%/30d; lag≤heartbeat+2s; |median−TWAP_5m|≤3σ.

---

# SP-19 — Mercado de Previsões (LMSR) {#SP-19}
**Custo:** \(C(\mathbf{q})=b\ln\sum_j e^{q_j/b}\). **Preço:** \(p_i= e^{q_i/b}/\sum_j e^{q_j/b}\). **Perda máx:** \(≤ b\ln K\).  
**Assentamento:** oráculo de evento; *grace* 30 min; commit‑reveal opcional.

> **D+++** Dualidade LMSR↔log‑score; Hessiana \(H=\frac{1}{b}(\mathrm{Diag}(p)-pp^\top)\); calibração de `b` por ticket→Δp alvo; mitigação de front‑running (commit‑reveal/batching).

---

# SP-20 — SDLC/Ágil, Storywriting e QA {#SP-20}
**Cadências:** sprints 2 semanas; planning/daily/review/retro; Scrum of Scrums.  
**DoR/DoD:** INVEST + Gherkin; CI com lint/testes/SAST/DAST/SBOM; canary + rollbacks.

> **D+++** Pirâmide de testes (Unit≥70%, crítico≥85%); mutation≥60% core; SLO 99,9% (erro budget=43min/mês); gates de release.

---

# SP-21 — Project/Program Management {#SP-21}
**RAID/RACI; OKRs; stage‑gates** (Spec→Build→Pilot→GA); program board.  
**PERT:** \(E=(o+4m+p)/6\), \(σ^2=((p-o)/6)^2\). **Earned Value:** CPI=EV/AC; SPI=EV/PV.

> **D+++** EMV=Prob×Impacto; Monte Carlo (10k) para caminho crítico; faixas CPI/SPI estáveis.

---

# SP-22 — Data Engineering (Data Pool, Lake/Lakehouse) {#SP-22}
**Arquitetura:** bronze/silver/gold (lakehouse). **Data Pool CE$:** domínios (leilões, pools, default, CE$ tokens, oráculos, previsões).  
**Contratos:** schemas versionados, tipos estáveis; breaking via `vNext` + sombra; SLOs (Freshness p95, Completeness).

> **D+++** Particionamento por `dt` e domínio; compaction 128–512MB; ZSTD; streaming com `allowed_lateness=15min`; watermarks; PII tagging; encriptação (em trânsito/em repouso).

---

# SP-23 — Cloud, Tokenomics & Segurança {#SP-23}
**Cloud:** Multi‑AZ; DR multi‑região (tier‑1); IaC (Terraform); autoscaling; PDBs.  
**Segurança:** KMS/HSM; MPC p/ chaves quentes; vault de secrets; zero‑trust (mTLS, RBAC/ABAC); SAST/DAST/deps scan/SBOM; auditoria + verificação formal.  
**Tokenomics:** staking/bond p/ oráculo; rewards por uptime/acurácia; taxa do CE$ ≤ 10 bps/ano do float (parâmetro governado).

> **D+++** AEAD (IND‑CPA+INT‑CTXT) com AAD; MPC (t,n) e cerimônias de chaves; RPO≤5min/RTO≤30min; rotação≤90d; auditorias ≥90% dos contratos críticos.

---

## Exemplos Trabalhados (mínimo 3) {#exemplos}
1. **Cupom do pool (3 posições)**  
Entradas: (1) 1,0M a 2,2%/60d; (2) 0,5M a 2,9%/45d; (3) 0,8M a 2,5%/75d.  
Resultado: `cupom ≈ 2,4368%` (ACT/365F).

2. **CIP (spot/forward e taxas)**  
S=5,20; r_d=10% a.a.; r_f=4% a.a.; T=0,5 (ACT/360) ⇒ \(F_{disc}≈5,35294\), \(F_{cont}≈5,35836\) (gap≈0,10%).

3. **Clearing de leilão com ELO/empates**  
Meta 500k; bids ordenados por custo e `ts`, `w_ELO` cap ±10%; cupom calculado por média ponderada capital×tempo×w.

---

## Pseudocódigos-Chave (Big‑O) {#pseudo}
- `cupom_pool`: O(n)  
- `forward_discreto/contínuo`: O(1)  
- `elo_update`: O(1) por evento  
- `il(ρ)`: O(1)  
- `lmsr_delta_q`: O(1)  
- `oracle.should_accept`: O(1) validação; O(N) agregação (mediana)

---

## Checklist de Precisão {#checklist}
- [ ] Base de dias declarada (ACT/365F, ACT/360, 30E/360).  
- [ ] Unidade de saída (%, pips, R$) explícita.  
- [ ] Símbolos conforme tabela global.  
- [ ] Lint matemático OK; sem mistura sem conversão.  
- [ ] No‑arbitragem verificada (vol, AMM, forwards).  
- [ ] SLOs/limiares versionados por pack.  
- [ ] Logs/replay e trilhas imutáveis habilitados.

---

## Tarefa YAML (metadados) {#tarefa}
```yaml
id: CE/spec_master_kb_rollout
name: Consolidar SPEC MASTER (PhD) em KB
owner: PO-CreditEngine
prioridade: P0
deps: [ULTRA_PACKAGE, Oracles_Deploy_v1]
acceptance_criteria:
  - Documento único com SP-00…SP-23 e blocos D+++.
  - Lint matemático passa em 100% das fórmulas chave.
  - 3 exemplos numéricos reprodutíveis (esta seção).
  - Checklist de Precisão 100% ✓.
license_notes: Uso interno, ver proveniência.
```

---

## Evidence JSON (KPIs RAG) {#evidence}
```json
{
  "id": "evidence/ce/spec_master_kb_v4_1",
  "kpis": { "mrr": null, "ndcg": null, "coverage": null, "leakage": null },
  "notes": "KPIs serão acoplados aos contratos de dados SP-22 e watchers SP-18.",
  "version": "v4.1.0"
}
```

---

## QGen (perguntas de avaliação) {#qgen}
**≥20 perguntas**  
1) Prove a relação discreta↔contínua da CIP e quantifique o erro para T pequeno.  
2) Como calibrar `b` do LMSR para limitar \(|Δp|\) por ticket médio?  
3) Demonstre a convexidade do valor do LP em \(\ln P\) no XYK.  
4) Quais condições garantem superfície de vol sem arbitragem?  
5) Derive `D_M`, `D^*` e `C` e use para aproximar ΔP/P.  
6) Formule δ_dyn com EWMA e justifique limites.  
7) Qual o breakdown point da mediana e por que é relevante?  
8) Explique o commit‑reveal no assentamento de previsões.  
9) Mostre que IL(ρ)=IL(1/ρ) e que IL(1)=0.  
10) Defina *error budget* e gates de release no SLO 99,9%.  
11) Como verificar paridade call‑put na prática?  
12) Projete um *fallback_order* de oráculo e seus riscos.  
13) Calcule o cupom de um pool dado um conjunto de entradas.  
14) Quando aplicar FIFO em stress vs não-resgatáveis?  
15) Mostre um algoritmo de bootstrapping e a tolerância alvo.  
16) Especifique RAID/RACI para um épico de oráculos.  
17) Defina contratos de dados com SLOs e testes GE.  
18) Explique STRIDE aplicado ao CE$ e thresholds CVSS.  
19) Derive Δq no LMSR para 0,4→0,6 (binário).  
20) Explique como medir Latency‑to‑Pause e configurar alertas.

**≥10 hard‑negatives (afirmações falsas plausíveis)**  
A) Em FX, T usa sempre calendário corrido (FALSO: ACT/360 e úteis).  
B) No LMSR, b menor aumenta profundidade de livro (FALSO: reduz).  
C) Em XYK, IL independe de variação de preço (FALSO: depende de ρ).  
D) Paridade call‑put vale mesmo com dividendos ignorados (FALSO sem ajuste).  
E) Duration modificada não depende de y (FALSO: \(D^*=D_M/(1+y)\)).  
F) Mediana tem breakdown point 25% (FALSO: 50%).  
G) δ_dyn deve ser sempre constante (FALSO: adaptativa).  
H) PoR diária dispensa reconciliação D+1 (FALSO).  
I) SLO 99,9% dá erro budget de 9h/mês (FALSO: ~43min).  
J) Watermarks removem atraso de eventos (FALSO: apenas limitam o atraso acumulado).

---

## Changelog {#changelog}
- **v4.1.0-kb-gold** — Documento único “KB‑ready”: consolidado norma + D+++, símbolos globais, exemplos, pseudocódigos, checklist, Tarefa YAML, Evidence, QGen, hard‑negatives.  
- v4.0.0 — ULTRA DENSIDADE (D+++), pacote executável e testes.  
- v3.3.0 — PhD (D++) por pack.  
- v3.2.0 — DENSIDADE+ (deep dives).  
- v3.1.0 — Oráculos/Previsões/SDLC/PM/Data/Cloud adicionados.  
- v3.0.0 — SP‑08…SP‑17 elevados a norma.
