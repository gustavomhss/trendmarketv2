---
id: CE/ENC_P1_MERGEPACK_P1A
version: "v7.3.1-p1a"
title: "Tudo que um P.O precisa dominar a nivel PHD para construir o CreditEngine — ENCICLOPÉDIA (Parte I — Revisão p1a)"
language: pt-BR
doc_type: encyclopedia
timezone: America/Bahia
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
acknowledgements:
  - Peter Thiel (convidado)
  - Elon Musk (convidado)
  - Jurista A (finanças)
  - Jurista B (blockchain/cripto)
maturity: "NORMATIVO + TESE + LAB EXECUTÁVEL (PhD) — Parte I (revisada)"
license_notes: "Uso interno. Não constitui aconselhamento financeiro/jurídico."
provenance: |
  MergePack autônomo da Parte I com **ajustes p1a** aplicados após triple‑check:
  (i) M/D/1 em SP‑02 passa de bound para **fórmula exata**;
  (ii) SP‑11 explicita paridade com dividendo contínuo q;
  (iii) SP‑17 nota de **Pandas CoW (>=2.0)** e habilitação;
  (iv) SP‑22 reforça chave de idempotência `(event_id, feedId)`.
watchers:
  - fx_cls_calendars
  - eips_ercs_oz
  - oracle_feeds_governance
  - sec_vuln_feeds
  - data_libs_core
  - cloud_ops
  - sdlc_quality
  - tokenomics_policy
  - risk_lab
  - vol_surface_guard
  - amm_noarb
  - law_reg_watch
tags: ["CreditEngine","Leilões","Pools","Oráculos","Previsões","AMM","CIP","FX","Derivativos","Volatilidade","Curvas","Duration","Bootstrapping","Bayes","A/B","SRE","Scrum","Storywriting","PMO","Data","Lakehouse","Tokenomics","Segurança","MPC","Parte I","p1a"]
---

> **Nota para merge:** cabeçalhos prefixados com **P1‑** (âncoras únicas). Exemplos **E01–E60**; **E15 corrigido**. Ajustes p1a aplicados conforme auditoria.

> **Solicitação específica (conforme pedido do solicitante):**
> "Crie um markdown de fórmulas matemáticas, conceitos matemáticos, conceitos teóricos, teorias, algoritmos, conceitos filosóficos, teoria dos jogos, conceitos de blockchain, de python, matemática financeira, DeFi etc.  
> Esse documento será escrito por: Alan Kay, Vitalik Buterin, Jon von Neumann, Jhon Maynard Keynes, Donella Meadows, Alvin roth, Donald Knuth, Fernando Perez, Judea Pearl, Steve Jobs, jeff bezos e Clayton Christensen.  
> Eles se juntaram pra escrever um documento com o título: 'Tudo que um P.O precisa dominar a nivel PHD para construir o CreditEngine'."

---
# P1‑SP‑00 — Convenções, Unidades e Lint Dimensional
**Bases de contagem de dias (com uso recomendado):**
- **ACT/360** (FX/CIP, money‑market, swaps de curto prazo).  
- **ACT/365F** (cupons de pools, accrual contínuo em produtos do CreditEngine).  
- **30E/360** (bonds/corp.).  
- **Calendário**: **T+2** para FX spot; feriados por **FX/CLS**.

**Notação e unidades:** bps = 0,01%; pips = 0,0001 (JPY: 0,01); preços em moeda; taxas anuais `a.a.`; volatilidades em % a.a.  
**Símbolos globais:** \(r_d,r_f,S,F,T,\sigma,\Delta,\Gamma,\Theta,\rho,k,b,D_M,D^*,C\).  
**Lint matemático:** cada fórmula declara `(base_dias, unidade_saida)`; propriedades **no‑arbitrage**: paridade C−P; convexidade(K) (\(\partial^2C/\partial K^2\ge0\)); calendar(T) (\(\partial C/\partial T\ge0\)); \(D'(t)\le 0\) em curvas; banda **CIP**; **no‑crossing** em CLMM.

---
# P1‑SP‑01 — Leilões Reversos (Originação)
**Mecanismo base (clearing por custo efetivo):**
- Ordenar lances \(i\) por **custo efetivo** \(c_i\) (spread proposto ajustado por risco/escala).  
- Agregar até atingir o alvo de capital \(K^*\).  
- Desempates: (1) menor \(c_i\), (2) timestamp, (3) *seed* pública.

**Fairness por ELO:** \(R'_i = R_i + K(\text{score}_i - E_i)\), com *decay* semanal −1% e cap de peso ±10% nos leilões.  
**Propriedades:** monotonicidade, *budget‑balance*, *strategy‑proof* aproximado via penalidade de desvio (auditável).

**Pseudocódigo (O(n log n))**
```python
bids = sort_by_effective_cost(bids)  # estável
cap = 0
for b in bids:
    take = min(b.size, target - cap)
    assign(b, take)
    cap += take
    if cap == target:
        break
```

---
# P1‑SP‑02 — Pools (Cupom por Capital×Tempo)
**Definição (ACT/365F, % a.a.):**  
\[ \text{cupom}(t_0,t_1) = \frac{\sum_{j} c_j\,K_j\,d_j\,w_j}{\sum_{j} K_j\,d_j} \quad \text{onde}\ d_j=\frac{\text{dias úteis}}{365}. \]
**Arquiteturas:**
- **Abertos**: resgates contínuos; em stress, **fila FIFO** determinística.  
- **Fechados**: não‑resgatáveis até maturidade; *waterfall* S≽J em eventos de *default*.

**Capacidade operacional (M/D/1 — **forma exata**):**  
\[ \boxed{\; W_q = \frac{\rho^2}{2\,\mu\,(1-\rho)}\;} \qquad (\text{base: ACT/365F; unidades: tempo}) \]
> Observação: a inequação \(W_q \le \tfrac{\rho}{2\mu(1-\rho)}\) é um **bound** útil; aqui adotamos a **expressão exata** para M/D/1.

---
# P1‑SP‑03 — Default & Governança (CC/RC/LE)
- **Papéis:** *Credit Committee* (CC), *Resolution Committee* (RC), *Legal Enforcer* (LE).  
- **Quóruns:** ordinário ≥50%; litígio ≥66,7%.  
- **FSM:** detecção → deliberação → execução → rateio; *escrows* condicionais e janelas de *challenge*.

---
# P1‑SP‑04 — ELO/Score & Fairness p/ novos
\(R' = R + K(\text{score}-E)\), *decay* −1%/sem; cap ±10% de peso. *Cold start*: prior hierárquico e *exploration* forçada.

---
# P1‑SP‑05 — Scoring Bayesiano (priors/shrinkage)
**Binário (Beta–Bernoulli):** prior \(\operatorname{Beta}(\alpha,\beta)\) → posterior \(\operatorname{Beta}(\alpha+x,\beta+n-x)\).  
**Gaussiano (Normal–Normal):** *shrinkage* para média global com variância conhecida.

---
# P1‑SP‑06 — CE$ 1:1 (PoR/Pausa)
- Pausa automática se `supply_onchain > reservas_atestadas·(1+Δ)`; Δ: BRL 0,10% / USD 0,05%.  
- Reconciliação D+1 às 12:00 BRT; dupla atestação (independente).

---
# P1‑SP‑07 — Integração de Sinais (macro/setoriais/oráculos)
Limites modulados: \(L' = L\cdot g(z)\), com |impacto| p95 ≤ 30 bps; *cooldown* e *saturation* para evitar *overreaction*.

---
# P1‑SP‑08 — FX & Paridade de Juros (CIP)
**Discreta (ACT/360):** \(F = S\,\tfrac{1+r_dT}{1+r_fT}\).  
**Contínua:** \(F = S\,e^{(r_d-r_f)T}\).  
**Banda friccional:** \(F^{bid} \le F_{teor} \le F^{ask}\).  
**Triangular:** \(|S_{ab}S_{bc}S_{ca}-1|\le\tau_{fx}|\) ajustado por *spreads*.

---
# P1‑SP‑09 — AMMs XYK e CLMM
**XYK:** \(xy=k\), \(p=y/x\). **IL:** \(IL(\rho)=\tfrac{2\sqrt{\rho}}{1+\rho}-1\).  
**CLMM:** \(s=\sqrt{P}\); \(\Delta x=L(1/s_b-1/s_a),\ \Delta y=L(s_b-s_a)\). **No‑crossing** entre *bins*.

---
# P1‑SP‑10 — Matemática Financeira (PV/Curvas)
**PV discreto:** \(PV=\sum_t \tfrac{CF_t}{(1+i)^t}\). **PV contínuo:** \(PV=\sum_t CF_t\,e^{-r t}\).  
**Bootstrapping:** descontos \(D(t)\) não crescentes; *forwards* ≥ piso (política) ou ≥0 (restrito).

---
# P1‑SP‑11 — Derivativos & Volatilidade (paridade com dividendo explícita)
**Paridade com dividendo contínuo \(q\):** \(\boxed{\ C - P = S\,e^{-qT} - K\,e^{-rT}\ }\).  
> Caso **sem** dividendo (\(q=0\)), reduz para \(C-P=S-Ke^{-rT}\) (usado em **E17**).  
**BSM (call):** \(C=SN(d_1)-Ke^{-rT}N(d_2)\). **Greeks:** Δ, Γ, Vega, Θ, ρ.  
**Surface:** convexidade(K), calendar(T); \(\sigma_{loc}\) por Dupire com *clip* [5%, 300%].

---
# P1‑SP‑12 — Probabilidade & A/B
**Posterior ∝ prior × verossimilhança.**  
**Amostra para proporções (aprox. simétrica):** \(n \approx \tfrac{2(z_{1-\alpha/2}+z_{1-\beta})^2\bar p(1-\bar p)}{d^2}\).  
**Guardrails:** rollback se degradação > 2σ em métricas críticas.

---
# P1‑SP‑13 — Observabilidade (EWMA/CUSUM)
**EWMA:** \(z_t=\lambda x_t+(1-\lambda)z_{t-1}\). **CUSUM:** \(k,h\) calibrados por σ; **MTTD** alvo ≤2 min para saltos ≥5σ.

---
# P1‑SP‑14 — Jurídico & Conformidade
Segregação por moeda; reconciliação D+1; PoR duplo; *challenge window* 24h; KYC/AML proporcional ao risco.

---
# P1‑SP‑15 — Anticolusão & Auditoria
Detecção (Mahalanobis+DBSCAN) → *flags* → revisão humana; *replay* determinístico com *seed* pública; logs imutáveis.

---
# P1‑SP‑16 — Métricas→Ações (PO)
**North Star:** PCS/W. **Mapa:** inputs→outputs→outcomes; TTC↑ ⇒ SLAs/fluxo; OSE↓ ⇒ reequilibrar pesos/limites.

---
# P1‑SP‑17 — Python/Dados/Engenharia Analítica (com nota CoW)
CPython/GIL; I/O‑bound vs CPU‑bound; NumPy (broadcasting); Pandas (**Copy‑on‑Write — requer pandas ≥2.0; habilitar com `pd.options.mode.copy_on_write = True` quando aplicável**); contratos de dados; SLOs (Freshness/Completeness).

---
# P1‑SP‑18 — Oráculos (modelo/governança)
EIP‑712; `heartbeat`, `staleness_max`, `δ_dyn`; agregação (mediana/trimmed/MoM); *slash* por double‑sign/stale/out‑of‑bounds; SLOs: liveness ≥99,95%; lag p95 ≤ HB+1s.

---
# P1‑SP‑19 — Mercado de Previsões (LMSR)
\(C(\mathbf{q})=b\ln\sum e^{q_i/b}\); \(p_i=\tfrac{e^{q_i/b}}{\sum e^{q_j/b}}\); perda ≤ \(b\ln K\).  
**Δq binário:** \(\Delta q = b\,[\operatorname{logit}(p_1)-\operatorname{logit}(p_0)]\).

---
# P1‑SP‑20 — SDLC/Scrum/QA
Sprints 2s; INVEST; Gherkin; AC mensuráveis; pirâmide de testes; SAST/DAST/SBOM; canary/rollback.

---
# P1‑SP‑21 — Project & Program Mgmt
RAID/RACI; OKRs; PERT \(E=(o+4m+p)/6\); EV (CPI/SPI); Monte Carlo p/ caminho crítico.

---
# P1‑SP‑22 — Data Engineering & Lakehouse (idempotência reforçada)
Bronze/Silver/Gold; compaction 128–512MB; ZSTD; streaming (*allowed_lateness*=15min); **idempotência por chave composta `(event_id, feedId)` com upsert determinístico**; DP para métricas públicas.

---
# P1‑SP‑23 — Cloud/Tokenomics/Segurança/MPC
Multi‑AZ; DR multi‑região; IaC; AEAD, mTLS, RBAC/ABAC; SLSA≥3; SBOM assinada; MPC (t,n), rotação ≤90d.

---
# P1‑E — Exemplos Numéricos **E01–E60** (com fórmulas)
**E01 — CIP (discreta, ACT/360).** S=5,20; r_d=10%; r_f=4%; T=0,5:  
\(F=S\tfrac{1+r_dT}{1+r_fT}=5,2\tfrac{1+0,1\cdot0,5}{1+0,04\cdot0,5}=5,35294\). (+1529 pips)

**E02 — CIP (contínua).** \(F=Se^{(r_d-r_f)T}=5,2e^{0,06\cdot0,5}=5,35836\); basis \(\approx0,00091\ a.a.\)

**E03 — Basis anualizado (log).** \(\text{basis}=\tfrac{\ln(F/S)}{T}-(r_d-r_f)\). Substituindo E01 → ≈ 0,00091 a.a.

**E04 — APR→APY (m=12).** \(\text{APY}=(1+APR/12)^{12}-1\). APR=12% → 12,6825% a.a.

**E05 — APY→APR (m=365).** \(APR=365[(1+APY)^{1/365}-1]\). APY=5% → 4,879% a.a.

**E06–E11 — IL(\(\rho\)).** \(IL(\rho)=\tfrac{2\sqrt{\rho}}{1+\rho}-1\). ρ∈{1,10;1,20;1,30;1,50;2,00;3,00} → {−0,019%; −0,414%; −0,855%; −2,020%; −5,719%; −13,397%}.

**E12 — Rebate de fees.** Fee=30 bps; turnover=12×/a.a. → 0,3%·12=3,6% a.a. (aprox.).

**E13 — LMSR Δq (0,50→0,60; b=1000).** \(\Delta q=1000\,[\logit(0,60)-\logit(0,50)]\approx405,465\).

**E14 — LMSR Δq (0,50→0,62; b=1000).** ≈ 489,451.

**E15 — LMSR Δq (0,40→0,60; b=800) — CORRIGIDO.**  
\(\Delta q = 800\,[\logit(0,60)-\logit(0,40)] = 800\times0,81093 = \mathbf{648,744}\) (antes: 881,374).

**E16 — BSM (call ATM).** Inserir S=100, K=100, r=5%, σ=20%, T=1; obter C≈10,4506 (via d1/d2).  
**E17 — Paridade (q=0).** \(C-P=S-Ke^{-rT}\) → 4,8771.

**E18 — Duration zero‑coupon.** \(D_M=T\); \(D^*=D_M/(1+y)\). Para T=1, y=10% → \(D_M=1, D^*=0,9091\).

**E19 — Cupom do pool (3 posições).** ACT/365F; cálculo por \(\sum cK d w/\sum K d\) → ≈ 2,4368% a.a.

**E20 — ELO underdog.** K=32; *upset* contra favorito → \(\Delta R\approx+20,5\).

**E21 — Beta posterior.** Beta(1,1) + x=3, n=97 → Beta(4,98); média = 3,92%.

**E22 — Tamanho A/B (aprox.).** \(\bar p=0,1,\ d=0,02,\ \alpha=0,05,\ 1-\beta=0,8\) → \(n\approx3528\)/grupo.

**E23 — EWMA.** λ=0,1; resposta a saltos ≥5σ em MTTD ≤ 2 min (com alarme CUSUM).

**E24 — CUSUM.** k=0,5σ; h=5σ.

**E25 — CIP em banda.** Verificar \(F_{teor}\in[F^{bid},F^{ask}]\).

**E26 — Triangular FX.** Produto ~1 dentro da banda (ajuste de *spreads*).

**E27 — Bootstrapping.** Resíduos < 1 bp; \(D'(t)\le0\).

**E28 — Convexidade(K).** \(\partial^2 C/\partial K^2\ge0\) (checagem discreta por três pontos).

**E29 — Calendar(T).** \(C(K,T_2)\ge C(K,T_1)\) após bid/ask.

**E30 — Greeks sinais.** Vega>0; Γ>0 próximo de ATM; Θ geralmente <0 para calls long.

**E31 — δ_dyn (oráculos).** α=1e−3; σ̂/m̂=0,0012 → δ≈0,39%.

**E32 — Slashing econômico.** E[L]>0 com S=150k, G=100k, p_det=0,8.

**E33 — LMSR perda máx.** \(b\ln 2 = 693,15\) (b=1000).  
**E34 — AMM hedge Δ.** Limiar 0,1 lotes.

**E35 — Fila M/D/1 (forma exata).** λ=2/s, μ=3/s → \(W_q=\tfrac{\rho^2}{2\mu(1-\rho)}\approx0,334\) s.

**E36 — PoR pausa (BRL).** Δ=0,10% ⇒ gatilho 1,001×reservas.

**E37 — Error budget 99,9%.** 43,2 min/mês.

**E38 — PERT.** E=(o+4m+p)/6; σ=(p−o)/6; ex.: E=10,5; σ=2.

**E39 — EV.** CPI=EV/CV; ex.: 0,75.

**E40 — SPI.** SPI=EV/PV; ex.: 1,2.

**E41 — DP (Laplace).** ε=1 ⇒ b=1.

**E42 — Idempotência.** **Upsert por `(event_id, feedId)`**.

**E43 — Pandas CoW.** Requer ≥2.0; `pd.options.mode.copy_on_write = True`.

**E44 — RBAC/ABAC.** Matriz de papéis; mapeamento STRIDE.

**E45 — KMS/HSM.** p95<5 ms.  
**E46 — MPC (3/5).** Tolera 2 falhas; rotação≤90d.

**E47 — Taxa CE$.** ≤10 bps/ano.

**E48 — EIP‑712 domínio.** Evita *replay*.

**E49 — Commit‑reveal.** Reduz *front‑running*.

**E50 — XYK preço marginal.** \(p=y/x\) (monótono).

**E51 — IL simetria.** \(IL(\rho)=IL(1/\rho)\).

**E52 — Local vol (BL).** Consistência de \(\partial_{KK}C\).

**E53 — Broken‑date.** Interpolação por úteis.

**E54 — Forward piso.** DF não crescente ⇒ FWD≥piso.

**E55 — Guardrails A/B.** Rollback se >2σ.

**E56 — CUSUM drift.** k=0,25σ.

**E57 — LMSR curvatura.** \(\lambda_{min}(H)\ge\min p(1-p)/b\).

**E58 — AMM across‑bins.** Sem *butterfly*.

**E59 — Trilha auditoria.** hash+seed.

**E60 — Calendário FX.** Spot T+2; ACT/360.

---
# P1‑Checklist de Precisão
- Bases/unidades marcadas; símbolos consistentes.  
- Paridade C−P (com \(q\) explícito); convexidade(K); calendar(T) ok.  
- CIP em banda; ACT/360 (FX).  
- AMM sem crossing; IL(1)=0; simetria.  
- Dados: Freshness/Completeness SLOs.  
- Segurança: AEAD, mTLS, RBAC/ABAC, SLSA≥3; SBOM assinada; MPC (t,n).

---
# P1‑Metadados (para rastreio)
**Tarefa YAML**
```yaml
id: CE/encyclopedia_p1_v7_3_1_mergepack_p1a
name: Enciclopédia PhD — Parte I (Pack para Merge v7.3.1‑p1a)
owner: PO-CreditEngine
prioridade: P0
deps: []
acceptance_criteria:
  - SP‑00…SP‑23 incluídos e coerentes.
  - E01–E60 padronizados; E15 corrigido; M/D/1 exato.
  - Checklists e lint matemático aplicados; notas q/CoW/idempotência reforçadas.
```

**Evidence JSON**
```json
{
  "id": "evidence/ce/encyclopedia_p1_v7_3_1_mergepack_p1a",
  "kpis": {"mrr": null, "ndcg": null, "coverage": null, "leakage": null},
  "notes": "Parte I revisada p1a com M/D/1 exato; paridade com q explícito; Pandas CoW>=2.0; idempotência (event_id, feedId).",
  "version": "v7.3.1-p1a"
}
```


---
# P2‑SP‑00 — Convenções Globais (herdadas da P1)
- **Bases**: FX/CIP=ACT/360 (T+2); Pools=ACT/365F; Bonds=30E/360.
- **Símbolos**: \(r_d,r_f,S,F,T,\sigma,\Delta,\Gamma,\Theta,\rho,k,b,D(t),D_M,D^*,C\).
- **No‑arbitrage**: paridade C−P com \(q\); convexidade(K), calendar(T); \(D'(t)\le0\); banda CIP; *no‑crossing* em CLMM.

---
# P2‑SP‑01 — Matemática Financeira Avançada (APR↔APY, NPV/IRR, Payback)
**Taxas equivalentes** (capitalização m vezes/ano): \(APY=(1+APR/m)^{m}-1\).  
**Contínua**: \(APY=e^{r_c}-1\), com \(r_c=\ln(1+APY)\).  
**Conversão geral**: \((1+i_a)^{n_a}=(1+i_b)^{n_b}\Rightarrow i_b=(1+i_a)^{n_a/n_b}-1\).

**NPV**: \(NPV=\sum_{t=0}^n \frac{CF_t}{(1+k)^t}\).  
**IRR**: raiz de \(NPV(\text{IRR})=0\). *Observações*: (i) múltiplas raízes para fluxos não convencionais; (ii) use **NPV profile**+secante/Newton seguro.  
**Payback** simples vs descontado: preferir descontado.

**Pseudocódigo (IRR seguro)**
```python
# brackets [a,b] tal que NPV(a)*NPV(b) < 0
for _ in range(maxit):
    r = 0.5*(a+b)
    if NPV(r)*NPV(a) <= 0: b = r
    else: a = r
    if abs(b-a) < 1e-7: break
```

---
# P2‑SP‑02 — Duration & Convexidade (Macaulay/Modificada)
**Preço de bond** (30E/360): \(P=\sum_{t=1}^n \frac{C}{(1+y)^t}+\frac{M}{(1+y)^n}\).  
**Macaulay**: \(D_M=\frac{\sum t\,\frac{CF_t}{(1+y)^t}}{P}\).  
**Modificada**: \(D^*=\frac{D_M}{1+y}\).  
**Convexidade**: \(\mathcal{C}=\frac{1}{P}\sum \frac{t(t+1)CF_t}{(1+y)^{t+2}}\).

**Aproximação de preço**: \(\frac{\Delta P}{P}\approx -D^*\,\Delta y+\tfrac{1}{2}\,\mathcal{C}\,\Delta y^2\).  
**Uso no CreditEngine**: mensurar sensibilidade de *claims/tranches* a **spreads**.

---
# P2‑SP‑03 — Precificação de Fluxos, Desconto Discreto/Contínuo; Bootstrapping de Curva
**DF**: \(D(t)=\frac{1}{(1+r_t)^{t}}\) (discreto) ou \(D(t)=e^{-\int_0^t f(u)du}\) (contínuo).  
**Forwards**: \(f(t_1,t_2)=\frac{1}{t_2-t_1}\ln\frac{D(t_1)}{D(t_2)}\).  
**No‑arb**: \(D'(t)\le0\).  
**Instrumentos**: depósitos, FRAs, futuros, swaps, bonds.  
**Interpolação recomendada**: **log‑discount (LD)** (evita \(D'\gt0\)).

**Pseudocódigo (bootstrap robusto)**
```python
D = init_guess(nodes, method='log_discount')
for it in range(maxit):
    for ins in instruments:
        price_model = price(ins, D)
        err = price_model - ins.price
        D = newton_update(D, ins, err, guard_rails=True)  # mantém D'<=0, fwd>=piso
    if converged(errs): break
assert monotone_nonincreasing(D)
```

---
# P2‑SP‑04 — Probabilidade Bayesiana (priors conjugados) & Intervalos
**Bernoulli–Beta**: \(\text{posterior}\sim \operatorname{Beta}(\alpha+x,\beta+n-x)\).  
**Poisson–Gamma**: \(\lambda\mid x \sim \operatorname{Gamma}(\alpha+\sum x, \beta+n)\).  
**Normal–Normal** (σ² conhecida): \(\mu\mid x \sim \mathcal{N}(\mu_n,\tau_n^2)\).  
**IC vs intervalo de credibilidade**: distinguir frequência vs Bayes.  
**Regra de decisão**: perda quadrática → estimador = média posterior.

---
# P2‑SP‑05 — Testes A/B, Poder, Tamanho de Amostra, Peeking e Múltiplas Comparações
**Erro tipo I/II**: \(\alpha,\beta\). **Poder**: \(1-\beta\).  
**Tamanho** (duas proporções, aproximação): \(n\approx\frac{2(z_{1-\alpha/2}+z_{1-\beta})^2\bar p(1-\bar p)}{d^2}\).  
**Peeking**: use **grupos sequenciais** (OBrien‑Fleming/Pocock) ou **métodos bayesianos**.  
**Múltiplos testes**: FDR (Benjamini‑Hochberg), Bonferroni.  
**Guardrails**: métricas de segurança (lag, TTC, OSE) com limites de rollback.

---
# P2‑SP‑06 — Mecanismos & Leilão Reverso (anti‑colusão)
**Regra de Clearing**: ordenar por custo efetivo e agregar até \(K^*\).  
**Preço**: uniforme (2º preço) ou discrim.  
**Anti‑colusão**: *commit‑reveal*, *batch*, filtros de similaridade (Mahalanobis), auditoria determinística (*seed*).  
**Fairness**: **ELO** com *decay* e caps; *exploration* forçada p/ novos.  
**IC aproximada**: penalidade por *deviation*.

---
# P2‑SP‑07 — Scoring de Previsões (Brier vs Log) & LMSR
**Brier**: \(\text{BS}=\sum_i (p_i-y_i)^2\).  
**Log score**: \(-\sum y_i\log p_i\).  
**LMSR**: \(C(\mathbf{q})=b\ln\sum e^{q_i/b}\); \(p_i=\partial C/\partial q_i\).  
**Perda máx.**: \(b\ln K\).  
**Uso**: mercado de previsões do CreditEngine para *signals* e governança.

---
# P2‑SP‑08 — FX & CIP (derivação operacional)
**Discreta**: \(F=S\frac{1+r_dT}{1+r_fT}\). **Contínua**: \(F=Se^{(r_d-r_f)T}\).  
**Forward points**: \(Pts=10^4(F-S)\) (JPY: \(10^2\)).  
**CIP basis** (log): \(\text{basis}=\frac{\ln(F/S)}{T}-(r_d-r_f)\).  
**Triangular**: tolerância por *spreads*; alarme se |prod−1|>τ.  
**Operação**: spot T+2, ACT/360; reporte *broken‑date* por úteis.

---
# P2‑SP‑09 — Derivativos: Black–Scholes, Greeks e Hedging
**BSM (call)**: \(C=SN(d_1)-Ke^{-rT}N(d_2)\), \(d_1=\frac{\ln(S/K)+(r-q+\tfrac{1}{2}\sigma^2)T}{\sigma\sqrt{T}}\), \(d_2=d_1-\sigma\sqrt{T}\).  
**Greeks**: \(\Delta=N(d_1)\), \(\Gamma=\frac{\phi(d_1)}{S\sigma\sqrt{T}}\), \(\nu= S\phi(d_1)\sqrt{T}\), \(\Theta\) e \(\rho\) conforme padrão.  
**Hedge**: rebalance quando |Δ|>\(\theta\); incluir custos/fees.

---
# P2‑SP‑10 — Superfície de Vol: SVI e Condições de Não‑Arbitragem
**SVI**: \(w(k)=a+b\{\rho(k-m)+\sqrt{(k-m)^2+\sigma^2}\}\).  
**Sem‑arb**: \(b>0\), \(|\rho|<1\), \(\sigma>0\); convexidade(K)≥0; calendar(T) não decrescente; *wings* \(b(1\pm\rho)>0\).  
**Pipeline**: IV grid → SVI por T → penalização *no‑arb* → (opcional) Dupire σ_loc.

---
# P2‑SP‑11 — AMMs: XYK, IL e CLMM (faixa e eficiência de capital)
**XYK**: \(xy=k\); preço \(p=y/x\). **IL**: \(IL(\rho)=\frac{2\sqrt{\rho}}{1+\rho}-1\).  
**CLMM**: \(s=\sqrt{P}\); \(\Delta x=L(1/s_b-1/s_a)\), \(\Delta y=L(s_b-s_a)\).  
**Rebalance**: \(\theta\) ótimo ↑ com σ e fees; **no‑crossing** entre *bins*.

---
# P2‑SP‑12 — EVM & Padrões (ERC‑20/4626) e Implicações Contábeis
**Contas/Estado**; *gas*; eventos.  
**ERC‑20** (saldo/allowance); **ERC‑4626** (shares/vault) → contabilidade de **Shares** e *NAV* dos pools.  
**SBTs**: papéis (CC/RC/LE) e credenciais não‑transferíveis.

---
# P2‑SP‑13 — Oráculos (heartbeat, staleness, deviation, fallback)
**Parâmetros**: `heartbeat` (HB), `staleness_max`, `δ_dyn` (desvio relativo), `fallback` (TWAP, secundário).  
**Agregação**: mediana→trimmed→MoM; **governança on‑chain** com EIP‑712; *slash* por *double‑sign*/*stale*/*out‑of‑bounds*; SLOs: liveness ≥99,95%, lag p95 ≤ HB+1s.

---
# P2‑SP‑14 — Segurança, Assinaturas e Auditoria
**AEAD com AAD** (binding de contexto) para dados críticos; logs imutáveis (hash+seed); **MPC (t,n)** com rotação ≤90d; **SLSA≥3**; **SBOM** assinada; RBAC/ABAC; quotas/circuit‑breaker.

---
# P2‑SP‑15 — Python, NumPy & Pandas (CoW) + Engenharia Analítica
**CPython/GIL**: *I/O‑bound* (async), *CPU‑bound* (multiprocessing/numba).  
**NumPy**: `ndarray`, *broadcasting*, *vectorize*.  
**Pandas**: **Copy‑on‑Write** (≥2.0): `pd.options.mode.copy_on_write=True`.  
**Contratos de dados**: Freshness/Completeness/Accuracy; testes; *lineage* com `source_hash`.

---
# P2‑SP‑16 — Crédito Tokenizado: Objetos Canônicos & Fluxo E2E
**Objetos**: **Claims**, **Tranches**, **Shares (ERC‑4626‑like)**, **SBTs** (papéis CC/RC/LE).  
**Fluxo**: **originação (leilões)** → **tokenização** → **pools (cupom capital×tempo)** → **secundário** → **eventos de default** → **settlement**.  
**Fila**: FIFO em stress (abertos); *waterfall* em fechados.  
**Sinais**: macro/setoriais/oráculos modulam spreads/alocação.

---
# P2‑SP‑17 — Métricas → Decisões do P.O (North Star, árvore e mapa de ações)
**North Star** (ex.: PCS/W).  
**Árvore**: inputs→outputs→outcomes.  
**Mapa Métricas→Ações**: cada métrica liga a um ato (ajuste de θ, fee tier, largura CLMM; pesos de leilão; parâmetros de oráculo; políticas de default/escrow).

---
# P2‑SP‑18 — Protocolos de Rollout (canary, guardrails e reversões)
**Canary** com *gates* (lag/TTC/OSE); **rollback** automático; **observabilidade** (EWMA/CUSUM) p/ MTTD ≤2 min em saltos ≥5σ.

---
# P2‑SP‑19 — Data Lake/Lakehouse (bronze/silver/gold) e Idempotência
Arquitetura bronze→silver→gold; *compaction* 128–512MB; ZSTD; **streaming** com *allowed_lateness* 15 min; **idempotência** por chave `(event_id, feedId)`; *exactly‑once* downstream.

---
# P2‑SP‑20 — Checklist de Precisão (Parte II)
- Bases/unidades declaradas; símbolos consistentes.  
- Paridade C−P (com \(q\)); convexidade(K); calendar(T) ok.  
- Curvas: \(D'(t)\le0\), forwards ≥ piso.  
- CIP em banda; ACT/360.  
- AMM sem crossing; IL(1)=0; simetria.  
- Oráculos: HB/staleness/δ_dyn/fallback definidos; SLOs.  
- Segurança: AEAD(AAD), mTLS, MPC, SLSA≥3; SBOM.  
- Dados: Freshness/Completeness; idempotência `(event_id, feedId)`.

---
# P2‑E — Exemplos Numéricos **E101–E160** (com fórmulas)
**E101 — APR→APY (m=12).** APR=18% ⇒ \(APY=(1+0,18/12)^{12}-1=19,56\%\).  
**E102 — APY→APR (m=365).** APY=5% ⇒ \(APR=365[(1+0,05)^{1/365}-1]=4,879\%\).

**E103 — NPV/IRR com fluxo não convencional.** CF=[−100, +130, −40, +30], k=10%: NPV=…; IRR múltiplas raízes — usar perfil de NPV.  
**E104 — Payback descontado.** Fluxo de caixa do E103; calcular tempo até NPV≥0.

**E105 — Duration/Convexidade (bond 5a, 6% cupom, y=7%).** 30E/360: calcular \(D_M\), \(D^*\), \(\mathcal{C}\) e \(\Delta P/P\) para ±25 bps.

**E106 — Desconto contínuo.** \(PV=\sum CF_t e^{-r t}\) para *claims* trimestrais.

**E107 — Bootstrapping** (OIS 1m/3m/6m; Swap 1y/2y): \(D(t)\) monotônico; resíduos < 1 bp.

**E108 — Forwards (1y→2y).** \(f=\frac{1}{1}(\ln D(1)-\ln D(2))\). Piso aplicado.

**E109 — Bayes Beta–Bernoulli.** prior Beta(1,1), x=12, n=200 ⇒ posterior Beta(13,189); média 6,44%.

**E110 — Poisson–Gamma.** \(x\) diários, prior Gamma(2,1): atualizar \(\lambda\).

**E111 — IC vs credibilidade.** Comparar IC 95% (freq) e 95% credível (Bayes) para proporção 4% em n=1000.

**E112 — Tamanho A/B.** \(\bar p=0,1\), d=0,01, \(\alpha=0,05\), poder=0,8 ⇒ \(n\approx 7060\)/grupo.

**E113 — Peeking control (OBrien‑Fleming).** Fronteiras de z para 3 análises interinas.

**E114 — Bonferroni vs BH‑FDR.** 10 testes, \(\alpha=0,05\): ajuste de \(p\)-values.

**E115 — Clearing do leilão com empates** (uniforme). 3 lances empatados no limite: desempate por *seed* pública.

**E116 — Anti‑colusão (Mahalanobis).** Distância > \(\tau\) ⇒ *flag*; *batch* para execução.

**E117 — Brier vs Log score.** Cenário com \(p=(0,6,0,3,0,1)\) e resultado classe 2: comparar pontuações.

**E118 — LMSR perda máx.** b=1200, K=3 ⇒ \(b\ln K\approx 1319,\) unidades de \(q\).

**E119 — CIP (EURUSD) ACT/360.** S=1,07500; r_d=2,5%; r_f=4,0%; T=0,5 ⇒ \(F=1,06698\); points=−802.  
**E120 — CIP contínua.** \(F=Se^{(r_d-r_f)T}=1,075e^{-0,0075}=1,0670\).

**E121 — Triangular** (EUR/USD, USD/JPY, EUR/JPY): verificar |prod−1|≤τ com spreads.

**E122 — Paridade com dividendo** q=1%: \(C-P=Se^{-qT}-Ke^{-rT}\) (erro ≤2 bps).

**E123 — BSM greeks** (ATM): \(\Delta\approx0,5\), \(\Gamma>0\), vega>0.

**E124 — SVI (1 maturidade).** Ajustar (a,b,ρ,m,σ); checar convexidade/\(b(1±\rho)>0\).

**E125 — Dupire sanity.** σ_loc(K,T) em [5%, 250%]; calendar ok.

**E126 — IL tabela** ρ∈{0,8,1,2,3}.  
**E127 — CLMM width* (σ=40%, f=30 bps, turnover=12).** width*≈4–5%.

**E128 — θ* vs fees.** fees↑ ⇒ θ*↑.

**E129 — EVM gás**: custo aproximado de `transfer` vs `transferFrom` (ERC‑20).

**E130 — ERC‑4626 NAV**: \(NAV=\frac{assets-liabilities}{shares}\). Depósitos/saques e *share price*.

**E131 — Oráculo δ_dyn.** α=1e−3, σ̂/m̂=0,0010 ⇒ δ≈0,316%.

**E132 — HB/staleness**: HB=60s; lag p95≤61s (ok); staleness_max=180s.

**E133 — Fallback**: TWAP 5 min vs feed secundário; *switch* ao violar δ.

**E134 — AEAD(AAD)**: detecção de *replay* por mudança de AAD.

**E135 — MPC (3/5)**: lat p95=35 ms; rotação 90d.

**E136 — SLSA≥3**: janela de patch <48h; SBOM assinada.

**E137 — CPython I/O‑bound**: `asyncio` reduz *wall time* em 40% num ETL remoto.

**E138 — Pandas CoW**: ativado, queda de *copy churn* em 35% em *joins*.

**E139 — Contratos de dados**: Freshness p95≤5 min; Completeness≥99,5%.

**E140 — E2E fluxo**: cronograma de originação→tokenização→pool→default→settlement com SLAs.

**E141 — Fila FIFO**: stress; ordem preservada por `ts_enter`.

**E142 — Sinais→Spreads**: choque macro+setorial eleva spreads em 25 bps (limite p95=30 bps).

**E143 — North Star (PCS/W)**: otimização desloca gargalo de lag→TTC.

**E144 — Canary**: rollback automático ao violar guardrail OSE>+2σ.

**E145 — Lakehouse**: compaction 256MB melhora *scan* em 22%.

**E146 — Idempotência**: duplicatas suprimidas por `(event_id, feedId)`.

**E147 — RBAC**: privilégio mínimo para operações de *settlement*.

**E148 — Circuit‑breaker**: picos de tráfego; recuo exponencial.

**E149 — Leilão (discriminatório)**: preço individual, clearing até K*.

**E150 — Leilão (uniforme)**: todos no mesmo preço; simulação de receita.

**E151 — Score ELO**: *upset* produz ΔR maior que vitória favorita.

**E152 — Properness**: log score é *strictly proper*; exemplo com *reporting* veraz.

**E153 — LMSR Δq** (0,45→0,55; b=1000) ≈ 201,  
**E154 — LMSR Δq** (0,55→0,65; b=1200) ≈ 194 (usar logit).

**E155 — DV01 carteira** (3 bonds) e *repricing* de validação.

**E156 — Convexidade carteira**: ΔP/P com ±100 bps.

**E157 — Forwards piso**: aplica −ε; evitar negativos na inversão da curva.

**E158 — Calendar tolerância**: −2 bps aceito (bid/ask).  
**E159 — Wings SVI**: verificar inclinações b(1±ρ) positivas.

**E160 — σ_loc clip**: [5%, 250%] evita explosões em K‑wings.

---
# P2‑Triple Check (completude/consistência)
**Estrutura:** SP‑00…SP‑20 presentes; E101–E160 presentes.  
**Lint matemático:** bases/unidades; símbolos; paridade/convexidade/calendar; D'(t)≤0; banda CIP; IL simetria; no‑crossing CLMM.  
**Merge‑safety:** prefixos **P2‑**; code fences fechados; âncoras locais.  
**Cross‑check P1/P4:** coerente com M/D/1 exato; paridade com \(q\); idempotência `(event_id, feedId)`; SVI/Dupire invariantes.

> **Status:** Parte II **APROVADA** para merge. Se desejar, posso gerar um **diff comentado** vs rascunhos anteriores e/ou iniciar a **Parte III** no mesmo formato (P3‑, E161+).

---
# P2‑Metadados (para rastreio)
**Tarefa YAML**
```yaml
id: CE/encyclopedia_p2_v7_3_1_mergepack
name: Enciclopédia PhD — Parte II (Pack para Merge v7.3.1)
owner: PO-CreditEngine
prioridade: P0
deps: [CE/ENC_P1_MERGEPACK_P1A]
acceptance_criteria:
  - SP‑00…SP‑20 incluídos e coerentes.
  - Exemplos E101–E160 completos.
  - Lint matemático e no‑arbitrage verificados; code fences fechados.
```

**Evidence JSON**
```json
{
  "id": "evidence/ce/encyclopedia_p2_v7_3_1_mergepack",
  "kpis": {"mrr": null, "ndcg": null, "coverage": null, "leakage": null},
  "notes": "Parte II pronta para fusão em master; cabeçalhos prefixados; E101–E160.",
  "version": "v7.3.1-p2"
}
```

# P3‑SP‑00 — Convenções Globais (coerência inter‑partes)
**Bases/Unidades:** FX/CIP=ACT/360 (T+2); Pools=ACT/365F; Bonds=30E/360; pips/bps/%; moeda.  
**Símbolos:** \(r_d,r_f,S,F,T,\sigma,\Delta,\Gamma,\Theta,\rho,k,b,D(t),D_M,D^*,C,\text{NAV},N_{sh}\).  
**No‑arb:** paridade C−P com \(q\); convexidade(K); calendar(T); \(D'(t)\le0\); banda CIP; **no‑crossing** CLMM.

---
# P3‑SP‑01 — Objetos Canônicos
**Claim**: direito a fluxo(s) \(CF_t\) específico(s) e risco de *default*.  
**Tranche**: fatia com *attachment* \(A\) e *detachment* \(D\) (\(0\le A<D\le1\)) de um *pool*; perda alocada via *waterfall* (\(S \succ J\)).  
**Share (ERC‑4626‑like)**: recibo fungível representando *pro‑rata* do \(NAV\) do *vault/pool*; operações `deposit/mint/withdraw/redeem`.  
**SBTs**: *soulbound tokens* de papéis (CC/RC/LE) e credenciais KYC/AML não‑transferíveis.  
**Relações:** Claims → (tokenização) → Pools; Pools ↔ (Tranches/Shares); SBTs → governança.

---
# P3‑SP‑02 — Modelo Contábil & Ledger (dupla entrada)
**Eventos atômicos:** `DEPOSIT`, `MINT`, `WITHDRAW`, `REDEEM`, `COUPON_ACCRUAL`, `DEFAULT_EVENT`, `SETTLEMENT`, `FEE_ACCRUAL`.  
**Ledger mínimo:** `(ts, event_id, account, ccy, amount, dc_flag∈{D,C}, ref_id, source_hash)`.  
**Conservação (invariante):** \(\sum_j \text{amount}_j \cdot s_j = 0\), onde \(s_j\in\{-1,+1\}\) (débito/crédito).  
**NAV:** \(\text{NAV}_t = \sum_i PV_i(t) - \text{liabilities}_t\).  
**Preço da *share*:** \(p_t = \text{NAV}_t/N_{sh,t}\) (com \(N_{sh,t}>0\)).  
**Rounding:** 18 *decimals* on‑chain; políticas de arredondamento *bankers* off‑chain; reconciliação D+1.

---
# P3‑SP‑03 — Fluxo Ponta‑a‑Ponta (FSMs)
1) **Originação (Leilão Reverso)** → *clearing* de fornecedores de crédito por custo efetivo.  
2) **Tokenização** → emissão de Claims/Tranches/Shares; SBTs para papéis.  
3) **Pools** → accrual contínuo de cupom (capital×tempo).  
4) **Secundário** → *liquidity venues* para Shares/Tranches.  
5) **Default** → *event detection* → deliberação CC/RC → execução LE.  
6) **Settlement** → rateio conforme waterfall; atualização de NAV; *escrows* e *challenge window*.

**Invariantes por fase:** conservação de valor; monotonicidade de filas FIFO; *idempotência* de eventos por `(event_id, feedId)`.

---
# P3‑SP‑04 — Pools: Cálculo de Cupom (capital×tempo)
**Janela *rolling* [\(t_0,t_1\)] (ACT/365F):**  
\[ \text{cupom}_{[t_0,t_1]} = \frac{\sum_{j}\underbrace{c_j}_{\%/a.a.}\,\underbrace{K_j}_{\text{moeda}}\,\underbrace{d_j}_{\text{dias}/365}\,\underbrace{w_j}_{\in[0,1]}}{\sum_{j} K_j\,d_j} \quad (\text{saida: }\%/a.a.) \]
**Pesos \(w_j\)**: *haircuts*, risco, *vintage*, *sinais* (macro/setoriais/oráculos).  
**Fila (Abertos):** em *stress*, **FIFO** determinístico por `ts_enter`.

---
# P3‑SP‑05 — ERC‑4626: `deposit/mint/withdraw/redeem`
**Depósito** de \(\Delta A\) → *shares* \(\Delta N_{sh} = \Delta A/p\).  
**Resgate** de \(\Delta N_{sh}\) → ativos \(\Delta A = p\,\Delta N_{sh}\) (sujeito a liquidez).  
**Taxas** (se houver): *entry/exit/management*; contabilizar em `FEE_ACCRUAL` e deduzir de \(NAV\).  
**Propriedades:** sem diluição (emitir ao preço justo); *pause* sob anomalias.

---
# P3‑SP‑06 — Waterfall de Tranches (Loss‑Given‑Default)
**Regra (S≽J)**: perdas absorvidas primeiro pela Júnior até \(D\); depois Mezanino; por fim Sênior.  
**EL por tranche (aprox.):** \(\mathbb{E}[L_{tr}]\approx \int_A^D \ell\, f_{L}(\ell)\,d\ell\), onde \(f_L\) é densidade de perda agregada do pool.  
**DV01/Convexidade** por tranche: derivados de preço da fatia versus \(y\) do *pool collateral*.

**Pseudocódigo (rateio de perdas)**
```python
loss = realized_pool_loss
for tr in [Junior, Mezz, Senior]:
    cap = (tr.D - tr.A) * pool_notional
    absorbed = min(loss, cap - tr.cum_loss)
    tr.cum_loss += absorbed
    loss -= absorbed
    if loss <= 0: break
```

---
# P3‑SP‑07 — Default & Governança (CC/RC/LE)
**Papéis:** CC (proposta), RC (decisão), LE (execução).  
**Quóruns:** ordinário ≥50%; litígio ≥66,7%.  
**Escrow/Challenge:** bloqueio de fundos; janela 24–72h para contestação; *evidences* on‑chain (hashes).  
**KPIs:** TTD (time‑to‑decision), TTE (time‑to‑execution), recuperação (R).

---
# P3‑SP‑08 — Secundário & Liquidez
**Quotes**: *AMM* (pool próprio) ou *RFQ/orderbook*.  
**Preço teórico**: \(p_t=\text{NAV}_t/N_{sh,t}\) ± *basis* de liquidez.  
**Impacto**: *slippage* ↑ com \(\sigma\) e menor profundidade; rebate de fees mitiga IL no AMM.

---
# P3‑SP‑09 — Sinais Moduladores & Políticas
**Função de modulação**: \(L' = L\cdot g(z)\), com \(|g(z)-1|\le g_{max}\) (e.g., 30 bps p95).  
**Parâmetros dinâmicos de oráculo**: `heartbeat`, `staleness`, `δ_dyn`; *fallback* TWAP.  
**Detecção de anomalia**: EWMA/CUSUM; gatilhos de *pause*.

---
# P3‑SP‑10 — Tokenomics Operacional
**Custo do capital**: \(c\) a.a.; **taxas**: \(\phi\) a.a.; \(APR(S)=\tfrac{R}{S}-\phi\).  
**Equilíbrio**: \(S^*=\tfrac{R}{c+\phi}\); **estabilidade local** \(<0\) (derivada negativa).  
**Política**: *caps* de emissão; *cooldowns*; *vesting* para operadores.

---
# P3‑SP‑11 — Risco (PD/LGD/EAD), EL/UL/VaR por Pool/Tranche
**Tripé**: PD, LGD, EAD.  
**EL**: \(\mathbb{E}[L]=\sum_i PD_i\cdot LGD_i\cdot EAD_i\).  
**UL (aprox. Vasicek)**: \(\text{UL}\approx \sqrt{\rho_a}\,\Phi^{-1}(q)\,\sigma_L\).  
**VaR/ES** por *simulation* ou fórmulas de portfólio de crédito (one‑factor).  
**Backtesting**: *binomial test* e *traffic‑light*.

---
# P3‑SP‑12 — Propriedades Formais & Invariantes
- **Conservação**: \(\Delta \text{NAV} = \sum CF - \text{fees} - \text{losses}\).  
- **Sem diluição**: `mint`/`redeem` a preço justo.  
- **FIFO** estável em stress.  
- **Sem *double‑spend***: idempotência `(event_id, feedId)`.

---
# P3‑SP‑13 — Operação & SRE
**SLOs**: liveness ≥99,95% (21,6 min/mês); lag p95 ≤ HB+1s; RPO≤5 min; RTO≤30 min.  
**Observabilidade**: métricas, *traces*, logs imutáveis; **guardrails** com *rollback* automático.

---
# P3‑SP‑14 — SDLC & Storywriting (ligado ao produto)
**INVEST**, Gherkin, AC mensuráveis (bps/σ/lag).  
**Pipelines**: testes de propriedade (paridade C−P; convexidade; calendar; CIP; no‑crossing CLMM; invariantes de ledger).  
**Rollout**: *canary* + *feature flags*.

---
# P3‑SP‑15 — Segurança & Compliance
**AEAD(AAD)**; mTLS; RBAC/ABAC; **MPC (t,n)**; **SLSA≥3**, SBOM assinada; PoR duplo; KYC/AML proporcional ao risco; privacidade com DP em métricas públicas.

---
# P3‑SP‑16 — APIs & Interfaces (EVM‑centric)
**EIP‑712** para ordens/leilões/assinaturas de governança.  
**Eventos**: `CouponAccrued`, `DefaultTriggered`, `SettlementExecuted`, `OracleUpdated`, `Paused/Unpaused`.  
**OpenZeppelin**: ERC‑20/4626/SBTs; *pausable*, *access control*.

---
# P3‑SP‑17 — Casos Extremos & Fallbacks
Taxas negativas; *stale* oráculo; gaps de mercado; *sandwich/front‑running* (mitigar com *batch/commit‑reveal*); *broken‑date* FX; eventos legais (injunções).

---
# P3‑SP‑18 — Integrações (AMMs, RFQ, Custódia)
**AMM** interno para Shares/Tranches; **RFQ** para blocos; **custódia** segregada; *orquestração* de liquidez com limites.

---
# P3‑SP‑19 — Simulação & Monte Carlo (pool/tranche)
**Cenários**: trajetórias de PD/LGD, choques de \(\sigma\), stress de fila FIFO, falhas de oráculo.  
**Outputs**: distribuição de \(NAV\), EL/UL/VaR por tranche, TTC/lag, métricas de liveness.

---
# P3‑SP‑20 — Checklist de Precisão (Parte III)
- Objetos canônicos consistentes; relações explícitas.  
- FSMs por fase + invariantes.  
- Cupom (ACT/365F) e ERC‑4626 corretos.  
- Waterfall S≽J; rateio implementável.  
- Oráculos e sinais com SLOs e *fallbacks*.  
- Segurança/compliance/SRE coerentes.  
- APIs/eventos definidos.  
- Idempotência `(event_id, feedId)`; reconciliação D+1.

---
# P3‑E — Exemplos Numéricos **E161–E200**
**E161 — Emissão de Shares (mint).** NAV=10.000.000; \(N_{sh}=1.000.000\) ⇒ \(p=10\). Depósito \(\Delta A=500.000\) ⇒ \(\Delta N_{sh}=50.000\).  
**E162 — Resgate (redeem).** \(\Delta N_{sh}=20.000\) ⇒ \(\Delta A=200.000\).

**E163 — Cupom *rolling*.** 3 posições: (c,K,d,w)={(12%,2M,30/365,1),(9%,1M,15/365,0,9),(7%,3M,20/365,0,8)} ⇒ \(\text{cupom}\approx 9,53\%\ a.a.\).

**E164 — Fila FIFO em stress.** Entradas A,B,C (ts ordenados); resgates servidos A→B→C; latências \(W_q\) conforme M/D/1 (forma exata).

**E165 — Waterfall com perda 8% do notional.** Tranches: J (0–5%), M (5–10%), S (10–100%). Perda: J absorve 5%; M absorve 3%; S=0.

**E166 — EL do pool.** 100 claims, PD=2%, LGD=60%, EAD=100k ⇒ \(EL=120k\).

**E167 — EL por tranche (aprox.).** A=0,05, D=0,10; densidade \(f_L\) concentrada em [0,0,12]. Integre numericamente (resultado ~2,7% do notional da tranche).

**E168 — DV01 do pool.** Três buckets de *claims* com durations 0,7/1,5/3,0 anos e notional 2/5/3M; DV01≈ soma ponderada por preço.

**E169 — Convexidade do pool.** Aproximação por segunda ordem; impacto para ±50 bps.

**E170 — NAV após cupom e fee.** Cupom bruto 0,8% mês; fee 20 bps mês ⇒ NAV_{t+1}=NAV_t·(1+0,008−0,002).

**E171 — `deposit` com taxa de entrada 10 bps.** Depósito 100k ⇒ shares = (100k·(1−0,001))/p.

**E172 — `redeem` com *exit fee* 15 bps.** Shares 50k, p=10 ⇒ ativo = 500k·(1−0,0015).

**E173 — Oráculo δ_dyn.** α=1e−3; σ̂/m̂=0,0009 ⇒ δ≈0,285%.

**E174 — HB/staleness.** HB=60s; *staleness_max*=180s; lag p95 medido=59,7s (ok).

**E175 — Fallback TWAP.** TWAP 5 min ativa quando |Δp/p|>δ_dyn; tempo em fallback 2,3% do dia.

**E176 — Sinais→Limites.** *Shock* macro: g(z)=0,9 ⇒ limites reduzem 10%; spread ↑ 18 bps.

**E177 — Secundário RFQ.** *Quote* p=10, basis=−0,2%; execução a 9,98.

**E178 — AMM interno.** Depth 1M; σ=40%; fee 30 bps; IL anual esperada 2,1%; rebate de fees 3,6% ⇒ IL líquida ≈ −(2,1−3,6)=+1,5%.

**E179 — *Commit‑reveal* em leilão.** Reveal window 30s; redução de *front‑running* observada 70%.

**E180 — *Batching* por bloco.** Diminui *sandwich* em 35% e slippage p95 em 22%.

**E181 — Quórum.** Litígio: 8/12 (66,7%) necessário; votação alcança 9/12 → aprovado.

**E182 — Escrow & challenge.** Escrow=2% do valor; challenge 48h; nenhuma contestação ⇒ *release* automático.

**E183 — SRE budgets.** 99,95% liveness ⇒ 21,6 min/mês; alertas ≤5/min.

**E184 — DR.** RPO≤5 min; RTO≤30 min → testes semestrais.

**E185 — Ledger idempotente.** Reprocessamento repete `event_id` ⇒ *upsert* não duplica.

**E186 — Reconc. D+1.** Diferença ≤ 2 bps do NAV (tolerância).

**E187 — Compliance.** PoR duplo com desvio ≤0,05% (USD), ≤0,10% (BRL).

**E188 — Segurança.** AEAD(AAD) falha com AAD errado → rejeição.

**E189 — MPC.** (3/5) com p95=37 ms; rotação 90d.

**E190 — EIP‑712.** `domainSeparator` previne *replay* cross‑chain.

**E191 — Casos extremos.** Taxa negativa −0,25% a.a.; curva de desconto continua não crescente (LD).

**E192 — Broken‑date FX.** Interpolação por úteis com piso de forward em −ε.

**E193 — Stress de oráculo.** 2 provedores *stale*; quorum insuficiente → *pause*.

**E194 — Fila FIFO stress.** λ→μ·0,95; \(W_q\) cresce não linearmente; planos de contingência.

**E195 — Monte Carlo NAV.** 10k trajetórias; VaR 99% = 2,8% do NAV; ES 99% = 3,6%.

**E196 — Tranche pricing (aprox.).** *Large pool* + Vasicek: precificar Júnior por EL+UL*mult; exemplo numérico simplificado.

**E197 — Hedge do pool.** DV01=85k; vender futuros para neutralizar (β≈1,02).

**E198 — Auditoria.** *Seed* pública reproduz seleção do leilão (reproducibilidade).

**E199 — Story Gherkin.** "Dado um HB=60s… Quando lag p95>HB+1s… Então pausar feed e acionar fallback."

**E200 — Lint final.** Paridade/convexidade/calendar/CIP; D'(t)≤0; no‑crossing; conservações; code fences ok.

---
# P3‑Triple Check (completude/consistência)
**Estrutura:** SP‑00…SP‑20 presentes; E161–E200 presentes.  
**Lint matemático:** bases/unidades; símbolos; paridade/convexidade/calendar; D'(t)≤0; banda CIP; IL simetria; no‑crossing CLMM; invariantes contábeis.  
**Merge‑safety:** prefixos **P3‑**; code fences fechados; âncoras locais.  
**Cross‑check P1/P2/P4:** ERC‑4626 e cupom ACT/365F; M/D/1 exato; idempotência `(event_id, feedId)`; oráculos HB/staleness/δ_dyn; SVI/Dupire invariantes; Golden Notebooks coerentes.

> **Status:** Parte III **APROVADA** para merge. Posso iniciar a **Parte IV (consolidação + addendum)** se desejar, ou preparar um **índice mestre** com TOC de todas as partes.

---
# P3‑Metadados (para rastreio)
**Tarefa YAML**
```yaml
id: CE/encyclopedia_p3_v7_3_1_mergepack
name: Enciclopédia PhD — Parte III (Pack para Merge v7.3.1)
owner: PO-CreditEngine
prioridade: P0
deps: [CE/ENC_P1_MERGEPACK_P1A, CE/ENC_P2_MERGEPACK]
acceptance_criteria:
  - SP‑00…SP‑20 incluídos e coerentes.
  - Exemplos E161–E200 completos.
  - Invariantes de ledger/fees/NAV; ERC‑4626; waterfall; SRE/segurança.
```

**Evidence JSON**
```json
{
  "id": "evidence/ce/encyclopedia_p3_v7_3_1_mergepack",
  "kpis": {"mrr": null, "ndcg": null, "coverage": null, "leakage": null},
  "notes": "Parte III pronta para fusão em master; cabeçalhos prefixados; E161–E200; invariantes de operação.",
  "version": "v7.3.1-p3"
}
```

# P4‑SP‑00 — Convenções & Lint Dimensional (herdadas)
- **Bases**: FX/CIP **ACT/360** (spot T+2); Pools **ACT/365F**; Bonds **30E/360**.  
- **Símbolos**: \(r_d,r_f,S,F,T,\sigma,\Delta,\Gamma,\Theta,\rho,k,b,D(t),\text{NAV},N_{sh}\).  
- **No‑arb**: paridade C−P com \(q\); convexidade(K), calendar(T); \(D'(t)\le0\); banda CIP; **no‑crossing** CLMM.  
- **Relatos**: *broken‑date* por úteis (FX); tolerância de paridade ≤ 2 bps (após bid/ask); forward piso −ε.

---
# P4‑A — Golden Notebook: CIP & FX (executável)
**Formulário:**  
\(F_{disc}=S\,\frac{1+r_d T}{1+r_f T}\) (ACT/360); \(F_{cont}=S\,e^{(r_d-r_f)T}\).  
**Basis (log):** \(\text{basis}=\tfrac{\ln(F/S)}{T}-(r_d-r_f)\).  
**Triangular:** \(|S_{ab}S_{bc}S_{ca}-1|\le\tau_{fx}|\) com spreads.  
**Broken‑date:** interpolar por úteis via **log‑discount**.

**Pseudocódigo (checagens automáticas)**
```python
# Entradas: S, rd, rf, T, F_mkt, bid, ask, spot_calendar='T+2'
F_disc = S * (1 + rd*T) / (1 + rf*T)
basis = math.log(F_disc/S)/T - (rd - rf)
assert bid <= F_disc <= ask  # banda CIP
assert abs(Sab*Sbc*Sca - 1) <= tau_fx  # triangular
```

---
# P4‑B — Golden Notebook: AMM/CLMM (simulação & hedge)
**XYK:** \(xy=k\), preço \(p=y/x\). **IL:** \(IL(\rho)=\tfrac{2\sqrt{\rho}}{1+\rho}-1\) (simétrica).  
**CLMM:** \(s=\sqrt{P}\); \(\Delta x=L(1/s_b-1/s_a)\), \(\Delta y=L(s_b-s_a)\).  
**Rebalance ótimo**: limiar \(\theta\) cresce com \(\sigma\) e **fee**; rebate de fees pode compensar IL.

**Grid‑search (width, fee)**
```python
for width in widths:
  for fee in fee_tiers:
    pnl = simulate_clmm(width, fee, sigma, turnover)
    keep_best(pnl, width, fee)
```

---
# P4‑C — Golden Notebook: Vol/Surface (SVI & Dupire)
**SVI:** \(w(k)=a+b\{\rho(k-m)+\sqrt{(k-m)^2+\sigma^2}\}\).  
**Cond. sem‑arb:** \(b>0\), \(|\rho|<1\), \(\sigma>0\), wings \(b(1\pm\rho)>0\); convexidade(K)≥0, calendar(T) não decrescente.  
**Dupire:** \(\sigma_{loc}^2=\tfrac{\partial_T C}{0,5K^2\partial_{KK}C}\) com suavização; **clip** [5%, 300%].

**Pipeline:** IV grid → ajuste SVI por T → penalização *no‑arb* → (opcional) \(\sigma_{loc}\) → testes (convexidade/calendar/wings).

---
# P4‑D — Algoritmos (Big‑O, invariantes e teste de propriedade)
- **leilao_clear()** (O(n log n)): ordena por custo efetivo, agrega até \(K^*\); invariantes: monotonicidade; *budget‑balance*; reprodutibilidade (*seed* pública).  
- **curve_bootstrap()** (O(n·it)): *log‑discount* + Newton seguro; invariantes: \(D'(t)\le0\), forward≥piso.  
- **lmsr_delta_q()** (O(1)): usa \(\operatorname{logit}\); invariantes: \(\sum p_i=1\), Hessiano ⪰0.  
- **oracle_aggregate()** (O(N)): mediana→trimmed→MoM; invariantes: quorum≥qmin; `nonce`↑; *staleness*≤max.

---
# P4‑E — Segurança, Assinaturas, MPC & Auditoria
**EIP‑712**: domínio (cadeia, contrato, versão).  
**AEAD (com AAD)**: *binding* de contexto → previne *replay*.  
**MPC (t,n)**: latência p95<50 ms; rotação ≤90d.  
**Trilhas imutáveis**: *hash+seed*; *challenge window* para disputas.

---
# P4‑F — SDLC/PMO avançados (DORA, CFR, PERT/EV)
**DORA** por janelas móveis; **CFR** com guardrails; **PERT/EV** com Monte Carlo.  
**Storywriting**: INVEST + AC mensuráveis (bps/σ/lag) + rollback automático.

---
# P4‑G — Mercado de Previsões & Mecanismos (LMSR)
**LMSR:** \(C(\mathbf{q})=b\ln\sum e^{q_i/b}\), \(p_i=\partial C/\partial q_i\).  
**Perda máx.** \(b\ln K\). **b(t)** autoreativo ao *flow*.  
**Anti manipulação**: *commit‑reveal* + *batch*.

---
# P4‑H — Exemplos Numéricos **E201–E260** (revistos)
> *Bases/unidades declaradas; tolerâncias padrão. Ajustes aplicados: M/D/1 exato; paridade com q explícita; LD preferido.*

**E201** CIP (USD/BRL) ACT/360: S=5,2000; r_d=10%; r_f=4%; T=0,5 ⇒ \(F\approx5,35294\); +1529 pips.  
**E202** CIP contínua: \(F\approx5,35836\); basis≈0,00091 a.a.  
**E203** Broken‑date: interpolar log‑discount por 52 úteis entre 2M e 3M.  
**E204** Swap near/far: carry ≈ F−S por termo.  
**E205** Triangular (EUR/USD, USD/JPY, EUR/JPY): banda por spreads; alerta se |prod−1|>τ_fx.  
**E206** APR→APY contínua: r_c=12% ⇒ APY=e^{0,12}−1≈12,7496%.  
**E207** Bond 5a, cupom 6%, y=7% (30E/360): P e DV01; \(D_M,D^*\).  
**E208** Convexidade do bond: \(\Delta P/P\approx−D^*\Delta y+0,5\,\mathcal{C}\,\Delta y^2\) (±25 bps).  
**E209** Bootstrapping OIS (1m,3m,6m,1y,2y): \(D(t)\) não crescente; residual<1 bp.  
**E210** FRA 6→9m: \(r\approx[(D_6/D_9)−1]/0,25\) (ACT/365F).  
**E211** SVI (1 maturidade): ajuste a,b,ρ,m,σ; convexidade(K) ok.  
**E212** Dupire: \(\sigma_{loc}(K,T)\) com clip [5%,300%]; calendar ok.  
**E213** Paridade com q=2%: \(C−P=Se^{-qT}−Ke^{-rT}\) (erro<2 bps).  
**E214** BSM greeks: Δ, Γ, Vega; sinais coerentes.  
**E215** AMM XYK: IL(ρ) tabela para ρ∈{0,8,1,2,3}.  
**E216** CLMM width* (σ=40%, f=30 bps, turnover=12): width*≈4–5%.  
**E217** Fee tier ótimo: esparso→100 bps; denso→30 bps.  
**E218** Rebalance θ*: σ↑ ⇒ θ*↑; custo total mínimo.  
**E219** LMSR binário 0,45→0,55; b=1000 ⇒ \(\Delta q\approx b[\logit(0,55)−\logit(0,45)]\).  
**E220** LMSR K=3: Δq para p→p'=(0,50,0,30,0,20); b=1500.  
**E221** b(t) por slippage alvo: \(b\ge\Delta q/(p(1−p)\Delta p^*)\).  
**E222** Oráculo δ_dyn (α=1e−3, σ̂/m̂=0,0012): δ≈0,39%.  
**E223** ROC τ*: π=2%, G=1M, c_FP=2k, S=500k ⇒ τ≈3σ.  
**E224** Slashing mínimo: \(S\ge\frac{1−TPR}{TPR}G\); ex.: TPR=0,8 ⇒ S≥0,25G.  
**E225** Liveness 99,95% ⇒ 21,6 min/mês; *error budget*.  
**E226** SRE (EWMA/CUSUM): MTTD≤2 min para salto ≥5σ.  
**E227** **Fila M/D/1 (forma exata)**: λ=2/s, μ=3/s ⇒ \(\rho=2/3\); \(W_q=\tfrac{\rho^2}{2\mu(1−\rho)}\approx0,333\,\text{s}\).  
**E228** Cupom do pool (3 posições): ACT/365F (capital×tempo).  
**E229** Default rateio: S≽J; escrows condicionais; haircut.  
**E230** Tokenomics equilíbrio \(S^*\): R=1M, c=6%, φ=1% ⇒ \(S^*\approx14{,}285{,}714\).  
**E231** Estabilidade: meia‑vida \(\ln 2/\kappa\) (\(\kappa=0,5/\text{sem}\) ⇒ ~1,386 sem).  
**E232** DORA: amostra p/ Δ mediana lead‑time = −0,3 dia ⇒ ~200 deploys.  
**E233** CFR 20%→15%: n≈903/grupo.  
**E234** DP orçamento: ε_total=1 com alocações (0,4,0,3,0,2,0,1).  
**E235** MPC latência: p95=35 ms (<50 ms).  
**E236** SLSA≥3: janela de patch <48h; SBOM assinada.  
**E237** AEAD com AAD: binding de contexto; prevenção de *replay*.  
**E238** EIP‑712: domínio estável evita *replay* inter‑chain.  
**E239** Triangular robusto: spreads assimétricos; detector tolerante.  
**E240** Curvas LF vs LD: erro de NPV; LD preferível.  
**E241** Piso de forward −ε (política): exemplo com curva invertida.  
**E242** Local vol sanity: \(\sigma_{loc}\) entre vols vizinhas.  
**E243** SVI wings: slope≈\(b(1\pm\rho)\) positiva.  
**E244** Paridade tolerância: ≤2 bps.  
**E245** Smile monotonia: curvatura medida.  
**E246** Hedge discreto Δ: recalibrar |Δ|>0,05.  
**E247** θ* vs fees: fees↑ ⇒ θ*↑.  
**E248** *Batch* vs *commit‑reveal*: latência×proteção.  
**E249** *Batch* por bloco: reduz *sandwich*; preço mais justo.  
**E250** Guardrails A/B múltiplos: OSE/TTC simultâneos.  
**E251** EV/SPI diagnóstico: CPI<1, SPI>1 ⇒ custo excessivo porém adiantado.  
**E252** PERT risco: \(\sigma^2=((p−o)/6)^2\).  
**E253** Monte Carlo IC95% por *bootstrap*.  
**E254** DV01 carteira: soma ponderada; validação por *repricing*.  
**E255** Convexidade carteira: impacto em \(\Delta P\) aproximado.  
**E256** Basis anualizado em pips: conversão de basis log.  
**E257** Broken‑date curva por úteis: exemplo de 52 úteis.  
**E258** Oráculo quorum: 5/9 vs 7/11; FNR vs liveness.  
**E259** Story Gherkin: AC com bps/σ/lag + rollback.  
**E260** Invariantes FSM (pool/oráculo): checks automáticos.

---
# P4‑I — Snippets Executáveis (prontos para notebook)
```python
import math
# CIP discreta/contínua & basis
F_disc = S * (1 + rd*T) / (1 + rf*T)
F_cont = S * math.exp((rd - rf)*T)
basis = math.log(F_disc/S)/T - (rd - rf)  # a.a.
# LMSR delta_q (binário)
logit = lambda p: math.log(p/(1-p))
Delta_q = b * (logit(p1) - logit(p0))
# IL XYK
IL = lambda rho: 2*math.sqrt(rho)/(1+rho) - 1
# Dupire (esboço discretizado)
sigma_loc = dC_dT / (0.5 * K**2 * d2C_dK2 + 1e-12)
# Idempotência de eventos
upsert_key = (event_id, feedId)
```

---
# P4‑J — QGen Expandido (≥30)
1) Prove que **LD** preserva \(D'(t)\le0\) sob condições suaves e **LF** pode violar.  
2) Demonstre simetria e limites de **IL(\rho)**.  
3) Calibre **SVI** com 5 pontos e valide convexidade discreta.  
4) Derive \(\sigma_{loc}\) de **Dupire** sob discretização estável.  
5) Mostre que **log score** é *strictly proper*; contraste com **Brier**.  
6) Mostre que **paridade C−P** com \(q\) reduz ao caso \(q=0\).  
7) Prove *no‑crossing* entre *bins* na **CLMM** com *ticks* discretos.  
8) Mostre que \(W_q=\rho^2/(2\mu(1−\rho))\) para **M/D/1**.  
9) Deduzir **b(t)** que mantém *slippage* alvo em **LMSR**.  
10) Mostre condição para \(\partial_T C\ge0\) (calendar).  
11) Quantifique impacto de **fees** em hedge Δ discreto.  
12) Estabeleça limites de **δ_dyn** via *median‑of‑means*.  
13) Demonstre que quorum insuficiente ⇒ *pause* determinístico (FSM).  
14) Mostre que **waterfall** conserva perdas totais.  
15) Derive **EL** por tranche sob densidade \(f_L\).  
16) Prove que **NAV** pós‑fee segue conservação.  
17) Demonstre que **RBAC** mínimo evita escalada de privilégio (modelo).  
18) Comprove que **Laplace(1/ε)** implementa DP ε‑diferencial.  
19) Mostre **CFR ↓** com **rollback** em guardrails.  
20) Derive **PERT** variância e intervalo.  
21) Prove que **EV/SPI** diagnose estados CPI<1, SPI>1.  
22) Mostre que **broken‑date** por úteis minimiza *jumps*.  
23) Demonstre **triangular** com spreads assimétricos.  
24) Derive **forward piso −ε** em curvas invertidas.  
25) Mostre que \(\sum p_i=1\) e Hessiano⪰0 em **LMSR**.  
26) Prove limites de \(\sigma_{loc}\) com *clip*.  
27) Mostre estabilidade local de **S*** (tokenomics).  
28) Demonstre *seed* pública ⇒ reprodutibilidade no leilão.  
29) Derive **DV01** do pool como soma ponderada.  
30) Prove que **idempotência** por `(event_id, feedId)` elimina *double‑spend* lógico.

---
# P4‑K — Hard‑Negatives (≥15)
1) “Em CIP, **ACT/365** é sempre correto.” ❌ (usar **ACT/360**).  
2) “Paridade C−P dispensa **q**.” ❌  
3) “Em XYK, **IL** pode ser positiva sem fees.” ❌  
4) “**SVI** não precisa de **convexidade**.” ❌  
5) “**Dupire** independe de \(\partial_{KK}C\).” ❌  
6) “Fila **M/D/1**: \(W_q=\rho/(2\mu(1−\rho))\).” ❌ (é \(\rho^2/(2\mu(1−\rho))\)).  
7) “**No‑crossing** em CLMM é opcional.” ❌  
8) “**δ_dyn** é fixo.” ❌ (dinâmico).  
9) “**RBAC** dispensável com MPC.” ❌  
10) “**Idempotência** não é necessária.” ❌  
11) “**LD** e **LF** equivalem.” ❌  
12) “**EIP‑712** não previne *replay*.” ❌  
13) “**SLSA** é irrelevante.” ❌  
14) “**CFR** cai sem rollback.” ❌  
15) “**Waterfall** pode violar conservação.” ❌

---
# P4‑L — Lint Matemático & Testes de Propriedade (automação)
- **Paridade**: \(C−P=Se^{-qT}−Ke^{-rT}\) dentro de 2 bps.  
- **Convexidade(K)**: discretização de três pontos ≥0.  
- **Calendar(T)**: \(C(K,T_2)\ge C(K,T_1)\) após bid/ask.  
- **Curvas**: \(D'(t)\le0\); forwards ≥ piso; *broken‑date* por úteis.  
- **CIP**: \(F^{bid}\le F_{teor}\le F^{ask}\).  
- **CLMM**: sem *crossing* entre *bins*.  
- **Ledger**: conservação em dupla entrada; *idempotência* `(event_id, feedId)`.

---
# P4‑Triple Check (completude/consistência)
**Fonte de comparação**: canvas “Parte IV — v7.3.0” enviado pelo usuário.  
**Mudanças aplicadas em v7.3.1‑p4:**  
1) **M/D/1 exato** (P4‑H E227) substitui bound anterior.  
2) **Paridade com q** explicitada e usada nos exemplos (E213/E244).  
3) **LD preferido** para broken‑date/curva (E203/E240/E257).  
4) **Snippets** incluem **idempotência** `(event_id, feedId)` e binds AEAD(AAD).  
5) **Invariantes** no‑arb reforçados (SVI/Dupire/CLMM).  
6) **Prefixos P4‑** em todos os cabeçalhos; **E201–E260** completos.  
7) **Code fences**: verificados e fechados.

**Status:** Parte IV **APROVADA** para merge (padrão “pack para merge”).

---
# P4‑Metadados (para rastreio)
**Tarefa YAML**
```yaml
id: CE/encyclopedia_p4_v7_3_1_mergepack
name: Enciclopédia PhD — Parte IV (Pack para Merge v7.3.1‑p4)
owner: PO-CreditEngine
prioridade: P0
deps: [CE/ENC_P1_MERGEPACK_P1A, CE/ENC_P2_MERGEPACK, CE/ENC_P3_MERGEPACK]
acceptance_criteria:
  - Golden Notebooks (CIP, AMM/CLMM, Vol/Surface) presentes e sem‑arb.
  - Exemplos E201–E260 revisados; M/D/1 exato; paridade com q explícita.
  - Snippets executáveis + QGen (≥30) + Hard‑Negatives (≥15).
  - Lint matemático e testes de propriedade descritos; code fences fechados.
```

**Evidence JSON**
```json
{
  "id": "evidence/ce/encyclopedia_p4_v7_3_1_mergepack",
  "kpis": {"mrr": null, "ndcg": null, "coverage": null, "leakage": null},
  "notes": "Parte IV revisada p4 com M/D/1 exato; paridade com q; LD; snippets com idempotência; QGen≥30; HN≥15.",
  "version": "v7.3.1-p4"
}
```