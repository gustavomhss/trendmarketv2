# CreditEngine — v10 Tabela de Mercado

> **Canônica**: indexa o **v9 — Master Catalog (Intermediação 100%)** como fonte única de escopo.  
> **Data/versão**: 2025‑09‑09 (America/Bahia)  
> **Legenda das colunas**  
> • **Volume de mercado anual (BR)**: ordem de grandeza 2024–2025 YTD; quando não há série pública → **N/D (proxy sugerido)**.  
> • **% Juros convencional**: faixas típicas de mercado **a.a.** (ou **yield/spread** quando aplicável).  
> • **% Juros sugerida CE**: referência neutra para **formação por RFQ/leilão/book**, p.ex., **CDI/IPCA/SOFR + spread alvo** ou **faixa**.  
> • **Fluxo CE**: como o CE intermedeia ponta‑a‑ponta.  
> • **Vantagem parte A** = **Tomador**; **Vantagem parte B** = **Credor/Pool/Investidor**.  
> • **Oportunidades/Desafios/Impedimentos**: highlights de go‑to‑market; **Impedimentos** = riscos/regulatório/infra.  
> • Valores são **indicativos**; para cotações firmes usar módulos **P1..P7** e políticas por item.

---

## 1) Modalidades de Crédito — PF
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Empréstimo pessoal (não consignado) | N/D (proxy: concessões PF livre BCB) | 70–120% | **CDI + 10–25%** | RFQ/leilão; contrato; liquidação | Taxa/limite justos | Risco/retorno calibrado | Cross‑sell PF | Inadimplência alta | Dados assimétricos | Best‑ex + score granular | Orquestra RFQ + antifraude + open finance |
| Consignado (INSS/público/privado) | N/D (estoque PF) | 22–60% | **CDI + 4–12%** | RFQ; averbação; repasses | Previsibilidade | Baixo default | Escala convênios | Regras por ente | Limites de margem | Políticas como código | Integra folha/averbação com eventos |
| Cartão — parcelado (sem emissão) | N/D (fluxo via adquirentes) | 40–80% | **CDI + 8–18%** | RFQ por arranjo; liquida lojista | Parcela previsível | Curto prazo diversificado | Embedded em PSP | Chargeback | Dependência do arranjo | Tape de recebíveis + risco sacado | Leilão por lotes + waterfall |
| Overdraft/cheque especial | N/D | até ~151% (teto) | **CDI + 12–30%** | Book dinâmico; limite | Liquidez imediata | Yield alto com controle | Ajuste em tempo real | Uso adverso | Teto regulatório | Telemetria e limites dinâmicos | Reprecificação automática por risco |
| BNPL varejo | N/D | 30–80% | **CDI + 6–16%** | Leilão em cestas | Aprovação rápida | Volumes em varejo | Parcerias marketplaces | Fraude | Qualidade de dados | Antifraude + score transacional | Lotes com pro‑rata e *eligibility* |
| Veículos (CDC) | ~R$ 180–220 bi (concessões/ano)* | 25–30% | **CDI + 6–14%** | RFQ; gravame; seguro | Prazo/longo | Ativo real | Esteiras com dealers | Recuperação | Depreciação | LTV/haircuts corretos | Integra gravame/seguro/eventos |
| Imobiliário/home equity | ~R$ 180–220 bi (SBPE/FGTS/ano)* | 11–13% + TR | **IPCA + 4–7%** | RFQ/Book; avaliação; registro | Taxas baixas | Lastro forte | HE e cash‑out | Cartórios | Prazos longos | Provas e LTV | Workflow cartorial + waterfall |
| Estudantil/saúde | N/D | 20–40% | **CDI + 6–12%** | RFQ; liquida prestador | Acesso | Fluxo previsível | Parcerias setoriais | Risco renda | Mensuração de conclusão | Dados alternativos | Runbooks por parceiro |
| Microcrédito PF | N/D | 30–70% | **CDI + 8–18%** | Book; regras de grupo | Inclusão | Diversificação | ONGs/IFs | Custo unitário | Informalidade | Automação de campo | Cobrança leve + dados alt |
| Leasing / rent‑to‑own | N/D | 20–40% | **CDI + 6–12%** | RFQ; posse/uso | Acesso ao bem | Residual capturado | Verticais nicho | Reprocesso | Jurídico | Contratos claros | Telemetria do ativo |
| Salary advance/13º | N/D | 20–45% | **CDI + 5–10%** | RFQ; folha | Dinheiro rápido | Risco baixo (folha) | HRTechs | Turnover | Risco empregador | Vínculo folha | Renovações automáticas |
| SBL — contra investimentos | N/D | 15–30% | **CDI + 3–8%** | RFQ; LTV/margem | Taxa baixa | Colateral líquido | Alta penetração | *Gap* de dados | Volatilidade | Haircuts dinâmicos | Oráculos de preço |
| Margin lending | N/D | 15–30% | **CDI + 4–9%** | Book; margem | Alavancagem | Taxa competitiva | Brokers parceiros | Volatilidade | *Margin calls* | Regras de risco | Monitoração contínua |
| HEA/Shared Appreciation | N/D | N/A (equity share) | **Deságio alvo 30–50% do upside** | RFQ; eventos | Sem parcela | *Upside* | Niche marketing | Avaliação | Liquidez | Contratos claros | *Triggers* de eventos |
| Embedded credit PF | N/D | 25–60% | **CDI + 6–14%** | Leilão em lote | Fricção zero | Deal‑flow | Acesso a dados | Fraude | Qualidade KYC | Intent‑based RFQ | Anti‑fraude + PSPs |

*Observação: ordens de grandeza indicativas (SBPE/FGTS/auto) 2024–2025.

---

## 2) Modalidades de Crédito — PJ/SME/Corporate
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Capital de giro/limites | N/D (PJ livre) | 20–35% | **CDI + 5–12%** | RFQ/Book | Liquidez flexível | Taxa por risco | Cross‑sell | Covenants | Dados ERP | Best‑ex com score | OF + ERP + watchers |
| Antecipação de recebíveis | N/D | 15–35% | **CDI + 4–10%** | Leilão por lote | Caixa rápido | Diversificação sacados | Volumes com registradoras | Concentração | Qualidade de título | *Tape* rico | Leilão single‑price + cessão |
| Desconto de duplicatas/invoice | N/D | 15–35% | **CDI + 4–10%** | RFQ/Leilão | Previsibilidade | Yield atrativo | Sacados âncora | Disputas | Registro | Verificabilidade | *Waterfall* vinculado |
| Vendor/Confirming (SCF) | N/D | 12–25% | **CDI + 3–8%** | Leilão por fornecedor | Custo baixo | Risco do anchor | Penetração base fornecedores | *Onboarding* | Integração ERP | Curva âncora | Pro‑rata por data |
| Linhas rotativas (RCF) | N/D | 18–30% | **CDI + 5–10%** | Book | Flexibilidade | *Fees* | Grandes *accounts* | Gestão limites | Agência | Automação RCF | Regras e *draws* |
| Term Loan | N/D | 15–28% | **CDI + 4–9%** | RFQ | Prazo/estabilidade | Previsão retorno | *Club deals* | Covenants | Documentação | Playbook *term sheet* | Fechamento com trustees |
| Unitranche/Direct lending | N/D | 20–30% | **CDI + 6–12%** | Book/Leilão | Velocidade | Retorno alto | Private credit local | Dados limitados | Estruturas | Data room | Covenants padrão |
| Mezanino (PIK/warrants) | N/D | 25–40% | **CDI + 10–18%** | RFQ | Flex × capital | Upside | Casos especiais | *Kickers* | Jurídico | Estruturas *template* | Gatilhos PIK |
| Bridge loans | N/D | 18–30% | **CDI + 6–12%** | RFQ | Rapidez | Spread | Janelas de mercado | Risco *take‑out* | Documentação | *Fast lane* | *Take‑out* mapeado |
| Project finance | N/D | 12–20% | **IPCA + 3–6%** | Book/Leilão | Longo prazo | Tranches | Infra/energia | Complexidade | Seguros/EPC | DSCR/OC/IC | Cash waterfall |
| Asset‑based lending (ABL) | N/D | 15–28% | **CDI + 5–10%** | RFQ | Taxa menor c/ colateral | Proteção | Estoques/AR | Avaliações | Custódia | *Borrowing base* | Certificados + *haircuts* |
| Warehouse lines (originadores) | N/D | CDI ± | **CDI + 2–6%** | RFQ | Funding escalável | Pool construído | Para securitizar | Testes de pool | Governança | *Eligibility* | Preparação take‑out |
| Forfaiting | N/D | SOFR/EUR + 2–6% | **SOFR + 2–5%** | RFQ | Sem recurso | Risco pós‑embarque | Comex | País/sacado | Doc trade | Precificação país | *Settlement* externo |
| Floorplan/Inventory | N/D | 15–28% | **CDI + 5–10%** | RFQ | Giro estoque | Controle | Varejo durável | Inspeção | Desvalorização | Telemetria estoque | *Curtailments* |
| Borrowing‑base commodities | N/D | 12–22% | **CDI + 4–8%** | RFQ | *Carry* | Diversificação | Agro/mineração | Qualidade | Logística | *Receipts* e oráculos | LTV dinâmico |
| Litigation finance | N/D | N/A | **IRR alvo 18–28%** | RFQ | Sem recurso | Alta convexidade | Nicho | *Case risk* | Jurídico | Modelos de *milestones* | Comitês CE |
| IP‑backed | N/D | N/A | **CDI + 6–12%** | RFQ | Monetiza intangível | Upside royalties | Tech/entretenimento | Valuation | Execução | *Escrow* e licenças | Cláusulas de gatilho |
| Fund finance (Capital call/NAV) | N/D | CDI ± | **CDI + 2–6%** | RFQ/Book | Velocidade | Baixa PD (LP) | PE/Infra/VC | Documentos | Governança | Leitura de LPAs | Covenants LP |
| B2B BNPL / dynamic discounting | N/D | 12–25% | **CDI + 3–8%** | Leilão | Liquidez fornecedor | Deságio atrativo | Penetração anchors | Dados | Disputas | Curva âncora | Orquestra datas |

---

## 3) Trade Finance
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| LC | N/D | SOFR/EUR + 2–6% (fees) | **Fee 1–3% a.a.** | RFQ; docs | Garantia de pagamento | Fee recorrente | Exportadores | Discrepâncias | Sanções | Motor de regras | Checklists e OCR |
| SBLC | N/D | Fee 1–4% | **1,5–3%** | RFQ | Garantia | Baixo sinistro | Infra/obras | *Expiry* | Legal | Watchers de *expiry* | Rotinas de renovação |
| Aval/Fiança | N/D | Fee 1–6% | **1–4%** | RFQ | Alavanca rating | *Fee* | Obras/judicial | Execução | Colateral | Políticas objetivas | Agenda de eventos |
| Cobrança documentária | N/D | Spread baixo | **CDI + 1–3%** | Book | Menor custo | *Float* | Cadeias export | Prazos | Documentos | Automação | SLA e *alerts* |
| ACC/ACE/FINIMP | Dezenas bi/ano | SOFR + spread | **SOFR + 2–5%** | RFQ | Custo baixo | Garantias ECA | Comex | Volatilidade FX | Limites | FX router + hedge | *Best‑ex* multi‑dealer |
| Warehouse receipts finance | N/D | 12–22% | **CDI + 4–8%** | RFQ | Estoque vira caixa | Proteção | Agro | Qualidade | Auditoria | Oráculos de qualidade | Inspeções programadas |
| Tolling/off‑taker backed | N/D | 12–20% | **CDI + 4–7%** | RFQ | Contrato âncora | Risco mitigado | Energia/indústria | Prazos | *Counterparty* | Validação *off‑take* | Covenants operacionais |

---

## 4) Mercado de Capitais — Dívida (Primário/SEC)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Debêntures (incl. incentivadas) | ~R$ 400–500 bi (2024) | DI/IPCA + spread | **DI + 1,5–4,5%** | Book | Captação ampla | Transparência | Infra/energia | Janelas | Coordenação | Dados ricos | Monitora covenants |
| Bonds corporativos (sênior/sub HY) | US$ dezenas bi (BR) | UST/SOFR + spread | **SOFR + 2–6%** | Book/RFQ | Base global | Curva externa | Diversificação | FX/ratings | Reg. externo | Integra janelas | Pós‑negócio eventos |
| CP/NP | Dezenas bi | DI + spread | **DI + 1,5–4%** | RFQ/Book | *Bridge* tático | Rapidez | Janela curta | *Roll* | Registro | RFQ multi‑dealer | Fechamento rápido |
| MTN/Reg S/144A | US$ bi | SOFR + spread | **SOFR + 2–5%** | Book | Flex docs | Base global | 144A/Reg S | *Disclosure* | Governança | Datas e curvas | Covenants tracking |
| CRI/CRA | ~R$ 150–250 bi | IPCA/DI + | **IPCA + 3–7%** | Book | Benefício fiscal | Lastro real | Imob/agro | Documental | Registro | *Tape*/eligibility | Waterfall eventos |
| FIDC (quotas) | ~R$ 200–300 bi (PL) | CDI ± | **CDI + 2–6%** | Book | Tranching | Spread ajustado | P2P/AR | OC/IC | Governança | Testes automáticos | Servicing integrado |
| Covered/LIG | N/D | DI/IPCA + | **DI + 1–3%** | Book | Custo baixo | Segurança | Imob | Estruturação | Rating | OC/IC/NAV | Eventos/calls |
| Perpétuos/AT1/CoCos | N/D | DI/SOFR + | **SOFR + 4–8%** | Book | Capital híbrido | Retorno alto | Bancos | Complexidade | Triggers | Dados e eventos | Alertas de capital |
| Municipal/Project bonds | N/D | IPCA + | **IPCA + 3–7%** | Book | Infra local | Base local | Municípios | Receita vinculada | Regras fiscais | Dados projeto | DSCR watchers |
| Schuldschein | N/D | EUR swap + | **€STR + 1–3%** | RFQ | Docs simples | *Clubs* | Alemanha | Jurisd. | Documentação | Playbook | Book por janela |
| Social/Impact bonds | N/D | IPCA/DI + | **DI + 1,5–4%** (ratchets) | Book | *Impact* | KPIs | Social | Medição | Verificação | KPIs→taxa | Oráculos de KPI |
| SLL/SLB (ratchets) | N/D | IPCA/DI + | **DI + 1,5–4%** (ratchets) | Book | Custo reduzido | Disciplina ESG | Corp. ESG | KPIs | *Greenwashing* | Conexão de métricas | Ajuste automático de taxa |

---

## 5) Securitização & Estruturados
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| ABS/RMBS/CMBS | N/D | DI/IPCA + | **DI + 2–6%** | Book | Off‑BS | Tranches | Imob/consumo | Dados pool | OC/IC | Tape/testes | Servicing/eventos |
| CLO/CDO | N/D | DI/SOFR + | **DI + 3–7%** | Book | Funding loans | Alocação risco | Private credit | Dados loan | Complexidade | Tape/IC/OC | Telemetria de loan |
| Marketplace lending ABS | N/D | DI + | **DI + 3–7%** | Book | Escala orig. | Spread justo | P2P/originadores | Heterogeneidade | Qualidade tapes | Normalização | Score por originador |
| NPL securitization | N/D | N/A | **IRR 18–30%** | Book | *De‑risk* balanço | *Recovery* | *Workout* | Recuperação | Jurídico | Dados *workout* | Gatilhos e *servicers* |
| Whole business securitization | N/D | IPCA/DI + | **DI + 3–6%** | Book | Monetiza fluxo | Tranches | Varejo/serviços | KPIs | Auditoria | KPIs↔taxa | *Covenants* operacionais |
| Re‑REMIC | N/D | DI + | **DI + 2–5%** | Book | Otimização | Spread | Casos especiais | Complexidade | Regras | Transparência | Camadas e limites |
| CLN (Credit‑Linked Notes) | N/D | Spread de crédito | **Spread 1,5–4%** | RFQ/Book | Transferência risco | Yield | Hedge | Eventos crédito | ISDA/Docs | Mapeamento eventos | Liquidação conectada |
| COE/Notas estruturadas | N/D | — | **RFQ** | RFQ | Hedge tático | *Payoff* custom | PB/wealth | Complexidade | Emissor | Roteamento | KIDs + guardrails |
| Structured deposits | N/D | — | **RFQ** | RFQ | Caixa com opcionalidade | Captação | PB | Preço | Transparência | Best‑ex | Comparador taxas |
| Certificates/Participation | N/D | — | **RFQ** | RFQ | Delta‑one | Acesso | Exposição | Tracking | Emissor | NAV eventos | *What‑ifs* |

---

## 6) Money Market & Depósitos (Funding)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| CDB/RDB/LC/LCI/LCA | Alto | DI/IPCA | **DI − 0,2…+2%** | RFQ/Book | Comparativo claro | Captação ágil | Funding cliente | Regulação | *Onboarding* | Roteamento | Best‑ex + trilhas |
| CDs/Time deposits | Médio | SOFR/EUR + | **SOFR + 0,5–2%** | RFQ | Diversificação | Base global | Cross‑border | KYC/FX | Jurisdição | Router multi‑moeda | Liquidação parceiros |
| CP/ECP | Médio | DI + | **DI + 1,5–4%** | RFQ/Book | Janela rápida | Bridge barato | Janelas | *Roll* | Registro | Execução neutra | APIs coordenadores |
| Repos/Reverse repos | Muito alto | DI ± | **RFQ** | RFQ/Book | Caixa seguro | Colateralizado | Gestão de caixa | Colateral | Mesa externa | Integração preço/colateral | Regras de alocação |
| Securities lending/borrowing | Alto | Fee mercado | **RFQ** | RFQ/Book | *Borrow* eficiente | *Lend* monetiza | Arbitragem | *Recalls* | CCP | *Locates* integrados | Rate‑time priority |
| Collateral upgrade | Médio | Spread colateral | **RFQ** | RFQ | Melhor uso de colateral | Spread extra | *Switches* | Liquidez | Tri‑party | Algoritmos de *switch* | Regras e PoR |
| Tri‑party dynamic allocation | Alto | — | — | Book | Eficiência | Margem menor | Algoritmos | Integração | Custódia | OMS + simulação | Alocação ótima |

---

## 7) Derivativos de Crédito (via dealers)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| CDS single‑name | Baixo (local) | prêmio (bps/ano) | **RFQ** | RFQ multi‑dealer | Hedge puro | Precificação clara | Casos corporativos | Liquidez | ISDA/CSA | Roteamento neutro | Timeseries + eventos |
| CDS índice (CDX/iTraxx) | Baixo | prêmio (bps/ano) | **RFQ** | RFQ | Hedge carteira | Execução rápida | Netting | Liquidez | ISDA | Melhor preço | *Marks* e *rolls* |
| Tranches/Nth‑to‑default | Residual | prêmio | **RFQ** | RFQ | Hedge concentrado | *Carry* | Carteiras concentradas | Modelagem | Docs | Transparência | Triggers programados |
| LCDS / TRS loans/bonds | Pontual | prêmio | **RFQ** | RFQ | Delta‑one crédito | Sem caixa | Arbitragem funding | Liquidez | ISDA | *Best‑ex* | *Cash‑flow* vinculado |
| Opções crédito/Swaptions CDS | Pontual | prêmio | **RFQ** | RFQ | Convexidade | Proteção | Vol events | Precificação | ISDA | *What‑ifs* | Watchers barreira |
| Credit spread options (CSO) | Pontual | prêmio | **RFQ** | RFQ | Hedge spread | Alvo risco | Casos HY | Vol/liq | ISDA | Comparação neutra | Curvas integradas |
| Options on TRS (OTRS) | Pontual | prêmio | **RFQ** | RFQ | Convexidade TRS | Gestão fina | Books complexos | Modelagem | ISDA | Telemetria | Greeks conectados |
| Quanto/FX‑linked CDS | Pontual | prêmio | **RFQ** | RFQ | Hedge FX+crédito | Proteção mista | Emissores offshore | Basis/FX | ISDA | Router FX + crédito | *Workflow* conjunto |

---

## 8) Derivativos de Juros e FX (hedge)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Swaps de juros (DI/fixo‑flutuante) | Muito alto | — | **RFQ** | RFQ; margem; *rolls* | Hedge duration | Fluxo recorrente | Carteiras grandes | Margem | ISDA | RFQ multi‑dealer | Métricas de *best‑ex* |
| Cross‑currency swaps (CCS) | Alto | — | **RFQ** | RFQ | Hedge multi‑moeda | Spread CCS | Export/infra | Basis | ISDA | Router multi‑dealer | *Best‑ex* + eventos |
| FX Forwards/Swaps | Muito alto | — | **RFQ** | RFQ | Simples/rápido | Spread FX | Todos | Liquidez | Corretoras | Roteamento | *TCA* de FX |
| Futuros (DI/Treasuries/FX) | Muito alto | — | **Book** | Brokers/B3 | Hedge tático | Execução | Tesouraria | Margens | B3 | Integra OMS | SLAs de execução |
| Opções (IR/FX) | Alto | — | **RFQ/Book** | Dealers/brokers | Proteção/convexidade | Prêmios | Vol | Precificação | ISDA | Simulação | Watchers barreira |

---

## 9) Lending & Borrowing (Web3)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Pools sobrecolateralizados | N/D (global; BR s/ recorte) | on‑chain APR 3–12% | **APR alvo 3–10%** | Book; contas segregadas | Liquidez 24/7 | Risco controlado | Yield com prova | De‑peg | Custódia | Provas/PoR | Haircuts dinâmicos |
| Pools permissionados | N/D | 8–20% | **DI + 3–8%** | RFQ/Book | Crédito institucional | Mandatos | RWAs | KYC | Liquidez | Policies→constraints | KPIs e covenants |
| LRT/LP/NFT colateral | N/D | var. | **Haircuts + taxa RFQ** | Book | Taxa menor | Diversificação | Colaterais novos | Oráculos | Liquidez | Invariantes | Watchers de risco |
| RWA tokenizados | Crescente | var. | **DI + 2–6%** | RFQ | Liquidez rápida | Pool seguro | FIDC/AR token | Regulação | Custódia | Eventos verificáveis | Waterfall on‑chain |
| Intent‑based RFQ/auction | Emergente | var. | **Single‑price** | Auction por *solvers* | Melhor execução | Competição | RFQ sem atrito | Ataques MEV | Tech | Neutralidade | Provas de execução |

---

## 10) Derivativos cripto/tokenizados
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Perpétuos | Alto (global) | funding ± | **RFQ/Book** | Brokers/CEX/DEX | Hedge fine | Liquidez | Yield/basis | Vol | Custódia | *Best‑ex* multi‑venue | TCA + oráculos |
| Futuros datados | Alto | — | **Book** | Brokers | Calendários | Rolagem | Estratégias | Margem | Custódia | OMS | SLAs |
| Opções | Médio/alto | — | **RFQ/Book** | Brokers | Proteção | Prêmio | Vol tokens | Volatilidade | Liquidez | Simulações | Watchers |
| Funding‑rate swaps | Emergente | funding swap | **RFQ** | Protocolos | Trava funding | Spread | Perps | Oráculos | Liquidez | *What‑ifs* | Roteamento |
| TRS/CFDs tokenizados | Emergente | — | **RFQ** | Protocolos | Exposição delta | Sem caixa | Cash‑and‑carry | Marcação | Custódia | Conciliação | Eventos |
| Vol tokens/power perps/barriers | Emergente | — | **RFQ/Book** | Protocolos | Estratégias vol | Yield | Nichos | Complexidade | Liquidez | Guardrails | Métricas de risco |

---

## 11) Tokenização de Dívida/Recebíveis (RWA)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| T‑bills/bonds tokenizados | Crescente | yield soberano | **RFQ/Book** | Custódia/NAV | Caixa com yield | Liquidez | Cash mgmt | Regulação | Custódia | Integra NAV | Eventos/cupom |
| Invoices/recebíveis tokenizados | Crescente | var. | **DI + 2–6%** | RFQ | Liquidez rápida | Diversificação | FIDC/AR | Qualidade | KYC | Verificabilidade | Servicing on‑chain |
| FIDC quotas tokenizadas | Pilotos | DI ± | **DI + 2–5%** | Book | Acesso RT | Governança | Pools permissionados | Regulação | Custódia | NAV/OC/IC | Eventos |
| NPL tokens | Nicho | IRR | **IRR 18–30%** | RFQ | Desconto alto | Upside recovery | *Workout* | Jurídico | LGPD/dados | Oráculos de recovery | Esteiras *workout* |
| Home equity tokens | Nicho | — | **IPCA + 3–6%** | RFQ | Liquidez imóvel | Lastro forte | HE token | Registro | Cartórios | LTV/registro | Eventos de venda |

---

## 12) Stablecoins & Colateral Digital
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Fiat‑backed (USDC/USDT) | ~R$ 30–47 bi/mês (BR transacionado) | — | **Book** | Cash mgmt | Liquidez | Baixo *fric.* | On/off‑ramps | De‑peg | Risco emissor | Provas de reserva | Haircuts/limites |
| Cripto‑colateralizadas (DAI/LUSD) | N/D | — | **Book** | Colateral | Modularidade | *Trustless* | Pools | Oráculos | De‑peg | Quórum de oráculos | Watchers de peg |
| Algorítmicas híbridas | N/D | — | **Book** | Colateral | Rendimento | Nichos | Pilotos | Risco desenho | Liquidez | Guardrails | *Allowlist* |
| Commodity‑backed | N/D | — | **Book** | Cash mgmt | Proteção inflação | Diversificação | Ouro/commodities | Custódia | *Auditability* | PoR | *Haircuts* |
| RWA‑backed (T‑bill) | N/D | — | **Book** | Caixa com yield | Rendimento | Segurança | Treasuries | Regulação | Custódia | NAV/PoR | Eventos |
| Yield‑bearing stables | N/D | — | **Book** | Cash com yield | Rendimento | *Composability* | Tesouraria | Risco contrato | Liquidez | Guardrails | Limites por emissor |
| CBDC (rail) | Pilotos | — | — | Liquidação | D+0 | Segurança | Integra rails | Indefinições | Acesso | Integra modular | Testes controlados |

---

## 13) Produtos Estruturados DeFi
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Covered‑call/put vaults | N/D | — | **Book** | Estratégias | Renda | Taxa implícita | High‑net‑worth | Vol | Liquidez | Guardrails | Monitor *greeks* |
| Principal‑protected on‑chain | N/D | — | **RFQ/Book** | Opção + T‑bill | Proteção | Fluxo estável | RWA | KIDs | Estrutura | Comparador de payoff | Simulador |
| Delta‑neutral basis | N/D | — | **Book** | Cash‑and‑carry | Renda | Basis capture | Perps/futuros | Basis | Custódia | Router multi‑venue | TCA |
| Tranching real yield (RWA/LP) | N/D | — | **Book** | Senior/junior | Proteção | Alavanca | Pools | OC/IC | Liquidez | Waterfall | *Watchers* |
| Dual currency on‑chain | N/D | — | **RFQ** | Multi‑moeda | *Yield* | Diversificação | FX | Vol FX | Liquidez | Guardrails | Oráculos FX |

---

## 14) Seguros Descentralizados (DeFi)
| Cobertura | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Smart contract/oracle/CEX | N/D | prêmio | **RFQ/Book** | Anexar apólices | Proteção | Retenção | RWAs/DEX | Dados | Aceitação | Integração eventos | Gatilhos LGD |
| Custodial/slashing | N/D | prêmio | **RFQ/Book** | Anexar apólices | Proteção | Retorno | Staking | Dados | Aceitação | Gatilhos | Watchers slashing |
| De‑peg stablecoins | N/D | prêmio | **RFQ** | Anexar apólices | Proteção | Retorno | Tesouraria | *Peg* | Oráculos | Quórum | Alarmes depeg |
| Paramétrico climático/índice | N/D | prêmio | **RFQ** | Índice→payout | Agro | *Basis risk* | Agrofin | Oráculos | Regulação | Conectores índice | SLA payout |
| Bundles (de‑peg+slashing) | N/D | prêmio | **Book** | Bundle | Cobertura ampla | Fee | Tesouraria | Complexidade | Adoção | Catálogos | Playbooks |

---

## 15) Mercado Interbancário & Funding
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Interbancário overnight/termo | Muito alto | DI/SELIC | **—** | Leitura/repasse | Custos reais | Transparência | *TCA* | Complexidade | Acesso | Traz visibilidade | Relatórios |
| Repo/Reverse repos (tri‑party) | Muito alto | DI ± | **RFQ** | Integra preço/colateral | Caixa/colateral | Spread | Tesouraria | Colateral | Mesa | Roteamento | Regras e PoR |
| FX swaps/CCS p/ funding | Alto | — | **RFQ** | Hedge funding | Custo menor | Proteção | Cross‑border | Basis | ISDA | Router | *Best‑ex* |
| CP/ECP; CDs/CDBs/RDB; time deposits | Alto | DI ± | **RFQ/Book** | Orquestra captação | Velocidade | Mandatos | Bridge funding | Vencimentos | Regulação | Consolida ordens | SLAs |
| Covered/LIG; ABCP/warehouse | Alto | DI ± | **Book** | Estruturar saída | Custo | Estrutura | Funding | OC/IC | Rating | Dados | Waterfalls |
| Multilaterais (BNDES/CAF/KfW) | Relevante | **benchmark** | **RFQ/Book** | Integra linha | Taxa atrativa | Mandato | Infra/verde | Regras | *Eligibility* | Orquestra docs | Indicadores |
| Janelas do BC | — | — | — | Leitura eventos | Transparência | — | Raros | Acesso | Política | Telemetria | Relatórios |

---

## 16) Infraestrutura de Crédito (Core CE)
| Componente | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Originação & decisão (KYC/AML/antifraude/open finance/bureaus/feature store) | — | — | — | Dados→score→recomendação | Aprovação rápida | Risco calibrado | Aumentar conversão | Dados ruins | LGPD | Orquestra dados | Watchers de qualidade |
| Observabilidade & governança (OTel/audit/MRM/BCDR/hooks) | — | — | — | Eventos, SLOs, gates | Transparência | Controle | Auditoria | Cultura | Processo | *Audit trail* | *Gates* bloqueiam regressões |
| Gestão de garantias (registries/escrow/avaliação/seguros) | — | — | — | Registro→execução | Segurança | Proteção | Colateral | Cartórios | Jurídico | Verificabilidade | Automa eventos |
| Pós‑negócio (servicing/trustees/SPV/CSD) | — | — | — | Reconciliação | Claridade | Fluxo confiável | Relato investidores | D+ prazos | Integração | *Waterfall* sólido | SLAs e alarmes |
| Estruturas legais (SPV/SPE/fiduciários) | — | — | — | Segregação | Proteção | Governança | Multilinhas | Burocracia | Custos | Padronização | Kits e modelos |
| Rating/validação/auditoria | — | — | — | Ingestão/pareceres | Taxa menor | Confiança | ESG/impacto | Tempo | Dados | Playbook | API ratings |
| Data clean rooms | — | — | — | *Join* seguro | Privacidade | Modelos ricos | Bancos/dados | Complexidade | Custos | Camada comum | Pipelines |
| Proof‑of‑reserve/solvency | — | — | — | Provas | Confiança | Risco menor | Custódia | Adoção | Técnica | PoR contínua | *Quórum* oráculos |
| Verifiable Events/EIP‑712 | — | — | — | Assinaturas | Não repúdio | Confiança | On/off‑chain | Adoção | Integração | Padrão comum | SDKs |

---

## 17) Ativos Sintéticos (TradFi & Cripto)
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| TRS/CFD/equity swaps | N/D | — | **RFQ** | RFQ; marks | Hedge sintético | Eficiência | *Basis* | Liquidez | ISDA | Roteamento | Conciliação |
| P‑Notes/participations | N/D | — | **RFQ** | RFQ | Acesso | Simplicidade | Exposição | Regulatória | KYC | Execução neutra | Compliance |
| ETNs/Certificates | N/D | — | **Book** | Book | Exposição | Liquidez | PB/wealth | Emissor | Risco emissor | Comparador | NAV tracking |
| Tokens sintéticos | N/D | — | **Book** | Book | Acesso 24/7 | *Composability* | Tesouraria | Oráculos | Liquidez | Guardrails | Monitoração |
| Tokenized index baskets | N/D | — | **Book** | Book | Diversificação | Gestão | Índices on‑chain | Rebalance | Custódia | Regras claras | Eventos |
| Synthetic repo (TRS + cash) | N/D | — | **RFQ** | RFQ | Financiamento | Spread | Arbitragem | Liquidez | ISDA | *Best‑ex* | *Cash‑flow* vinculado |

---

## 18) Crowdlending / P2P lending
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| P2P consumo | N/D | 25–60% | **CDI + 6–14%** | Book/RFQ | Acesso | Diversificação | *Long tail* | Risco idiossincrático | Suitability | *Scoring* comum | Curvas por coorte |
| P2P SME | N/D | 20–40% | **CDI + 5–12%** | Book | Capital de giro | Yield melhor | SME base | Dados | Garantias | Tape único | Watchers covenants |
| Invoice marketplaces | N/D | 15–35% | **CDI + 4–10%** | Leilão | Liquidez | Tranche curta | Volumes | Registro | Qualidade | Single‑price | Cessão integrada |
| Real estate crowdfunding (dívida) | N/D | 12–20% | **IPCA + 3–6%** | Book | Taxa menor | Lastro | Imob PME | Cartório | Avaliação | LTV | Eventos |
| Estudantil/saúde/community | N/D | 15–30% | **CDI + 4–9%** | Book | Acesso | Missão | *Impact* | Renda | Medição | KPIs impacto | Ratchets |
| Microfinanças (grupo) | N/D | 30–70% | **CDI + 8–18%** | Book | Inclusão | Spread | ONGs | Custo unit. | Formalização | Automação | Dados alternativos |
| Revenue‑based/royalty | N/D | 18–35% | **Receita % 1–10%** | RFQ | Sem diluição | Upside | SaaS/retail | Auditoria | Vol receita | Conciliação | *Hooks* receita |
| Receivables crowdfunding | N/D | 15–35% | **CDI + 4–10%** | Leilão | Caixa rápido | Diversificação | Marketplaces | Qualidade | Registro | Verificabilidade | Lotes/eligibility |
| Impact/community lending | N/D | 12–25% | **DI + 2–6%** | Book | Custo menor | *Impact KPI* | Municípios/ONGs | Medição | Verificação | KPIs→taxa | Oráculos de KPI |

---

## 19) NFTs Financeiros
| Subtipo | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| NFTs de posição (LP/veNFT) | N/D | — | **Book** | Book; leitura de posições | Taxa menor | Colateral | *Real yield* | Liquidez | Oráculos | Haircuts | Watchers |
| NFT‑backed loans | N/D | — | **RFQ** | RFQ; avaliação | Liquidez | Proteção | *Creator economy* | Avaliação | Vol | Políticas | LTV/haircuts |
| NFT bonds/notes | N/D | — | **RFQ** | RFQ; cessão | Liquidez | *Cash‑flows* | Recebíveis | Aceitação | Registro | Verificabilidade | Eventos |
| NFT de título/lien | N/D | — | **RFQ** | RFQ; registro | Execução clara | Segurança | Imob/ativos | Cartório | Jurídico | Provas | SDK cartórios |
| NFTs de vesting | N/D | — | **Book** | Book; cronograma | Controle | Previsão | *Token deals* | UX | Custódia | Transparência | Schedules |
| Derivativos de NFT | N/D | — | **Book** | Book | Hedge | Prêmios | Nicho | Liquidez | Risco modelo | Guardrails | Comparadores |

---

## 20) Seguros & Garantias (TradFi)
| Cobertura | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Seguro crédito comercial | Bilhões (prêmio) | prêmio | **RFQ** | Apólice↔contrato | Proteção | Fee | Cadeia B2B | Coberturas | Sinistro | Telemetria | LGD watchers |
| Seguro garantia | ~R$ 5–6 bi (prêmio) | prêmio | **RFQ** | Apólice↔obra | Garantia | Fee | Infra | Renovação | Jurídico | Agenda *expiry* | Renova auto |
| Seguro prestamista/vida | Alto | prêmio | **Book** | *Attach rate* | Cobertura | Cross‑sell | Varejo crédito | *Attach* | SUSEP | Recomendações | Regras de *attach* |
| Mortgage/title insurance | N/D | prêmio | **RFQ** | Título | Segurança | Fee | Imob | Cartório | Jurídico | Checklists | Eventos de registro |
| Risco político | N/D | prêmio | **RFQ** | Cobertura | Proteção | Fee | Comex/infra | Medição | País | Matriz país | Gatilhos |
| ECA cover | N/D | prêmio | **RFQ** | Cobertura ECA | Custo baixo | Proteção | Export | Lineas | Critérios | *Eligibility* | Runbooks |
| Monoline/Bond insurance | N/D | prêmio | **RFQ** | *Wrap* | Taxa menor | Spread menor | Emissões | Rating | Oferta | Integra rating | Eventos |
| ILS — Cat bonds/ILW | N/D | yield cat | **Book** | Dados risco | Hedge cat | Yield | Infra/seguro | Modelagem | Regulação | Transparência | Oráculos eventos |

---

## 21) Infra de Garantias Colateralizadas
| Componente | Volume BR anual | % Juros convencional | % Juros sugerida CE | Fluxo CE | Vantagem parte A | Vantagem parte B | Oportunidades | Desafios | Impedimentos | Por que o CE pode fazer melhor? | Como o CE pode fazer melhor? |
|---|---:|---|---|---|---|---|---|---|---|---|---|
| Registries/cartórios | — | — | — | Registro/execução | Segurança | Padronização | Eficiência | Burocracia | Custos | Automação | Connectors |
| Tri‑party collateral mgmt | — | — | — | *Alloc/substitute* | Taxa menor | Menor risco | Multi‑colateral | Integração | Regras | OMS | Simulador |
| CCPs/clearing/margem | — | — | — | Requisitos | Segurança | Confiança | Derivativos | Dados | Acesso | Ingest | Alertas |
| Rehypothecation/transformação | — | — | — | *Switch* | Liquidez | Yield | Funding | Risco | Política | Guardrails | PoR |
| Otimização de colateral (engine) | — | — | — | Algoritmos | Eficiência | Menor custo | Tesouraria | Dados | Complexidade | Solver | Haircuts |
| Vaults on‑chain multi‑colateral | — | — | — | Segregação | Provas | Segurança | RWAs | Adoção | Tech | SDK/PoR | Watchers |
| Oráculos (preço/PoR) | — | — | — | Feeds | Transparência | Redundância | Todos | Ataques | Latência | Quórum | Fallbacks |
| Seguro de colateral | — | prêmio | **RFQ** | Apólice | Proteção | Retorno | Pools | Aceitação | SUSEP | Integração | Gatilhos |
| Cross‑margin engine | — | — | — | Cálculo | Menor margem | Eficiência | Multi‑ativo | Modelos | Correl. | Framework | Backtests |
| Oráculos de recovery/TTR | — | — | — | Feeds | LGD melhor | Pricing | NPL/AR | Dados | Tempos | DCR + ETLs | Gatilhos |

---

> **Observação final**: onde consta **N/D**, recomendamos parametrizar **proxies** (ex.: **BCB concessões/estoque**, **ANBIMA emissões**, **SUSEP prêmios**, **RFB/Chain analytics** para cripto) e preencher via ETL mensal.

