# CreditEngine — v11 Tabela de Mercado + Scores (v9 Canônica)

> **Canônica**: este v11 cobre **100%** das linhas do **v9 — Master Catalog** (e do v10), com **novas colunas** pedidas.  
> **Revisão**: checagem quíntupla (escopo, duplicatas, consistência de família, rubricas de score, ranges de Cut CE, coerência risco×complexidade).  
> **Data/versão**: 2025‑09‑09 (America/Bahia)

### Novas colunas (definições)
- **Diferencial CE**: proposta única (best‑execution neutra, eventos verificáveis, watchers/hooks, neutralidade de fluxo, integrações).  
- **Complexidade Desenvolvimento (0‑10)**: esforço técnico (integrações, modelos, orquestração, tempo).  
- **Complexidade Legal (0‑10)**: licenças, estruturas, obrigações regulatórias/jurídicas.  
- **Risco médio**: **Baixo / Médio / Alto** (crédito+mercado+operacional+regulatório).  
- **Cut CE %**: *take‑rate* típico do CE (faixa **% do notional/PL ou a.a.**) ou nota **“— (SaaS)”** quando for assinatura/serviço fixo.  
- **Viabilidade (0‑10)**: prontidão de go‑live no modelo de **intermediação 100%** (curto prazo).  
> **Notas**: “bps not.” = % sobre notional (0,05% = 5 bps). Onde há *servicing*, range anual típico; onde roteamento puro, bps de notional. Para valores firmes, usar RFQ/contrato.

---

## 1) Modalidades de Crédito — PF (mesma turma do v10)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Empréstimo pessoal (não consignado) | Best‑ex + open finance + antifraude orquestrado | 5 | 6 | Alto | 0,6–1,2% a.a. | 8 |
| Consignado (INSS/público/privado) | Averbação integrada + leilão por faixa | 5 | 7 | Médio | 0,4–0,8% a.a. | 9 |
| Cartão — parcelado (sem emissão) | Leilão por arranjo + tape de recebíveis | 6 | 6 | Médio | 0,4–0,9% a.a. | 8 |
| Overdraft/cheque especial | Limite dinâmico com watchers | 6 | 6 | Alto | 0,5–1,0% a.a. | 7 |
| BNPL varejo | Lotes single‑price + antifraude | 6 | 6 | Médio | 0,5–1,0% a.a. | 8 |
| Veículos (CDC) | LTV/gravame/seguro em esteira única | 6 | 6 | Médio | 0,5–1,0% a.a. | 8 |
| Imobiliário/home equity | Avaliação + registros + eventos | 7 | 7 | Médio | 0,4–0,9% a.a. | 8 |
| Estudantil/saúde | Liquidação a prestadores + KPIs setoriais | 5 | 5 | Médio | 0,5–1,0% a.a. | 7 |
| Microcrédito PF | Dados alternativos + cobrança leve | 6 | 5 | Alto | 0,6–1,2% a.a. | 7 |
| Leasing / rent‑to‑own | Telemetria do ativo + posse programável | 6 | 6 | Médio | 0,5–1,0% a.a. | 7 |
| Salary advance/13º | RFQ via folha + reconciliação eventos | 5 | 6 | Baixo | 0,4–0,8% a.a. | 9 |
| SBL — contra investimentos | Oráculos de preço + margin engine | 6 | 7 | Médio | 0,3–0,7% a.a. | 8 |
| Margin lending | Integração brokers + watchers de margem | 5 | 7 | Médio | 0,2–0,5% a.a. | 8 |
| HEA/Shared Appreciation | Eventos verificáveis (venda/refi) | 6 | 7 | Médio | 0,5–1,0% a.a. | 6 |
| Embedded credit PF | Intent→RFQ + PSPs | 5 | 6 | Médio | 0,4–0,9% a.a. | 8 |

---

## 2) Modalidades de Crédito — PJ/SME/Corporate
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Capital de giro/limites | Book/Best‑ex + covenants como código | 6 | 6 | Médio | 0,5–1,0% a.a. | 9 |
| Antecipação de recebíveis | Leilão single‑price + cessão/registradoras | 6 | 6 | Médio | 0,6–1,2% a.a. | 9 |
| Desconto de duplicatas/invoice | Verificação de título + waterfall | 6 | 6 | Médio | 0,5–1,0% a.a. | 9 |
| Vendor/Confirming (SCF) | Curva âncora + pro‑rata por data | 6 | 6 | Baixo | 0,4–0,9% a.a. | 9 |
| Linhas rotativas (RCF) | Automação de *draws* + agência digital | 6 | 6 | Médio | 0,4–0,9% a.a. | 8 |
| Term Loan | Term sheet padronizado + RFQ neutro | 6 | 6 | Médio | 0,4–0,9% a.a. | 8 |
| Unitranche/Direct lending | Data room unificado + disputa por covenants | 7 | 7 | Médio | 0,5–1,1% a.a. | 7 |
| Mezanino (PIK/warrants) | Estruturas *template* + gatilhos PIK | 7 | 7 | Alto | 0,6–1,3% a.a. | 6 |
| Bridge loans | *Fast lane* + take‑out mapeado | 5 | 6 | Médio | 0,5–1,0% a.a. | 8 |
| Project finance | DSCR/OC/IC em watchers + seguros | 8 | 8 | Médio | 0,5–1,0% a.a. | 7 |
| Asset‑based lending (ABL) | Borrowing‑base + certificados digitais | 7 | 7 | Médio | 0,5–1,0% a.a. | 8 |
| Warehouse lines (originadores) | Elegibility + testes de pool automatizados | 7 | 7 | Médio | 0,4–0,8% a.a. | 8 |
| Forfaiting | Precificação país/sacado + *settlement* | 6 | 7 | Médio | 0,3–0,7% a.a. | 7 |
| Floorplan/Inventory | Telemetria e *curtailments* | 6 | 6 | Médio | 0,5–1,0% a.a. | 8 |
| Borrowing‑base commodities | Oráculos de qualidade/estoque | 7 | 7 | Médio | 0,5–1,0% a.a. | 7 |
| Litigation finance | Milestones e comitês programáticos | 7 | 7 | Alto | 0,8–1,5% a.a. | 6 |
| IP‑backed | Escrow/licenças conectadas | 7 | 7 | Alto | 0,7–1,3% a.a. | 6 |
| Fund finance (Capital call/NAV) | Leitura de LPAs + covenants LP | 6 | 7 | Médio | 0,3–0,7% a.a. | 8 |
| B2B BNPL / dynamic discounting | Leilão por datas + reconciliação | 6 | 6 | Baixo | 0,4–0,9% a.a. | 9 |

---

## 3) Trade Finance
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Carta de Crédito (LC) | Motor documental + RFQ multi‑banco | 6 | 7 | Médio | 0,2–0,5% not. | 8 |
| Standby LC (SBLC) | Watchers de *expiry* + renovações | 6 | 7 | Médio | 0,2–0,5% not. | 8 |
| Aval/Fiança | Políticas objetivas + agenda de eventos | 6 | 7 | Médio | 0,2–0,5% not. | 8 |
| Cobrança documentária (D/P; D/A) | Checklists e OCR | 5 | 6 | Baixo | 0,1–0,3% not. | 8 |
| ACC/ACE; FINIMP | Router FX + best‑ex multi‑dealer | 6 | 7 | Médio | 0,2–0,4% not. | 8 |
| Warehouse receipts finance | Oráculos de qualidade + inspeções | 7 | 7 | Médio | 0,5–1,0% a.a. | 7 |
| Tolling/off‑taker backed | Validação *off‑take* + covenants | 7 | 7 | Médio | 0,4–0,9% a.a. | 7 |

---

## 4) Mercado de Capitais — Dívida (Primário/SEC)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Debêntures (incl. incentivadas) | Book/API + monitor de covenants/ESG | 7 | 8 | Médio | 0,1–0,3% not. | 8 |
| Bonds corporativos | Integra janelas + FX/ratings | 7 | 8 | Médio | 0,1–0,3% not. | 7 |
| CP/NP | RFQ multi‑dealer + *fast close* | 6 | 7 | Médio | 0,1–0,3% not. | 8 |
| MTN/Reg S/144A | Calendário global + *disclosure* | 7 | 8 | Médio | 0,1–0,3% not. | 7 |
| CRI/CRA | Tape/lastro + waterfall eventos | 7 | 8 | Médio | 0,2–0,6% not. | 8 |
| FIDC (quotas) | Testes OC/IC + servicing | 7 | 8 | Médio | 0,3–0,8% a.a. | 8 |
| Covered/LIG | NAV/OC/IC com alerts | 7 | 8 | Baixo | 0,1–0,3% not. | 7 |
| Perpétuos/AT1/CoCos | Eventos de capital + alerts | 7 | 9 | Alto | 0,1–0,3% not. | 6 |
| Municipal/Project bonds | DSCR watchers + dados projeto | 7 | 8 | Médio | 0,1–0,3% not. | 7 |
| Schuldschein | RFQ *club* padronizado | 6 | 7 | Médio | 0,1–0,2% not. | 7 |
| Social/Impact bonds | Oráculos de KPI de impacto | 7 | 8 | Médio | 0,1–0,3% not. | 7 |
| SLL/SLB (ratchets) | KPIs→taxa automatizados | 7 | 8 | Médio | 0,1–0,3% not. | 8 |

---

## 5) Securitização & Estruturados
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| ABS/RMBS/CMBS | Tape/tests + pós‑negócio | 8 | 8 | Médio | 0,3–0,8% a.a. | 8 |
| CLO/CDO | Telemetria de loan + IC/OC | 8 | 8 | Médio | 0,3–0,8% a.a. | 7 |
| Marketplace lending ABS | Normalização multi‑orig. | 8 | 8 | Médio | 0,3–0,8% a.a. | 8 |
| NPL securitization | *Workout* integrado + recovery | 8 | 8 | Alto | 0,5–1,2% a.a. | 6 |
| Whole business securitization | KPIs operacionais→taxa | 8 | 8 | Médio | 0,3–0,8% a.a. | 7 |
| Re‑REMIC | Re‑tranching com controles | 8 | 9 | Médio | 0,2–0,6% not. | 6 |
| CLN (Credit‑Linked Notes) | Eventos de crédito conectados | 7 | 8 | Médio | 0,1–0,3% not. | 7 |
| COE/Notas estruturadas | Roteamento neutro + KIDs | 6 | 8 | Médio | 0,1–0,2% not. | 7 |
| Structured deposits | Comparador best‑ex | 5 | 7 | Baixo | 0,05–0,15% not. | 8 |
| Certificates/Participation | NAV eventos + *what‑ifs* | 6 | 7 | Médio | 0,1–0,2% not. | 7 |

---

## 6) Money Market & Depósitos (Funding)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| CDB/RDB/LC/LCI/LCA | Comparador + roteamento | 5 | 6 | Baixo | 0,05–0,15% not. | 9 |
| CDs/Time deposits | Multi‑moeda + FX router | 6 | 7 | Médio | 0,05–0,15% not. | 8 |
| CP/ECP | RFQ multi‑dealer | 6 | 7 | Médio | 0,1–0,2% not. | 8 |
| Repos/Reverse repos | Preço×colateral *engine* | 6 | 7 | Baixo | 0,02–0,08% not. | 8 |
| Securities lending/borrowing | Locates integrados | 6 | 7 | Médio | 0,02–0,10% not. | 8 |
| Collateral upgrade | Switch algorítmico | 6 | 7 | Médio | 0,03–0,10% not. | 7 |
| Tri‑party dynamic allocation | OMS + simulação | 7 | 7 | Baixo | — (SaaS) | 8 |

---

## 7) Derivativos de Crédito (via dealers)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| CDS single‑name | RFQ neutro + eventos | 6 | 9 | Alto | 0,03–0,10% not. | 6 |
| CDS índice (CDX/iTraxx) | *Rolls* e *marks* automatizados | 6 | 9 | Alto | 0,03–0,08% not. | 6 |
| Tranches/Nth‑to‑default | Triggers programáveis | 7 | 9 | Alto | 0,03–0,10% not. | 5 |
| LCDS / TRS loans/bonds | Cash‑flows vinculados | 6 | 9 | Alto | 0,03–0,08% not. | 6 |
| Opções crédito/Swaptions CDS | Watchers de barreira | 7 | 9 | Alto | 0,03–0,08% not. | 5 |
| Credit spread options (CSO) | Curvas integradas | 6 | 9 | Alto | 0,03–0,08% not. | 5 |
| Options on TRS (OTRS) | Greeks conectados | 7 | 9 | Alto | 0,03–0,08% not. | 5 |
| Quanto/FX‑linked CDS | Workflow FX+crédito | 7 | 9 | Alto | 0,03–0,10% not. | 5 |

---

## 8) Derivativos de Juros e FX (hedge)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Swaps de juros (DI/fixo‑flutuante) | RFQ multi‑dealer + TCA | 6 | 8 | Médio | 0,02–0,06% not. | 8 |
| Cross‑currency swaps (CCS) | Router + *basis* watchers | 6 | 8 | Médio | 0,03–0,08% not. | 7 |
| FX Forwards/Swaps | RFQ + *best‑ex* FX | 5 | 7 | Baixo | 0,01–0,04% not. | 9 |
| Futuros (DI/Treasuries/FX) | OMS + execução neutra | 6 | 8 | Médio | — (SaaS) | 8 |
| Opções (IR/FX) | Simulador + barreiras | 6 | 8 | Médio | 0,02–0,06% not. | 7 |

---

## 9) Lending & Borrowing (Web3)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Pools sobrecolateralizados | Provas/PoR + haircuts dinâmicos | 6 | 8 | Médio | 0,2–0,6% a.a. | 7 |
| Pools permissionados | Policies→constraints + KYC | 6 | 8 | Médio | 0,3–0,7% a.a. | 7 |
| LRT/LP/NFT colateral | Invariantes on‑chain | 7 | 9 | Alto | 0,3–0,8% a.a. | 6 |
| RWA tokenizados | Eventos verificáveis + waterfall | 7 | 9 | Médio | 0,3–0,8% a.a. | 7 |
| Intent‑based RFQ/auction | Execução por *solvers* | 7 | 8 | Médio | 0,05–0,15% not. | 6 |

---

## 10) Derivativos cripto/tokenizados
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Perpétuos | TCA multi‑venue + hedge | 6 | 8 | Alto | 0,02–0,06% not. | 7 |
| Futuros datados | OMS + *calendar/roll* | 6 | 8 | Médio | — (SaaS) | 7 |
| Opções | Simulação de greeks | 6 | 8 | Alto | 0,02–0,06% not. | 6 |
| Funding‑rate swaps | Casamento de *cash‑flows* | 7 | 9 | Alto | 0,02–0,05% not. | 5 |
| TRS/CFDs tokenizados | Conciliação de *marks* | 7 | 9 | Alto | 0,02–0,05% not. | 5 |
| Vol tokens/power perps/barriers | Guardrails de vol | 7 | 9 | Alto | 0,02–0,06% not. | 5 |

---

## 11) Tokenização de Dívida/Recebíveis (RWA)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| T‑bills/bonds tokenizados | NAV/PoR + eventos cupom | 6 | 8 | Baixo | 0,1–0,3% not. | 7 |
| Invoices/recebíveis tokenizados | Cessão + oráculos de pagamento | 7 | 9 | Médio | 0,3–0,8% a.a. | 7 |
| FIDC quotas tokenizadas | Espelhamento de tranches | 7 | 9 | Médio | 0,3–0,8% a.a. | 6 |
| NPL tokens | Esteiras *workout* | 7 | 9 | Alto | 0,5–1,2% a.a. | 5 |
| Home equity tokens | LTV + eventos de venda | 7 | 9 | Médio | 0,3–0,7% a.a. | 6 |

---

## 12) Stablecoins & Colateral Digital
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Fiat‑backed (USDC/USDT) | Provas de reserva + limites | 5 | 8 | Médio | 0,02–0,08% not. | 8 |
| Cripto‑colateralizadas (DAI/LUSD) | Quórum de oráculos | 6 | 8 | Médio | 0,02–0,06% not. | 7 |
| Algorítmicas híbridas | Guardrails + allowlist | 6 | 9 | Alto | 0,02–0,06% not. | 5 |
| Commodity‑backed | PoR custódia | 6 | 8 | Médio | 0,02–0,06% not. | 6 |
| RWA‑backed (T‑bill) | NAV/PoR contínuos | 6 | 8 | Baixo | 0,02–0,06% not. | 7 |
| Yield‑bearing stables | Limites por emissor | 6 | 9 | Médio | 0,02–0,06% not. | 6 |
| CBDC (rail) | Integração modular | 5 | 9 | Baixo | — (SaaS) | 5 |

---

## 13) Produtos Estruturados DeFi
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Covered‑call/put vaults | Guardrails + monitor greeks | 6 | 8 | Alto | 0,02–0,06% not. | 6 |
| Principal‑protected on‑chain | Payoff comparado (RWA+opção) | 7 | 9 | Médio | 0,02–0,06% not. | 6 |
| Delta‑neutral basis | TCA + basis watchers | 6 | 8 | Médio | 0,02–0,05% not. | 6 |
| Tranching real yield (RWA/LP) | Waterfall on‑chain | 7 | 9 | Médio | 0,3–0,8% a.a. | 6 |
| Dual currency on‑chain | Oráculos FX + RFQ | 7 | 9 | Alto | 0,02–0,06% not. | 5 |

---

## 14) Seguros Descentralizados (DeFi)
| Cobertura | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Smart contract/oracle/CEX | Gatilhos LGD conectados | 6 | 8 | Médio | 0,02–0,06% not. | 6 |
| Custodial/slashing | Watchers de slashing | 6 | 8 | Médio | 0,02–0,06% not. | 6 |
| De‑peg stablecoins | Oráculos de peg | 6 | 8 | Médio | 0,02–0,06% not. | 6 |
| Paramétrico climático/índice | Conectores de índice | 6 | 9 | Médio | 0,02–0,06% not. | 5 |
| Bundles (de‑peg+slashing) | Catálogos e playbooks | 6 | 9 | Médio | 0,02–0,06% not. | 5 |

---

## 15) Mercado Interbancário & Funding
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Interbancário overnight/termo | TCA e transparência | 5 | 7 | Baixo | — (SaaS) | 8 |
| Repo/Reverse repo (tri‑party) | Regras de alocação | 6 | 7 | Baixo | 0,02–0,06% not. | 8 |
| FX swaps/CCS p/ funding | Best‑ex + router | 6 | 8 | Médio | 0,02–0,06% not. | 7 |
| CP/ECP; CDs/CDBs/RDB; time deposits | Consolidador neutro | 6 | 7 | Médio | 0,05–0,15% not. | 8 |
| Covered/LIG; ABCP/warehouse | Waterfalls + rating | 7 | 8 | Médio | 0,1–0,3% not. | 7 |
| Multilaterais (BNDES/CAF/KfW) | Indicadores e *eligibility* | 7 | 8 | Médio | 0,05–0,15% not. | 7 |
| Janelas do BC | Telemetria de eventos | 5 | 8 | Baixo | — (SaaS) | 6 |

---

## 16) Infraestrutura de Crédito (Core CE)
| Componente | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Originação & decisão | Feature store + recomendação | 7 | 6 | Médio | — (SaaS) | 9 |
| Observabilidade & governança | Eventos EIP‑712 + SLOs | 7 | 5 | Baixo | — (SaaS) | 9 |
| Gestão de garantias | Registro/execução unificado | 7 | 7 | Médio | — (SaaS) | 8 |
| Pós‑negócio/servicing/SPV | Waterfall e reconciliação | 7 | 7 | Médio | 0,3–1,0% a.a. | 8 |
| Estruturas legais (SPV/SPE/fid.) | Kits e modelos | 6 | 8 | Médio | — (SaaS) | 7 |
| Rating/validação/auditoria | API ratings/pareceres | 6 | 7 | Baixo | — (SaaS) | 8 |
| Data clean rooms | *Join* seguro multi‑parte | 7 | 6 | Médio | — (SaaS) | 8 |
| Proof‑of‑reserve/solvency | PoR contínua | 7 | 7 | Médio | — (SaaS) | 7 |
| Verifiable Events/EIP‑712 | Assinaturas canônicas | 7 | 6 | Baixo | — (SaaS) | 9 |

---

## 17) Ativos Sintéticos (TradFi & Cripto)
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| TRS/CFD/equity swaps | *Marks* integrados | 6 | 8 | Médio | 0,02–0,06% not. | 7 |
| P‑Notes/participations | Compliance/adequação | 5 | 8 | Médio | 0,02–0,05% not. | 7 |
| ETNs/Certificates | Comparador NAV | 5 | 8 | Médio | 0,02–0,05% not. | 7 |
| Tokens sintéticos | Guardrails/óraculos | 6 | 9 | Alto | 0,02–0,05% not. | 6 |
| Tokenized index baskets | Rebalance programável | 6 | 9 | Alto | 0,02–0,05% not. | 6 |
| Synthetic repo (TRS + cash) | *Cash‑flows* vinculados | 6 | 8 | Médio | 0,02–0,05% not. | 7 |

---

## 18) Crowdlending / P2P lending
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| P2P consumo | *Scoring* comum + suitability | 6 | 7 | Médio | 0,5–1,0% a.a. | 8 |
| P2P SME | Tape único + watchers | 6 | 7 | Médio | 0,5–1,0% a.a. | 8 |
| Invoice marketplaces | Leilão single‑price | 6 | 7 | Médio | 0,5–1,0% a.a. | 9 |
| Real estate crowdfunding (dívida) | LTV/registro integrados | 6 | 7 | Médio | 0,4–0,9% a.a. | 8 |
| Estudantil/saúde/community | KPIs de impacto | 6 | 7 | Médio | 0,4–0,9% a.a. | 7 |
| Microfinanças (grupo) | Automação de campo | 6 | 6 | Alto | 0,6–1,2% a.a. | 7 |
| Revenue‑based/royalty | *Hooks* de receita | 6 | 7 | Médio | 0,5–1,0% a.a. | 7 |
| Receivables crowdfunding | Elegibility + cessão | 6 | 7 | Médio | 0,5–1,0% a.a. | 9 |
| Impact/community lending | Oráculos de KPI | 6 | 7 | Médio | 0,4–0,9% a.a. | 7 |

---

## 19) NFTs Financeiros
| Subtipo | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| NFTs de posição (LP/veNFT) | Leitura de posições + haircuts | 6 | 8 | Médio | 0,3–0,8% a.a. | 6 |
| NFT‑backed loans | Avaliação/verificabilidade | 6 | 9 | Alto | 0,4–0,9% a.a. | 5 |
| NFT bonds/notes | Cessão via NFT + eventos | 6 | 9 | Médio | 0,3–0,7% a.a. | 6 |
| NFT de título/lien | Registro/ônus programável | 7 | 9 | Médio | 0,3–0,7% a.a. | 6 |
| NFTs de vesting | Transparência de *schedules* | 6 | 8 | Médio | — (SaaS) | 7 |
| Derivativos de NFT | Comparadores + guardrails | 7 | 9 | Alto | 0,02–0,06% not. | 5 |

---

## 20) Seguros & Garantias (TradFi)
| Cobertura | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Seguro crédito comercial | Telemetria LGD | 6 | 8 | Médio | 0,1–0,3% not. | 8 |
| Seguro garantia | Agenda de *expiry* | 6 | 8 | Médio | 0,1–0,3% not. | 8 |
| Seguro prestamista/vida | Regras de *attach* | 6 | 8 | Baixo | 0,1–0,3% not. | 9 |
| Mortgage/title insurance | Checklists cartoriais | 6 | 8 | Baixo | 0,1–0,3% not. | 8 |
| Risco político | Matriz país/eventos | 6 | 9 | Médio | 0,1–0,3% not. | 6 |
| ECA cover | Conexão linhas ECA | 6 | 8 | Médio | 0,1–0,3% not. | 7 |
| Monoline/Bond insurance | Integra rating/wrap | 6 | 9 | Médio | 0,1–0,3% not. | 6 |
| ILS — Cat bonds/ILW | Oráculos de evento cat | 7 | 9 | Médio | 0,1–0,3% not. | 6 |

---

## 21) Infra de Garantias Colateralizadas
| Componente | Diferencial CE | Dev 0‑10 | Legal 0‑10 | Risco médio | Cut CE % | Viabilidade 0‑10 |
|---|---|---:|---:|---|---|---:|
| Registries/cartórios | Connectors multi‑registro | 7 | 7 | Médio | — (SaaS) | 8 |
| Tri‑party collateral mgmt | Alloc/substitute orquestrado | 7 | 7 | Baixo | — (SaaS) | 8 |
| CCPs/clearing/margem | Ingest de regras/margens | 6 | 8 | Baixo | — (SaaS) | 8 |
| Rehypothecation/transformação | Guardrails + PoR | 7 | 8 | Médio | 0,02–0,06% not. | 7 |
| Otimização de colateral (engine) | Solver de haircuts/limites | 8 | 7 | Baixo | — (SaaS) | 8 |
| Vaults on‑chain multi‑colateral | Segregação + provas | 7 | 8 | Médio | — (SaaS) | 7 |
| Oráculos (preço/PoR) | Quórum/fallbacks | 7 | 7 | Médio | — (SaaS) | 9 |
| Seguro de colateral | Gatilhos de apólice | 6 | 8 | Baixo | 0,1–0,3% not. | 7 |
| Cross‑margin engine | Cálculo correlacional | 8 | 7 | Médio | — (SaaS) | 7 |
| Oráculos de recovery/TTR | Feeds LGD/tempo | 7 | 7 | Médio | — (SaaS) | 8 |

---

### Observações finais
- Estes *scores* servem para **priorização** e **planejamento** (produto/engenharia/compliance).  
- Para **valores firmes** (Cut CE, preços, SLOs), usar **RFQs e contratos** nos módulos P1..P7.  
- Onde algum item exija *fee* fixo em vez de %, marcamos **“— (SaaS)”**.  
- Mantida a **indexação canônica ao v9**; qualquer ajuste de escopo deve ocorrer no v9 e ser propagado.

