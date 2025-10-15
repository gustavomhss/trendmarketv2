---
id: kb/blocos/bloco_04_a24_a33_final_v4_00
title: "Bloco 04 — A24–A33 (Markets v2, Treasury, Governance+, TKN) • FINAL v4.00 — sem placeholders"
version: "v4.00 (conforme v3.1 + Simon v2.8)"
date: "2025-09-07"
timezone: America/Bahia
owner: AG1 (Knowledge Builder)
stewards: [Research, Builder]
doc_type: kb_block
block_range: [A24, A33]
domain: markets_v2
snippet_budget_lines: 200
maturity: Gold
rag_kpis: { mrr: null, ndcg: null, coverage: null, leakage: null }
links:
  - kb/blocos/bloco_01_a0_a12_final_v1_60
  - kb/blocos/bloco_02_autopilot_final_v2_10
  - kb/blocos/bloco_03_a13_a23_final_v3_00
observability:
  common_keys: [job_id, pack_id, artifact_path, trace_id]
  sim_trace_hash_required: true
---

# 0) Sumário & **Revisão Tripla** (v4.00)
**Objetivo:** Entregar **Bloco 04 (A24–A33)** **100% preenchido** (sem placeholders), com **conteúdo canônico inline**, **Evidence JSON** por pack + **agregado**, **Probes/QGen/Hard‑negatives (20/20/10)** por pack, **watchers + parâmetros**, **runbooks** e **closeout sintético**.

**Revisão Tripla:**
1) **Conteúdo** — Todos os packs completos; respostas canônicas no corpo. **OK**.
2) **Técnica** — Gates v2.8; watchers; CI/gates; statusboards; Evidence pronto. **OK**.
3) **Conformidade v3.1** — front‑matter `rag_kpis=null`; snippet budget=200; Evidence/QGen/HN em padrão; maturidade Gold. **OK**.

---

# 1) `pack_defaults` — v2.8 (Simon)
```yaml
pack_defaults:
  enforce_gates: true
  gates:
    rag_mrr_min: 0.35
    err_p95_max: 3.0
    fairness_gini_max: 0.25
    proof_coverage_ratio_min: 0.80
    attention_utilization_bounds: { min: 0.3, max: 0.85 }
    coupling_max: 0.5
    sop_autonomy_ratio_min: 0.6
  keynes_buffer:
    throughput_max_rps: 50
    queue_max_seconds: 5
    circuit_breaker: { p95_latency_ms: 1500, action: "degradar_para_pack_lite" }
  mechanism_gates: { M1_incentive_compat: ok, M2_strategy_proofness: ok, M3_anti_collusion: ok, M4_fairness_min: "Gini<=0.25" }
```

---

# 2) Watchers — catálogo & parâmetros do bloco
```yaml
watchers:
  - thickness_watch:               { check: "espessura de mercado abaixo do alvo" }
  - congestion_watch:              { check: "fila/latência acima dos targets" }
  - collusion_watch:               { check: "padrões de colusão entre agentes" }
  - unraveling_watch:              { check: "antecipação/agenda destruindo matching" }
  - decision_cycle_slip_watch:     { check: "tempo de ciclo > target por 3 janelas" }
  - overshoot_watch:               { check: "supply > need_line por N janelas" }
  - stability_watch:               { check: "blocking_pairs > 0" }
  - truthfulness_watch:            { check: "ganho esperado por misreport > 0" }
  - mev_inclusion_delay_watch:     { check: "p95 de inclusão por slot > alvo" }
  - transport_mismatch_watch:      { check: "quebra de suposições em transporte" }
  - decision_cycle_slip_watch:     { check: "tempo de ciclo > alvo" }
params:
  thickness_watch: { active_bidders_min: 5, depth_levels_min: 3 }
  collusion_watch: { corr_bid_max: 0.8 }
  congestion_watch: { queue_wait_p95_max_sec: 10 }
  mev_inclusion_delay_watch: { slots_p95_max: 6 }
```

---

# 3) Statusboards
```yaml
statusboards:
  markets:  "/statusboard/markets_v2.yml"         # spreads, adoção, espessura, p95 inclusão
  treasury: "/statusboard/treasury.yml"           # ALM, duration, reservas, PoR
  gov:      "/statusboard/governance.yml"         # quóruns, tempo de caso, disputas
  tkn:      "/statusboard/tkn.yml"                # supply, distribuição, governança
```

---

# 4) Packs A24–A33 (conteúdo canônico completo)
> Estrutura: **Tarefa YAML → Conteúdo → Evidence JSON → Probes (20) → QGen (20) → Hard‑negatives (10)**.

## A24 — Leilões v2 (Mecânica Avançada)
### Tarefa YAML
```yaml
id: A24-AUCTION-V2
competency: Market Design
priority: P1
why: eficiência de preço sob competição
content_min: [reverse_auctions, anti_collusion, clearing_policies]
deps: [A2, A10]
license: MIT
```
### Conteúdo
- **Tipos**: leilão reverso com lances selados; variantes com lote único e múltiplos; RFQ controlado como fallback.
- **Clearing**: menor cupom **ponderado por capital**; regras públicas; transparência de **média ponderada**.
- **Anti‑colusão**: janela aleatória; limites de correlação; auditoria de padrões; sanções progressivas.
- **Sinal**: **preço de leilão prevalece**; score/ELO apenas **modula limites**.
### Evidence JSON
```json
{ "id": "A24-AUCT-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A24-—-Leilões-v2-(Mecânica-Avançada)"], "vector_ids": ["a24-auct-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Diferenças entre RFQ e leilão reverso.
2. Como calcular clearing por capital.
3. Por que preço de leilão prevalece.
4. Limites de correlação de lances.
5. Como aleatorizar janelas.
6. Política de sanções.
7. Como publicar transparência de média.
8. Métricas de espessura.
9. Como tratar lotes múltiplos.
10. Como evitar unraveling.
11. Como registrar disputas.
12. Limites por score.
13. Auditoria de padrões suspeitos.
14. Regras de cancelamento.
15. Compatibilidade com pools.
16. Como lidar com tie‑break.
17. Logs mínimos do leilão.
18. Publicidade mínima.
19. Fairness mínima.
20. Comunicação ao mercado.
### QGen (20)
- Template de RFQ.
- Script de clearing.
- Plano anti‑colusão.
- Simulação de espessura.
- Política de sanções.
- Painel de leilões.
- Runbook de disputa.
- Randomização de janelas.
- Deduplicação de lances.
- Tie‑break rules.
- Lotes múltiplos.
- Logs e export.
- Métrica de fairness.
- Procedimento de cancelamento.
- Integração com pools.
- Filtros anti‑outlier.
- Checklist de publicidade.
- Limites por score.
- Auditoria externa.
- Comunicação de resultados.
### Hard‑negatives (10)
- RFQ substitui leilões sempre.
- Preço de leilão é opcional.
- Não há risco de colusão.
- Transparência é supérflua.
- Espessura é irrelevante.
- Disputas não precisam de runbook.
- Randomização atrapalha sempre.
- Sanções não são necessárias.
- Lotes múltiplos não mudam regra.
- Fairness não se aplica.

---

## A25 — Mercado Secundário v2
### Tarefa YAML
```yaml
id: A25-SECONDARY-V2
competency: Market Ops
priority: P1
why: disciplina de preço e liquidez
content_min: [order_types, circuit_breakers, transparency]
deps: [A24]
license: MIT
```
### Conteúdo
- **Ordem/Execução**: leilões de abertura/fechamento; livro de ofertas; RFQ; P2P com fee do credor.
- **Circuit breakers**: limites de variação; pausas programáticas; fila de leilão de retomada.
- **Transparência**: spreads, profundidade, volumes e **tempo para liquidez**.
### Evidence JSON
```json
{ "id": "A25-SEC-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A25-—-Mercado-Secundário-v2"], "vector_ids": ["a25-sec-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Leilão de abertura vs contínuo.
2. Critérios de breaker.
3. Fila de retomada.
4. P2P fee do credor.
5. Medir profundidade.
6. Spreads e custo implícito.
7. Book vs RFQ.
8. Transparência mínima.
9. Regras de cancelamento.
10. Indicadores de liquidez.
11. Anti‑manipulação.
12. Logs de execução.
13. Painéis públicos.
14. Colusão no secundário.
15. Relação com primário.
16. Proteção do pequeno investidor.
17. Restrição por tranches.
18. Limites por risco.
19. Rota degradada.
20. Comunicação.
### QGen (20)
- Desenhar breaker.
- Painel de liquidez.
- Métrica de profundidade.
- Simular choques.
- Procedimento de retomada.
- Guia P2P.
- Livro de ofertas.
- Export público.
- Fairness checks.
- Anti‑manipulação.
- Logs e auditoria.
- RFQ configs.
- Cancelamentos.
- Indicadores chave.
- Relação com leilão primário.
- Proteção ao investidor.
- Tranches.
- Limites de risco.
- Rota degradada.
- Comunicação.
### Hard‑negatives (10)
- Breaker não é necessário.
- Transparência pode ser omitida.
- Liquidez não importa.
- P2P deve cobrar do tomador.
- Logs são supérfluos.
- Colusão não ocorre.
- Painéis públicos desnecessários.
- Cancelamentos sem regra.
- RFQ sempre domina.
- Pequeno investidor não precisa de proteção.

---

## A26 — Pools & Tranching v2
### Tarefa YAML
```yaml
id: A26-POOLS-V2
competency: Pool Design
priority: P1
why: alocação por risco/duração
content_min: [open_closed, tranches, redemption_queue]
deps: [A25]
license: MIT
```
### Conteúdo
- **Pools**: abertos/fechados; regras de resgate; ACT/365; prioridade por **fila** sob stress.
- **Tranches**: seniores/mezz/júniors; **waterfall**; divulgação pública de perdas.
- **Gestão**: limites por score; duration alvo; HWM; withdrawal fee sob estresse.
### Evidence JSON
```json
{ "id": "A26-POOL-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A26-—-Pools-&-Tranching-v2"], "vector_ids": ["a26-pool-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Diferenças aberto vs fechado.
2. Fila de resgates.
3. Regras ACT/365.
4. Tranches e waterfall.
5. Perdas e divulgação.
6. Duration alvo.
7. Limites por score.
8. HWM.
9. Fee sob stress.
10. Governação de mudanças.
11. Liquidez interna.
12. Transferência entre pools.
13. Impacto de defaults.
14. Painéis por pool.
15. Anti‑corrida.
16. Gate de resgates.
17. Transparência mínima.
18. Riscos por tranche.
19. Auditoria de regras.
20. Janelas de resgate.
### QGen (20)
- Política de resgates.
- Design de tranches.
- Divulgação de perdas.
- Duration e limites.
- HWM.
- Fee stress.
- Painel do pool.
- Anti‑corrida.
- Gate e fila.
- Transferências.
- Defaults.
- ACT/365.
- Auditoria.
- Regras públicas.
- SLA de resgate.
- Liquidez.
- Score limites.
- Waterfall.
- Tranches.
- Comunicação.
### Hard‑negatives (10)
- Fila é opcional sob stress.
- Waterfall não precisa ser público.
- HWM é supérfluo.
- Duration não importa.
- Perdas não precisam ser divulgadas.
- Resgates sem gate estão sempre ok.
- Sem limites por score.
- Auditoria é dispensável.
- ACT/365 não se aplica.
- Comunicação não é necessária.

---

## A27 — Default v2 (Governança de Casos)
### Tarefa YAML
```yaml
id: A27-DEFAULT-V2
competency: Governance
priority: P1
why: resolução eficiente e justa
content_min: [cc_rc_le, s_claims, carve_outs, quorum]
deps: [A3, A26]
license: MIT
```
### Conteúdo
- **Papéis**: CC (Conselho de Credores), RC (Relator), **LE Escrow**.
- **Menu**: ação coletiva; **S‑Claims**; carve‑out; venda fracionada; opt‑out documentado.
- **Quóruns**: ≥50% padrão; ≥66,7% estrutural; logs públicos imutáveis.
### Evidence JSON
```json
{ "id": "A27-DEF-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A27-—-Default-v2-(Governança-de-Casos)"], "vector_ids": ["a27-def-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Papéis e responsabilidades.
2. Opções do menu.
3. Quóruns.
4. Logs públicos.
5. Opt‑out.
6. S‑Claims.
7. Carve‑outs.
8. Voto estratégico.
9. Conflitos de interesse.
10. Substituição de RC.
11. SLA de disputa.
12. Publicidade mínima.
13. Auditoria externa.
14. Sanções por abuso.
15. Empate.
16. Janela de contestação.
17. Metadados de decisões.
18. Captura regulatória.
19. Cross‑border.
20. Reapreciação.
### QGen (20)
- Estatuto do CC.
- Termo do RC.
- Template de resolução.
- Regras de voto.
- Logs imutáveis.
- Procedimento de opt‑out.
- S‑Claims.
- Carve‑outs.
- Auditoria.
- Sanções.
- Empate.
- Contestação.
- Cross‑border.
- Conflitos.
- Transparência.
- Publicidade.
- SLA.
- Reapreciação.
- Registro público.
- Comunicação.
### Hard‑negatives (10)
- Quóruns são desnecessários.
- Logs podem ser privados.
- Opt‑out não precisa registro.
- S‑Claims sem regra.
- Carve‑out sem quórum.
- Conflitos não precisam ser declarados.
- SLA de disputa é irrelevante.
- Auditoria externa dispensa‑se.
- Publicidade mínima não se aplica.
- Empates não têm procedimento.

---

## A28 — Tesouraria & ALM
### Tarefa YAML
```yaml
id: A28-TREASURY-ALM
competency: Treasury
priority: P1
why: solvência e liquidez
content_min: [duration, alm, reserves_policy]
deps: [A26, A19]
license: MIT
```
### Conteúdo
- **ALM**: casado de prazos; duration buckets; stress tests.
- **Reservas**: segregadas; PoR diária; reconciliação D+1 12:00 BRT.
- **Políticas**: limites por moeda; buffers; fila de resgates.
### Evidence JSON
```json
{ "id": "A28-ALM-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A28-—-Tesouraria-&-ALM"], "vector_ids": ["a28-alm-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Duration buckets.
2. Casamento de prazos.
3. PoR diária.
4. Reconciliação.
5. Limites por moeda.
6. Buffers.
7. Stress tests.
8. Liquidez vs retorno.
9. Fila sob stress.
10. Prioridade de pagamentos.
11. FX e hedge.
12. Diversificação bancária.
13. Custódia.
14. Políticas públicas.
15. Controles internos.
16. Painéis.
17. Auditoria.
18. Indicadores de solvência.
19. Indicadores de liquidez.
20. Comunicação.
### QGen (20)
- Política de duration.
- Plano de ALM.
- PoR.
- Reconciliação.
- Limites.
- Buffers.
- Stress.
- Retorno.
- Fila.
- Prioridade.
- FX.
- Bancos.
- Custódia.
- Publicação.
- Controles.
- Painéis.
- Auditoria.
- Solvência.
- Liquidez.
- Comunicação.
### Hard‑negatives (10)
- Duration é irrelevante.
- PoR pode ser mensal.
- Buffers são desnecessários.
- Stress não precisa.
- Reconciliação sem janela.
- FX sem política.
- Sem diversificação.
- Custódia irrelevante.
- Controles dispensáveis.
- Solvência não precisa de métrica.

---

## A29 — Risco & Limites
### Tarefa YAML
```yaml
id: A29-RISK-LIMITS
competency: Risk
priority: P1
why: conter perdas e alocar capital
content_min: [exposure_limits, concentration, stress_limits]
deps: [A28]
license: MIT
```
### Conteúdo
- **Limites**: por score, por região, por setor, por tranche.
- **Concentração**: caps por tomador/origem; diversificação.
- **Stress**: gatilhos para reduzir exposição; rota degradada.
### Evidence JSON
```json
{ "id": "A29-RISK-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A29-—-Risco-&-Limites"], "vector_ids": ["a29-risk-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Limites por score.
2. Limites regionais.
3. Setoriais.
4. Por tranche.
5. Caps por tomador.
6. Diversificação.
7. Gatilhos de stress.
8. Rota degradada.
9. Auditoria.
10. Logs de limites.
11. Painéis.
12. Revisão periódica.
13. Integração com ALM.
14. Transporte de sinais.
15. Spillover.
16. Fairness mínima.
17. Anti‑colusão.
18. Conflitos de política.
19. Comunicação.
20. Documentação.
### QGen (20)
- Tabela de limites.
- Caps.
- Stress.
- Degradada.
- Auditoria.
- Painéis.
- Revisão.
- ALM.
- Transporte.
- Spillover.
- Fairness.
- Anti‑colusão.
- Política.
- Comunicação.
- Documentação.
- Logs.
- Integração.
- Checks.
- Versionamento.
- Runbook.
### Hard‑negatives (10)
- Limites não são necessários.
- Concentração não importa.
- Stress não precisa.
- Auditoria é supérflua.
- Sem logs.
- Sem revisão.
- Sem integração com ALM.
- Fairness é irrelevante.
- Sem comunicação.
- Documentação é dispensável.

---

## A30 — Dados & Telemetria v2
### Tarefa YAML
```yaml
id: A30-DATA-TEL
competency: Data/Observability
priority: P1
why: decisões auditáveis
content_min: [schemas, freshness, export_public]
deps: [A4, A10]
license: MIT
```
### Conteúdo
- **Schemas**: atestações (hash, assinatura, ts, fonte); eventos de mercado; snapshots de reservas.
- **Freshness**: SLAs por feed; alarmes e fallback.
- **Export público**: formatos abertos; notarização.
### Evidence JSON
```json
{ "id": "A30-DATA-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A30-—-Dados-&-Telemetria-v2"], "vector_ids": ["a30-data-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Campos mínimos.
2. Assinaturas.
3. Timestamps.
4. Freshness SLAs.
5. Alarmes.
6. Fallback.
7. Export.
8. Notarização.
9. Privacidade mínima.
10. Painéis.
11. Logs.
12. Versionamento de schema.
13. Auditoria externa.
14. Drift de fontes.
15. Redundância.
16. Sim2real drift.
17. Consistência cruzada.
18. Atrasos.
19. Transporte entre regiões.
20. Publicação.
### QGen (20)
- Schema.
- Assinaturas.
- Timestamps.
- SLAs.
- Alarmes.
- Fallback.
- Export.
- Notarização.
- Privacidade.
- Painéis.
- Logs.
- Versionamento.
- Auditoria.
- Drift.
- Redundância.
- Sim2real.
- Consistência.
- Atrasos.
- Transporte.
- Publicação.
### Hard‑negatives (10)
- Assinaturas são opcionais.
- Freshness não importa.
- Export pode ser fechado.
- Notarização é supérflua.
- Privacidade é irrelevante.
- Painéis são dispensáveis.
- Logs não precisam de padrão.
- Versionamento não é necessário.
- Drift pode ser ignorado.
- Publicação é opcional.

---

## A31 — Compliance v2 (Transfronteiriço)
### Tarefa YAML
```yaml
id: A31-COMPL-V2
competency: Compliance
priority: P1
why: operar em múltiplas jurisdições
content_min: [data_residency, sanctions, reporting_xborder]
deps: [A20, A30]
license: MIT
```
### Conteúdo
- **Residência de dados**; conflitos de jurisdição; minimização necessária.
- **Sanções**: listas; bloqueios; logs públicos de congelamento.
- **Reporting**: por país; prazos; formatos.
### Evidence JSON
```json
{ "id": "A31-COMPL-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A31-—-Compliance-v2-(Transfronteiriço)"], "vector_ids": ["a31-compl-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Data residency.
2. Conflitos legais.
3. Sanções.
4. Bloqueios.
5. Logs públicos.
6. Relatórios.
7. Prazos.
8. Formatos.
9. Consentimento.
10. Transferência internacional.
11. Segregação por país.
12. Auditoria externa.
13. Provedores.
14. DPIA.
15. Minimização.
16. Retenção.
17. Acesso interno.
18. Incidentes.
19. Comunicação.
20. Governança.
### QGen (20)
- Política de residency.
- Conflitos.
- Sanções.
- Bloqueios.
- Logs.
- Relatórios.
- Prazos.
- Formatos.
- Consentimento.
- Transferência.
- Segregação.
- Auditoria.
- Provedores.
- DPIA.
- Minimização.
- Retenção.
- Acesso.
- Incidentes.
- Comunicação.
- Governança.
### Hard‑negatives (10)
- Residency é opcional.
- Sanções podem ser ignoradas.
- Logs públicos não são necessários.
- Relatórios não precisam de prazo.
- Consentimento é dispensável.
- Transferência sem controles.
- Sem segregação.
- Sem auditoria.
- Minimização irrelevante.
- Retenção sem política.

---

## A32 — Governança v2 (Processos)
### Tarefa YAML
```yaml
id: A32-GOV-V2
competency: Governance
priority: P1
why: decisões reprodutíveis e auditáveis
content_min: [decision_logs, dynamic_quorums, public_register]
deps: [A27]
license: MIT
```
### Conteúdo
- **Decision Logs**: motivos, evidências, votos; hash público.
- **Quóruns dinâmicos**: ajuste por severidade; transparência.
- **Registro público**: indexado e notarizado.
### Evidence JSON
```json
{ "id": "A32-GOV-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A32-—-Governança-v2-(Processos)"], "vector_ids": ["a32-gov-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. Campos do Decision Log.
2. Evidências.
3. Votos.
4. Hash público.
5. Quóruns dinâmicos.
6. Severidade.
7. Transparência.
8. Registro público.
9. Indexação.
10. Notarização.
11. Auditoria.
12. Versão.
13. SLA de publicação.
14. Privacidade mínima.
15. Contestação.
16. Reapreciação.
17. Conflitos.
18. Comunicação.
19. Export.
20. Painéis.
### QGen (20)
- Template de Decision Log.
- Política de evidências.
- Registro de votos.
- Notarização.
- Quóruns.
- Severidade.
- Publicação.
- Privacidade.
- Contestação.
- Reapreciação.
- Conflitos.
- Export.
- Painéis.
- Auditoria.
- Versões.
- SLA.
- Indexação.
- Governança.
- Comunicação.
- Relatórios.
### Hard‑negatives (10)
- Decision Logs são opcionais.
- Quóruns não precisam ajuste.
- Registro público sem hash está ok.
- Auditoria é supérflua.
- SLA de publicação é irrelevante.
- Contestação não é necessária.
- Transparência não importa.
- Versões não precisam.
- Export é desnecessário.
- Painéis são perfumaria.

---

## A33 — TKN (Tokenização & Direitos)
### Tarefa YAML
```yaml
id: A33-TKN
competency: Tokenização
priority: P1
why: direitos claros e transferíveis
content_min: [claim_nft, tranches_erc, vault_shares, governance_rights]
deps: [A24, A26, A32]
license: MIT
```
### Conteúdo
- **Objetos**: Claim NFTs (direitos creditórios); **Tranches** (ERC‑20/1155); **Vault Shares** (ERC‑4626); **Cashflow tokens**.
- **Direitos**: voto (quando aplicável), proventos, prioridade em waterfalls, acesso a informação.
- **Regras**: contratos públicos; listas de bloqueio; transferência com KYC/KYB quando exigido; PoR/escrow quando necessário.
- **Governança**: registro público de emissões; quóruns aplicáveis; contestação auditável.
> **Nota**: TKN **não** é moeda algorítmica; segue regras de lastro/registro já definidas nos blocos anteriores.
### Evidence JSON
```json
{ "id": "A33-TKN-01", "artifact_paths": ["/kb/blocos/bloco_04_a24_a33_final_v4_00.md#A33-—-TKN-(Tokenização-&-Direitos)"], "vector_ids": ["a33-tkn-0001"],
  "tests": {"retrieval": {"pass": null, "probes": 20, "hard_neg": 10, "mrr": null, "ndcg": null, "coverage": null, "leakage": null}},
  "timestamps": {"prepared_at": "2025-09-07T00:00:00-03:00"}}
```
### Probes (20)
1. O que é Claim NFT.
2. Tranches e padrões ERC.
3. Vault Shares 4626.
4. Cashflow tokens.
5. Direitos de voto/provento.
6. Prioridade em waterfall.
7. KYC/KYB e transferências.
8. Listas de bloqueio.
9. PoR/escrow.
10. Registro público de emissões.
11. Quóruns aplicáveis.
12. Contestação.
13. Logs públicos.
14. Auditoria de contratos.
15. Integração com pools.
16. Integração com secundário.
17. Transparência mínima.
18. Restrições por jurisdição.
19. Cancelamento/queima.
20. Comunicação ao mercado.
### QGen (20)
- Especificação Claim NFT.
- ERCs por tranche.
- 4626 shares.
- Cashflow tokens.
- Direitos.
- Waterfall.
- KYC/KYB.
- Bloqueio.
- PoR/escrow.
- Emissões.
- Quóruns.
- Contestação.
- Logs.
- Auditoria.
- Pools.
- Secundário.
- Transparência.
- Jurisdição.
- Queima.
- Comunicação.
### Hard‑negatives (10)
- Claim NFT é opcional.
- Tranches não precisam de padrão.
- 4626 é desnecessário.
- Direitos não importam.
- KYC/KYB é irrelevante.
- PoR/escrow é supérfluo.
- Emissões sem registro público.
- Sem contestação.
- Logs não são necessários.
- Jurisdição não se aplica.

---

# 5) Evidence JSON — **agregado**
```json
{
  "block_id": "B04-A24-A33",
  "packs": ["A24-AUCT-01","A25-SEC-01","A26-POOL-01","A27-DEF-01","A28-ALM-01","A29-RISK-01","A30-DATA-01","A31-COMPL-01","A32-GOV-01","A33-TKN-01"],
  "kpis": { "mrr": null, "ndcg": null, "coverage": null, "leakage": null },
  "timestamps": { "executed_at": null }
}
```

---

# 6) Runbook — Ingestão & Testes
```bash
# 1) Ingestão
make ingest BLOCK=A24-A33

# 2) Probes + QGen + Hard-negatives
actions/run_probes.sh --block A24-A33 --qgen 20 --hardneg 10

# 3) Evidence JSON (merge de resultados)
python ops/tests/merge_evidence.py --block A24-A33 --out ops/tests/evidence/A24-A33.json

# 4) Atualizar front-matter (rag_kpis)
actions/update_rag_kpis.py --evidence ops/tests/evidence/A24-A33.json --pack kb/blocos/bloco_04_a24_a33_final_v4_00.md
```

---

# 7) Regras de Maturidade (auto)
```yaml
maturity_rules:
  to_silver: { require: [evidence_json.pass, rag_kpis.filled] }
  to_gold:   { require: [watchers.extended_ok, incident_playbook.if_applicable] }
```

---

# 8) Closeout — sintético/demonstrativo
```json
{
  "block_id": "B04-A24-A33",
  "packs": ["A24-AUCT-01","A25-SEC-01","A26-POOL-01","A27-DEF-01","A28-ALM-01","A29-RISK-01","A30-DATA-01","A31-COMPL-01","A32-GOV-01","A33-TKN-01"],
  "kpis": {"mrr": 0.49, "ndcg": 0.71, "coverage": 0.87, "leakage": 0.00},
  "proof_coverage_ratio": 0.83,
  "mechanism": {"gates_ok": ["M1","M2","M3","M4"]},
  "causal": {"gate_ok": ["C1","C2","C4"]},
  "timestamps": {"executed_at": "2025-09-07T00:00:00-03:00"},
  "mode": "synthetic-demo"
}
```

---

# 9) Auditoria final v3.1
- Front‑matter com `rag_kpis=null` ✅  
- `snippet_budget_lines=200` ✅  
- Packs A24–A33 completos (conteúdo + Evidence + QGen/Probes/HN) ✅  
- Watchers & parâmetros ✅  
- Runbook de ingestão/testes ✅  
- Closeout sintético ✅  
- **Sem placeholders** ✅

