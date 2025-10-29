# Q2 vFinal++ — MBP + Oráculo (Wave 1) — Especificação 100/10 (S7..S12) + Superprompt Codex

Contexto: Repositório canônico `trendmarketv2`. DNA v2 e A110 são fonte canônica. Free‑tier estrito (DuckDB/SQLite, GitHub Actions, testnets EVM). Orçamento em dinheiro reservado apenas para Beta Fechado. Corte de Q2 = R‑1.0 pronto para Beta Fechado. Este documento substitui versões anteriores do Q2 e consolida as melhorias do comitê, elevando a spec a 100/10.

Objetivo macro de Q2: provar tecnicamente o oráculo BR/LatAm 0→1 em produção e operar o MBP binário com governança de risco (limites de exposição + kill‑switch por categoria), transparência pública e trilhas de evidências, reduzindo risco tecnológico e operacional para Q3.

Resultados‑chave até R‑1.0: staleness p95 ≤ 20s e divergence p95 ≤ 1,0% por 7 dias; auto‑resolução ≥ 95% com override ≤ 5%; uptime ≥ 99,5% (Q2); status público com monitor externo, link de abuso/appeals e template de post‑mortem; política de exposição publicada e kill‑switch por categoria testado em staging; primeiro relatório semanal de shadow backtests de fee; 0 P1 por 14 dias antes do corte; bundles de evidência S7..S12 assinados.

Invariantes de Build (I1..I7) — gates bloqueantes no CI: I1: nenhum vazamento de segredo (gitleaks==0). I2: Trivy HIGH/CRITICAL==0. I3: workflows YAML válidos. I4: evidências presentes por sprint. I5: toolchain ruff/pytest instalada e operante. I6: docs críticos presentes (policy de exposição, runbook kill‑switch, post‑mortem template). I7: doc público da Status API presente.

Invariantes de Produto (P1..P9) — validadas por watchers/testes:
P1: proof append‑only por sprint que toca ingest.
P2: staleness por fonte ≤ 15s (staging).
P3: divergence p95 global ≤ 1%.
P4: finalização do consenso ≤ 90s.
P5: throughput consenso ≥ 5k eventos/min p95 (dataset sintético) com memória ≤ 512MB e CPU ≤ 1 vCPU em CI; footprint steady‑state ≤ 128MB.
P6: ≥95% auto‑resolução e override ≤5%.
P7: exposure policy paramétrica (por categoria/tier/fonte) aplicada e com testes de limites; kill‑switch testado (ativar/reverter).
P8: A11y WCAG AA comprovada por matriz e evidência de navegação por teclado/taborder em Disputes/Status.
P9: status público UP 7 dias + shadow report semanal gerado.

Plano de Sprints (S7→S12, duas semanas cada):

S7 — Modelo de Evento, Normalização, Prova Append‑only e Assinatura Ed25519 com Rotação. Escopo: contrato canônico `contracts/data/event_v1.json`; normalizador PT/ES (canonização, datas ISO, entidades, `equivalenceHash` determinístico); dedup (hash+heurística); writer de lote com Merkle root + timestamp; **assinatura Ed25519** do lote; **rotação de chaves a cada 90 dias** com cadeia de confiança e política de custódia; harness de verificação append‑only + assinatura; ADRs de modelo, assinatura, rotação/custódia; regras de frescor iniciais. DoD: testes goldens 100%; p95 normalização ≤ 150 ms; `out/evidence/S7_event_model/proof_append_only.json` e `signature.json` gerados; `keystore.json` presente; ADR‑Event‑Model, ADR‑Event‑Signing e ADR‑Key‑Rotation versionados. Aceitação: P1 verde, I1..I5 verdes.

S8 — Adapters Tier‑1 BR/LatAm e Health/Compliance. Escopo: ~15 fontes com DSL mínima (fetch→parse→normalize), idempotência, retries, rate‑limit e circuit breaker; respeito a robots/ToS; health endpoints por fonte; painel “Oracle Sources”; segregação mínima de funções (dois operadores em rodízio, logs assinados). DoD: staleness p95 por fonte ≤ 15s (staging); falha isolada não derruba pipeline; `out/evidence/S8_sources_health/health_report.json`. Aceitação: P2 verde, I1..I5 verdes.

S9 — Consenso v1 (2/3 + mediana ponderada), Watchers, Perf/Throughput & Memória. Escopo: engine `services/oracle/consensus/v1` com quorum 2/3; mediana ponderada por `trust_0`; watchers de staleness/divergence/uptime; **bench de throughput/memória** com dataset sintético (50k, 100k, 250k eventos) e orçamentos definidos; build gates no CI; ADR de consenso + ADR de perf. DoD: divergence p95 ≤ 1%, finalização ≤ 90s, **≥ 5k eventos/min p95** no dataset de 100k com memória ≤ 512MB em CI e steady ≤ 128MB local; `out/evidence/S9_consensus_v1/` com logs de quórum, `perf_report.json` e `ci_gates_report.json`; I1..I7 OK. Aceitação: P3, P4, P5 verdes, I1..I7 verdes.

S10 — MBP v1 Binário, Settlement e Disputa v1 com A11y e Exposição Paramétrica. Escopo: settlement binário e ledger local (DuckDB/CSV), reconciliação D+1; disputa v1 (janela, stake, override auditado); microcopy final PT‑BR/ES; **A11y WCAG AA** (teclado/ARIA) nas telas de Dispute; **política de exposição paramétrica** (YAML) por categoria/tier/fonte publicada e validações no backend. DoD: ≥ 95% auto‑resolução; override ≤ 5%; **A11y matrix** anexada e evidência de teclado/taborder gravada; `out/evidence/S10_end_to_end_settlement/` com extratos e prints A11y; `exposure_policy_q2.yml` e testes de limites aprovados. Aceitação: P6, P7 (policy) e P8 verdes, I1..I7 verdes.

S11 — Antimanipulação v1, Simulador e Kill‑switch por Categoria. Escopo: guardas (outlier, semantic‑dedup, clusterização leve); simulador de ataques com KPIs; kill‑switch por categoria (flag runtime + banner em UI) e runbook `docs/runbooks/kill_switch_category.md`. DoD: sob ataques simulados, divergence p95 ≤ 1% e staleness p95 ≤ 20s; ativação/reversão do kill‑switch com `out/evidence/S11_attack_sims/kill_switch_test.log`. Aceitação: P7 (completo) verde, I1..I7 verdes.

S12 — Transparência Pública v1 (Status/API/SDK), Shadow Backtests semanal e Monitor Externo. Escopo: Status API v1 (`/status`); **monitor externo UptimeRobot (Free, 5‑min interval) configurado**, alvo `/status` com latência < 1.5s p95 e disponibilidade ≥ 99,5%; link de abuso/appeals e template de post‑mortem público; API v1 com quotas/chaves e **webhooks HMAC**; **SDK v0 (read/verify) com contrato de versionamento SemVer** e **testes de conformidade**; pipeline de shadow backtests de fee com relatório semanal MD→PDF. DoD: p95 da API ≤ 200ms local; monitor “UP” 7 dias (capturas do UptimeRobot + `monitor_external_report.json`); primeiro relatório semanal publicado; `out/evidence/S12_api_status/` preenchido; testes de conformance do SDK v0 aprovados. Aceitação: P9 e I1..I7 verdes.

Estrutura de Repositório (alvos de Q2, atualizada): contracts/data/event_v1.json; services/oracle/normalizer/*; services/oracle/adapters/*; services/oracle/consensus/v1/*; services/oracle/guards/*; services/mbp/binary/*; services/mbp/validation/exposure.py; api/status.py; ui/disputes/*; ui/banners/kill_switch_banner.*; scripts/fees/fees_shadow.py; scripts/perf/consensus_bench.py; scripts/ci/*; scripts/dr/backup_restore.sh; scripts/crypto/sign_batch.py; tools/crypto/keystore.json; docs/econ/exposure_policy_q2.md; **docs/econ/exposure_policy_q2.yml**; docs/runbooks/kill_switch_category.md; docs/public/postmortem_template.md; docs/public/status_api_v1.md; **docs/public/monitor_external.md**; **docs/a11y/wcag_aa_matrix_disputes_status.md**; docs/release/R-1.0-checklist.md; models/tla/append_only/append_only.tla; models/tla/consensus/consensus_v1.tla; models/tla/guards/kill_switch.tla; out/evidence/<SPRINT>/ (gerado).

Criptografia — Assinatura Ed25519, Rotação e Custódia: `tools/crypto/keystore.json` armazena chaves com `kid`, `alg: Ed25519`, `created_at`, `not_after`, `issuer`, `pubkey`, `status`. Política: rotação a cada 90d; retenção de 1 chave ativa + 1 anterior (overlap 7d); custódia lógica separada (pasta com permissões restritas + audit trail). CLI: `scripts/crypto/sign_batch.py` assina o `batch_{ts}.json` (Merkle root) gerando `signature.json` com `{kid, alg, sig, merkle_root, ts}`; verificador no CI valida assinatura. ADR‑Key‑Rotation documenta cadeia de confiança e processo de rotação; `run_invariants.py` falha se `keystore.json` estiver ausente/fora da política.

Exposure Policy Paramétrica (YAML) + Testes de Limite: `docs/econ/exposure_policy_q2.yml` contém `categories: [politics, sports, entertainment, ...]`, `tiers: [guest, verified, pro]`, `limits: { per_market_pool_cap, per_user_category_cap, per_user_daily_cap }`, `sources_overrides`. Backend aplica validações; testes `tests/test_exposure_limits.py` cobrem limites, fronteiras (==, >, <) e combinações tier×categoria×fonte; UI exibe mensagens específicas PT‑BR/ES; doc MD espelha YAML e é linkado na UI.

WCAG AA — Matriz e Evidência: `docs/a11y/wcag_aa_matrix_disputes_status.md` cataloga critérios (percebível/operável/compreensível/robusto), roles/ARIA, foco visível, ordem tabular, atalhos de teclado, contrastes, labels, estados; protocolo de teste inclui **vídeo/gif** de navegação por teclado (sem mouse) cobrindo fluxo Dispute/Status; evidências salvas em `out/evidence/S10_end_to_end_settlement/a11y/`.

DR Test — Backup/Restore (Q2): `scripts/dr/backup_restore.sh` realiza dump horário (DuckDB/CSV), simula perda e restaura; critérios de aprovação: RPO ≤ 10m, RTO ≤ 45m; salva logs/tempos em `out/evidence/DR_Q2/backup_restore.log`; PR final precisa anexar esse log.

Perf Harness & k6: `scripts/perf/consensus_bench.py` gera datasets 50k/100k/250k, mede latências/throughput/memória; escreve `out/reports/perf/perf_report.json` e gráfico simples PNG. `k6` para `/status` com 50 VUs/3min e SLO p95 ≤ 200ms (arquivo `k6/status_test.js`); resultados copiados para `out/evidence/S12_api_status/`.

SDK v0 — Contrato e Conformance: SemVer estrito. `sdk/python/` com funções `read_status()`, `verify_signature(batch, signature, pubkey)`. Testes `tests/sdk/test_sdk_conformance.py` garantem: compatibilidade do wire format, verificação Ed25519, tratamento de erros e versionamento (`__version__`). Checklist de publicação e CHANGELOG.

Monitor Externo — UptimeRobot Free: documentação em `docs/public/monitor_external.md` (intervalo 5min, 2 falhas seguidas para DOWN, latência p95 < 1.5s, alvo `/status` com cabeçalho `Cache-Control: no-store`). Evidência `monitor_external_report.json` + screenshots exportados semanalmente para `out/evidence/S12_api_status/`.

Mapeamento P‑invariantes → TLA+/Assertions: P1↔`append_only.tla` (invariantes: impossibilidade de remoção/alteração; monotonicidade da raiz Merkle). P3/P4↔`consensus_v1.tla` (segurança: não‑divergência de decisão; liveness: decisão ≤ N rounds; quorum ≥2/3). P7↔`kill_switch.tla` (safety: com kill‑switch ativo, nenhum evento da categoria é processado; liveness: reversão reativa após sinal). `run_tla` no CI executa Apalache nessas specs quando presentes e publica traces em `out/evidence/<SPRINT>/tla/`.

CI/ORR (refinado): `_s4-orr.yml` agora também verifica (I8) keystore válido e assinatura presente quando existir `out/evidence/*/batch_*.json` (falha se ausente). `run_invariants.py` inclui validação de `keystore.json`, `signature.json`, `monitor_external_report.json` (quando S12), presença de `perf_report.json` (S9) e de `a11y/` (S10).

SLOs e Alertas (Q2): ingest p95 ≤ 150 ms; agregação p95 ≤ 200 ms; consenso p95 ≤ 400 ms; API p95 ≤ 200 ms; throughput consenso ≥ 5k ev/min p95 (100k dataset) em CI; burn‑rate (1h/6h/24h); MTTR p95 ≤ 6h. DR: backup horário; restore test 1×; RPO ≤ 10 m, RTO ≤ 45 m.

Segurança e Privacidade: CSP/Trusted Types, OAuth2+PKCE, HMAC nos webhooks, rotação de chaves 90d, LGPD minimização/DSRs, link de appeals.

RACI/WIP: S7 Oráculo; S8 Oráculo; S9 Oráculo+SRE; S10 MBP+Produto/UX; S11 Oráculo+Segurança; S12 Plataforma+DevRel. WIP ≤ 2 sprints.

Riscos/Mitigações: fontes mudam → adapters tolerantes + fallback 24–48h. Divergência >1% persistente → ajuste `trust_0` + triagem auditada. Disputas frívolas → depósito mínimo + anti‑spam. Falhas API → WAF/rate‑limit; modo leitura; health externo. PII → isolamento/rotação/notificação/RCA com post‑mortem.

Go/No‑Go R‑1.0 (atualizado): staleness p95 ≤ 20s e divergence p95 ≤ 1% por 7 dias; ≥ 95% auto‑resolução; 0 P1 por 14 dias; status público com monitor externo (UptimeRobot) e appeals/post‑mortem; exposure policy paramétrica publicada e kill‑switch testado; bundles S7..S12 assinados; shadow report semanal #1; DR log aprovado; perf P5 atingido.

Execução PR‑first (ordem e convenções): branches `q2/s7-event-model`, `q2/s8-adapters`, `q2/s9-consensus`, `q2/s10-mbp`, `q2/s11-anti-manip`, `q2/s12-status`. Cada PR: escopo, mudanças, DoD, evidências `out/evidence/<SPRINT>/`, resultado I1..I7(+I8), links ADRs/TLA. Merge somente com `_s4-orr` verde. PR final `release/r-1.0` com checklist e evidências.

Plano de Testes: unitários (normalizador, equivalenceHash, guards, payout, SDK), integrados (adapters com fixtures, consenso em datasets, ledger/reconciliação), E2E determinísticos (criação→aposta→resolução→payout→disputa), perf/soak e DR.

Quickstart local de validação: `pytest -q`; `python services/oracle/normalizer/merkle_append_only.py`; `python scripts/crypto/sign_batch.py out/evidence/S7_event_model/batch_*.json`; `uvicorn api.status:app --host 0.0.0.0 --port 8080`; `k6 run k6/status_test.js`; `python scripts/perf/consensus_bench.py`; `bash scripts/dr/backup_restore.sh`.

Superprompt — Versão Definitiva (Q2 vFinal++ → Codex, PR‑first, zero placeholders): Papel: AG2 (Codex Eng). Repositório: `trendmarketv2`. Objetivo: materializar integralmente esta especificação de Q2 (S7..S12) para entregar R‑1.0. Restrições: free‑tier; tudo reprodutível; evidências por sprint; gates I1..I7(+I8) bloqueantes. Estratégia: 6 PRs (S7..S12) + PR final de release. Para cada PR, criar exatamente a estrutura e os arquivos listados nesta spec, implementar funcionalidades, testes, TLA stubs e evidências conforme DoD/Aceitação; atualizar `CHANGELOG.md`; rodar `_s4-orr` até verde e publicar `s4-orr-evidence`. Abrir PR “R‑1.0 Release Train” com checklist e links de evidências. Política de falha: qualquer gate vermelho bloqueia merge; corrigir antes de re‑rodar. Resultado esperado: oráculo verificável (append‑only + assinatura/rotação), consenso v1 com metas de perf/mem, MBP binário com settlement/dispute/A11y/limites paramétricos, kill‑switch por categoria, status público/monitor/appeals/post‑mortem, shadow backtests semanais, DR test e ORR/CI sólidos; pronto para Beta Fechado (R‑1.0).
