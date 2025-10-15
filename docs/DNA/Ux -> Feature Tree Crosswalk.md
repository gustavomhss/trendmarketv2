---
id: kb/crosswalk/ux_to_feature_tree_v13_enriched
Title: "UX → Feature Tree Crosswalk — Enriched (v13 • MASTER • vPro)"
version: "2025-09-10"
date: "2025-09-10"
timezone: America/Bahia
owner: PO (Credit Engine Product Master)
doc_type: mapping_enriched
notes: "Crosswalk bidirecional com Owner, Hooks A110 e links (OpenAPI/JSON Schemas/Evidence). Fonte: Feature Tree v13 (120 cards)."
---

> Convenções de link: `openapi:` caminho de rota; `schema:` arquivo JSON Schema; `evidence:` caminho padrão (`evidence/feat-<id>-*.json`). Owners seguem defaults por domínio.

# 0) Owners por domínio (defaults)
- **A Entrar & Habilitar**: SEC (prim.), PM, INT, FE  
- **B Pedir Preço**: DEC (prim.), FE, PLAT, INT  
- **C Descobrir Preço Justo**: PM/Treasury (prim.), SRE/PLAT, ML  
- **D Decidir & Aceitar**: DEC (prim.), PM, ML, SRE  
- **E Formalizar & Liquidar**: INT/OPS (prim.), PM, RSK/Treasury  
- **F Pós‑Trade & Governança**: OPS/SRE (prim.), SEC, RSK, DATA

# 1) Autenticação, Conta & Identidade (A)
| Clássico | Feature ID — Nome | Owner | Hooks A110 (exemplos) | Links |
|---|---|---|---|---|
| Login (com MFA) | F‑A‑11 — MFA Adaptativo | SEC/FE | `dep_vuln_watch`; `idp_keys_rotation_watch`; `web.inp.p75>200ms•24h->rollback_FE` | openapi:`/mfa/challenge` • schema:`account.v1.json` • evidence:`evidence/feat-F-A-11-*.json` |
| Sessão/Quarentena | F‑A‑12 — Session Quarantine | SEC/PLAT | `alert_storm_watch`; `policy_violation_watch` | openapi:`/session/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-12-*.json` |
| Device Trust | F‑A‑06 — Device Binding | SEC/FE | `image_vuln_regression_watch`; `privacy_budget>1.5x•1h->freeze` | openapi:`/device/bind` • schema:`attachment.v1.json` • evidence:`evidence/feat-F-A-06-*.json` |
| Troca/Reset senha | (via IdP) + F‑A‑11/F‑A‑06/F‑A‑14 | SEC/PM | `idp_keys_rotation_watch`; `dp_budget_breach_watch` | openapi:`/privacy/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-14-*.json` |
| Onboarding conta | F‑A‑03 — Onboarding de Contas/Carteiras | PM/INT | `api_breaking_change_watch`; `schema_registry_drift_watch` | openapi:`/accounts/link` • schema:`account.v1.json` • evidence:`evidence/feat-F-A-03-*.json` |
| KYC/Consentimento | F‑A‑01 — Consent & KYC Fast‑Track | SEC/PM/INT | `privacy_budget_guard`; `dp_budget_breach_watch` | openapi:`/kyc/start|callback` `/consents` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-01-*.json` |
| Enriquecer perfil | F‑A‑04 — Profile Enrichment | PM/DATA | `doc_coverage_watch`; `schema_registry_drift_watch` | openapi:`/profile/enrich` • schema:`account.v1.json` • evidence:`evidence/feat-F-A-04-*.json` |
| Revogar consent. | F‑A‑05 — Consent Revocation | SEC/PM | `privacy_budget_guard` | openapi:`/consents/revoke` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-05-*.json` |
| Flags de risco | F‑A‑07 — Risk Flags (PF/PJ) | DATA/ML | `model.psi>0.2•24h->rollback_model` | openapi:`/risk/flags` • schema:`risk.flag.v1.json` • evidence:`evidence/feat-F-A-07-*.json` |
| PEP/Sanctions | F‑A‑08 — Sanctions/PEP Screening | SEC/PM | `idp_keys_rotation_watch`; `dp_budget_breach_watch` | openapi:`/kyc/screen` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-08-*.json` |
| KYB Docs | F‑A‑09 — KYB Docs Workflow | SEC/PM | `schema_registry_drift_watch` | openapi:`/kyb/docs` • schema:`attachment.v1.json` • evidence:`evidence/feat-F-A-09-*.json` |
| Data Residency | F‑A‑10 — Data Residency Guard | SEC/RSK | `privacy_budget>1.5x•1h->freeze` | openapi:`/privacy/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-10-*.json` |
| Portal do titular | F‑A‑14 — Portal do Titular (LGPD) | SEC/PM | `privacy_budget_guard` | openapi:`/privacy/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-14-*.json` |
| KYC Fallback | F‑A‑15 — KYC Provider Fallback | SEC/PM | `oracle.staleness>30s•5m->TWAP+failover` | openapi:`/kyc/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-15-*.json` |
| Explainability | F‑A‑16 — Risk‑Score Explainability | ML/PM | `ab.srm_fail•run->pause+audit` | openapi:`/risk/explain` • schema:`audit.v1.json` • evidence:`evidence/feat-F-A-16-*.json` |

# 2) RFQ & Solicitação (B)
| Clássico | Feature ID — Nome | Owner | Hooks A110 | Links |
|---|---|---|---|---|
| Criar RFQ | F‑B‑01 — RFQ Mínima | DEC/INT | `api_breaking_change_watch`; `slo_budget_burn>2x•30m->freeze_releases` | openapi:`/rfq` • schema:`offer.v1.json` • evidence:`evidence/feat-F-B-01-*.json` |
| Anexos | F‑B‑02 — Collateral & Attachments | INT/FE | `cache_ttl_misuse_watch` | openapi:`/rfq/attachments` • schema:`attachment.v1.json` • evidence:`evidence/feat-F-B-02-*.json` |
| Explicabilidade | F‑B‑03 — Eligibility Explanations | DEC/PM | `decision.latency>0.8s•5m->degrade_route` | openapi:`/eligibility/explain` • schema:`contract.v1.json` • evidence:`evidence/feat-F-B-03-*.json` |
| Idempotency & Retries | F‑B‑04 — RFQ Idempotency & Retries | INT/PLAT | `idempotency_conflict_watch`; `contract_tests_fail_pct>0->block_release` | openapi:`/rfq` • schema:`offer.v1.json` • evidence:`evidence/feat-F-B-04-*.json` |
| Abuse/Quotas | F‑B‑05 — Abuse Guard & Quotas | PLAT/SRE | `rate_limit_breach_watch` | openapi:`/` (GW) • schema:`audit.v1.json` • evidence:`evidence/feat-F-B-05-*.json` |
| RFQ Batch | F‑B‑06 — RFQ Batch | DEC/INT | `slo_budget_burn>2x•30m->freeze_releases` | openapi:`/rfq/batch` • schema:`offer.v1.json` • evidence:`evidence/feat-F-B-06-*.json` |
| Multi‑SKU | F‑B‑07 — RFQ Multi‑SKU | DEC/PM | `api_breaking_change_watch` | openapi:`/rfq?sku=` • schema:`offer.v1.json` • evidence:`evidence/feat-F-B-07-*.json` |
| Cancel/Amend | F‑B‑08 — RFQ Cancel/Amend | DEC/INT | `policy_violation_watch` | openapi:`/rfq/{id}/cancel|amend` • schema:`contract.v1.json` • evidence:`evidence/feat-F-B-08-*.json` |
| Sandbox | F‑B‑09 — RFQ Sandbox | INT/PM | `policy_violation_watch` | openapi:`/rfq/sandbox/*` • schema:`offer.v1.json` • evidence:`evidence/feat-F-B-09-*.json` |
| Validation Rules | F‑B‑10 — Validation Ruleset | DEC/PM | `api_breaking_change_watch` | openapi:`/rfq/validate` • schema:`contract.v1.json` • evidence:`evidence/feat-F-B-10-*.json` |
| Rate Limits & Telemetry | F‑B‑11 | PLAT/SRE | `alert_storm_watch`; `slo_burn_freeze` | openapi:`/` (GW) • schema:`audit.v1.json` • evidence:`evidence/feat-F-B-11-*.json` |
| Quote Cache | F‑B‑12 — Quote Snapshot Cache | PLAT/SRE | `price.cache_watch` | openapi:`/quotes/snap` • schema:`offer.v1.json` • evidence:`evidence/feat-F-B-12-*.json` |
| Dicionário de erros | F‑B‑13 — RFQ Error Dictionary | FE/PM | `api_breaking_change_watch` | openapi:`/rfq/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-B-13-*.json` |
| Schema Lints FE | F‑B‑14 | FE | `web.inp.p75>200ms•24h->rollback_FE` | openapi:`/` (lint FE) • schema:`contract.v1.json` • evidence:`evidence/feat-F-B-14-*.json` |
| UX progressiva | F‑B‑15 — Progressive UX | FE/PM | `web.inp_regression` | openapi:`/` (FE) • schema:`contract.v1.json` • evidence:`evidence/feat-F-B-15-*.json` |
| Pré‑check tributos | F‑B‑16 — Pre‑Check Tributos | PM/DEC | `contract_break->rollback+waiver_timebox` | openapi:`/tax/indicative` • schema:`statement.v1.json` • evidence:`evidence/feat-F-B-16-*.json` |

# 3) Pricing, Oráculos & Execução (C)
| Clássico | Feature ID — Nome | Owner | Hooks A110 | Links |
|---|---|---|---|---|
| Oráculos | F‑C‑01 — Oracles (multi‑fonte + TWAP + Quorum) | PM/Treasury, SRE | `oracle.staleness>30s•5m->TWAP+failover`; `oracle_divergence_watch` | openapi:`/oracles/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-01-*.json` |
| Leilão | F‑C‑02 — Auction Single‑Price | PM/SRE | `halt_auction` | openapi:`/auction/commit` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-02-*.json` |
| CIP/CLS & calendários | F‑C‑03 | PM/RSK | `cls_payin_cutoff_watch` | openapi:`/calendars/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-C-03-*.json` |
| Best‑Execution | F‑C‑04 — Best‑Execution Router | SRE/DEC | `degrade_route` | openapi:`/router/*` • schema:`route.plan.v1.json` • evidence:`evidence/feat-F-C-04-*.json` |
| Liquidez & Heatmap | F‑C‑05 | PM/ML | `liquidity_regression_watch` | openapi:`/liquidity/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-05-*.json` |
| Benchmark Feeds | F‑C‑06 | PM/SRE | `oracle_divergence_watch` | openapi:`/benchmarks/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-06-*.json` |
| Venue Health/Timeouts | F‑C‑07 | SRE/PLAT | `exclude_venue`; `timeout_guard` | openapi:`/venues/health` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-07-*.json` |
| Spread Guard | F‑C‑08 | PM/DEC | `spread_breach_watch` | openapi:`/spread/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-08-*.json` |
| Price Fairness (ELO) | F‑C‑09 | PM/ML | `fairness_drift_watch` | openapi:`/fairness/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-09-*.json` |
| TWAP Failover Drill | F‑C‑10 | PM/SRE | `TWAP+failover` | openapi:`/oracles/drill` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-10-*.json` |
| Auction Replay Audit | F‑C‑11 | PM/SRE | `audit` | openapi:`/auction/replay` • schema:`audit.v1.json` • evidence:`evidence/feat-F-C-11-*.json` |
| Maker Concentration | F‑C‑12 | PM/RSK | `concentration_guard` | openapi:`/makers/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-12-*.json` |
| Stress Scenarios | F‑C‑13 | PM/SRE | `breakers` | openapi:`/stress/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-13-*.json` |
| Calendar Exceptions | F‑C‑14 | PM/RSK | `cls_exception_guard` | openapi:`/calendars/exceptions` • schema:`audit.v1.json` • evidence:`evidence/feat-F-C-14-*.json` |
| Quote Explainability | F‑C‑15 | DEC/PM | `policy_audit` | openapi:`/quotes/explain` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-15-*.json` |
| Basis Monitor | F‑C‑16 | PM/SRE | `basis_breach_watch` | openapi:`/basis/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-16-*.json` |
| Slippage Guard | F‑C‑17 | PM/SRE | `slippage_spike_watch` | openapi:`/slippage/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-17-*.json` |
| Geo‑Failover | F‑C‑18 | SRE/PLAT | `geo_failover` | openapi:`/venues/failover` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-18-*.json` |
| Price Clamp & TTL | F‑C‑19 | DEC/PM | `ttl_matrix_guard` | openapi:`/quotes/ttl` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-19-*.json` |
| Haircut Hint | F‑C‑20 | DEC/PM | `haircut_regression_watch` | openapi:`/collateral/haircut` • schema:`contract.v1.json` • evidence:`evidence/feat-F-C-20-*.json` |
| Dealer Commitment | F‑C‑21 | PM/RSK | `commitment_drop_watch` | openapi:`/dealers/commitment` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-21-*.json` |
| CIP Regression | F‑C‑22 | PLAT/SRE | `contract_tests_fail_pct>0->block_release` | openapi:`/cip/test` • schema:`audit.v1.json` • evidence:`evidence/feat-F-C-22-*.json` |
| FX Latency Map | F‑C‑23 | SRE/PLAT | `latency_map_guard` | openapi:`/latency/map` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-23-*.json` |
| Liquidity Heat Replay | F‑C‑24 | PM/SRE | `replay_guard` | openapi:`/liquidity/replay` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-24-*.json` |
| Circuit Breakers UX | F‑C‑25 | FE/PM | `degrade_route` | openapi:`/breakers/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-25-*.json` |
| VWAP/TWAP Compare | F‑C‑26 | PM/DEC | `oracle_divergence_watch` | openapi:`/twap-vwap/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-26-*.json` |
| Reserve Bands | F‑C‑27 | PM/RSK | `reserve_breach_watch` | openapi:`/reserves/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-27-*.json` |
| Quote TTL Matrix | F‑C‑28 | DEC/PM | `ttl_matrix_guard` | openapi:`/quotes/ttl-matrix` • schema:`events.v1.json` • evidence:`evidence/feat-F-C-28-*.json` |

# 4) Decisão & Aceitação (D)
| Clássico | Feature ID — Nome | Owner | Hooks A110 | Links |
|---|---|---|---|---|
| Motor de decisão | F‑D‑01 — Decision Core v1 | DEC/SRE | `decision.latency>0.8s•5m->degrade_route` | openapi:`/decision/quote` • schema:`route.plan.v1.json` • evidence:`evidence/feat-F-D-01-*.json` |
| DSL de decisão | F‑D‑02 | DEC/PM | `policy_audit` | openapi:`/decision/policy/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-02-*.json` |
| APR & custo total | F‑D‑03 | DEC/PM | `basis_breach_watch` | openapi:`/apr/*` • schema:`statement.v1.json` • evidence:`evidence/feat-F-D-03-*.json` |
| Intercreditor | F‑D‑04 | RSK/PM | `covenant_breach` | openapi:`/ic-sc/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-04-*.json` |
| Evidence ledger | F‑D‑05 | DEC/SEC | `audit` | openapi:`/evidence/*` • schema:`price.evidence.v1.json` • evidence:`evidence/feat-F-D-05-*.json` |
| Trade‑off sliders | F‑D‑06 | PM/FE | `web.inp_regression` | openapi:`/decision/ui/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-06-*.json` |
| Disputas & TTR | F‑D‑07 | OPS/PM | `ttr_guard` | openapi:`/disputes/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-07-*.json` |
| Multi‑LP routing | F‑D‑08 | DEC/SRE | `exclude_venue` | openapi:`/routing/*` • schema:`route.plan.v1.json` • evidence:`evidence/feat-F-D-08-*.json` |
| Quote staleness | F‑D‑09 | DEC/PM | `staleness_guard` | openapi:`/quotes/staleness` • schema:`events.v1.json` • evidence:`evidence/feat-F-D-09-*.json` |
| APR sim vs real | F‑D‑10 | DEC/PM | `apr_mismatch_watch` | openapi:`/apr/compare` • schema:`statement.v1.json` • evidence:`evidence/feat-F-D-10-*.json` |
| Versioning & rollback | F‑D‑11 | DEC/PLAT | `policy_version_guard` | openapi:`/decision/versions` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-11-*.json` |
| Audit Trail | F‑D‑12 | SEC/DEC | `audit` | openapi:`/audit/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-12-*.json` |
| Hedging What‑If | F‑D‑13 | PM/RSK | `exposure_limit_guard` | openapi:`/hedge/whatif` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-13-*.json` |
| Guardrails reg. | F‑D‑14 | SEC/RSK | `reg_guard_live` | openapi:`/reg/guardrails` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-14-*.json` |
| Covenant templates | F‑D‑15 | RSK/PM | `covenant_breach` | openapi:`/covenants/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-15-*.json` |
| Badges SLA/Policy | F‑D‑16 | PM/OPS | `slo_burn_freeze` | openapi:`/badges/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-16-*.json` |
| Shadow/AB | F‑D‑17 | DEC/ML | `ab.srm_fail•run->pause+audit` | openapi:`/ab/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-D-17-*.json` |
| Acceptance timeout | F‑D‑18 | DEC/PM | `acceptance_timeout_guard` | openapi:`/decision/accept/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-18-*.json` |
| Retry budget | F‑D‑19 | PLAT/SRE | `retry_budget_exhausted` | openapi:`/retries/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-19-*.json` |
| Side‑by‑Side | F‑D‑20 | PM/FE | `web.inp_regression` | openapi:`/compare/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-20-*.json` |
| Impact disclosure | F‑D‑21 | PM/RSK | `policy_audit` | openapi:`/disclosure/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-D-21-*.json` |
| Reg Guardrails Live | F‑D‑22 | SEC/RSK | `reg_guard_live` | openapi:`/reg/live` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-22-*.json` |
| Quorum visualizer | F‑D‑23 | PM/DEC | `quorum_drop_watch` | openapi:`/quorum/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-D-23-*.json` |
| Policy Shadow Diff | F‑D‑24 | DEC/PLAT | `policy_diff_guard` | openapi:`/policy/diff` • schema:`audit.v1.json` • evidence:`evidence/feat-F-D-24-*.json` |

# 5) Formalização & Liquidação (E)
| Clássico | Feature ID — Nome | Owner | Hooks A110 | Links |
|---|---|---|---|---|
| IC‑SC | F‑E‑01 — IC‑SC | RSK/PM | `contract_break->rollback+waiver_timebox` | openapi:`/ic-sc/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-E-01-*.json` |
| Payment Agency | F‑E‑02 | INT/OPS | `settlement.miss_pct>0.02%•1d->reconcile+halt` | openapi:`/payments/split` • schema:`payment.v1.json` • evidence:`evidence/feat-F-E-02-*.json` |
| TaxCalc | F‑E‑03 | PM/DEC | `contract_break` | openapi:`/tax/indicative` • schema:`statement.v1.json` • evidence:`evidence/feat-F-E-03-*.json` |
| Waterfall Composer/Validator | F‑E‑04 | INT/RSK | `waterfall_invariant_guard` | openapi:`/waterfall/*` • schema:`waterfall.v1.json` • evidence:`evidence/feat-F-E-04-*.json` |
| Payment Idempotency | F‑E‑05 | INT/PLAT | `idempotency_conflict_watch` | openapi:`/payments/*` • schema:`payment.v1.json` • evidence:`evidence/feat-F-E-05-*.json` |
| Split Optimizer | F‑E‑06 | INT/PM | `fee_drag_regression_watch` | openapi:`/payments/split/opt` • schema:`payment.v1.json` • evidence:`evidence/feat-F-E-06-*.json` |
| Statement API | F‑E‑07 | INT/OPS | `statement_consistency_watch` | openapi:`/statements/*` • schema:`statement.v1.json` • evidence:`evidence/feat-F-E-07-*.json` |
| Chargeback | F‑E‑08 | OPS/PM | `chargeback_sla_guard` | openapi:`/chargeback/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-E-08-*.json` |
| Escrow Recon | F‑E‑09 | OPS/INT | `reconcile_guard` | openapi:`/escrow/reconcile` • schema:`statement.v1.json` • evidence:`evidence/feat-F-E-09-*.json` |
| CLS Cutoff Guard | F‑E‑10 | Treasury/RSK | `cls_payin_cutoff_watch` | openapi:`/cutoff/cls` • schema:`audit.v1.json` • evidence:`evidence/feat-F-E-10-*.json` |
| Counterparty DD | F‑E‑11 | RSK/SEC | `dd_violation_guard` | openapi:`/counterparty/dd` • schema:`audit.v1.json` • evidence:`evidence/feat-F-E-11-*.json` |
| Settlement Alerts & MTTR | F‑E‑12 | OPS/SRE | `mttr_guard` | openapi:`/settlement/alerts` • schema:`events.v1.json` • evidence:`evidence/feat-F-E-12-*.json` |
| Fees Policy & Timelock | F‑E‑13 | PM/RSK | `timelock_breach_guard` | openapi:`/fees/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-E-13-*.json` |
| Legal Doc Diff | F‑E‑14 | PM/SEC | `legal_diff_guard` | openapi:`/legal/diff` • schema:`audit.v1.json` • evidence:`evidence/feat-F-E-14-*.json` |
| Webhooks Idempotent | F‑E‑15 | INT/PLAT | `idempotency_conflict_watch` | openapi:`/webhooks/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-E-15-*.json` |
| Payment Event Bus | F‑E‑16 | INT/PLAT | `event_bus_health_watch` | openapi:`/payments/events/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-E-16-*.json` |
| Recon Rules Engine | F‑E‑17 | OPS/DATA | `reconcile_guard` | openapi:`/recon/rules` • schema:`statement.v1.json` • evidence:`evidence/feat-F-E-17-*.json` |
| Beneficiary Registry | F‑E‑18 | SEC/INT | `kyc_guard` | openapi:`/beneficiaries/*` • schema:`account.v1.json` • evidence:`evidence/feat-F-E-18-*.json` |
| SLA/Penalties Engine | F‑E‑19 | OPS/PM | `slo_burn_freeze` | openapi:`/sla/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-E-19-*.json` |
| Exit Plan Runbook | F‑E‑20 | OPS/SRE | `drill_guard` | openapi:`/runbooks/exit` • schema:`audit.v1.json` • evidence:`evidence/feat-F-E-20-*.json` |

# 6) Pós‑Trade & Governança (F)
| Clássico | Feature ID — Nome | Owner | Hooks A110 | Links |
|---|---|---|---|---|
| Ledger & Recon | F‑F‑01 — Ledger & Reconciliação | OPS/DATA | `reconcile_guard` | openapi:`/ledger/*` • schema:`statement.v1.json` • evidence:`evidence/feat-F-F-01-*.json` |
| Observabilidade & SLO | F‑F‑02 | SRE/OPS | `slo_burn_freeze` | openapi:`/obs/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-02-*.json` |
| A/B + SRM + Drift | F‑F‑03 | ML/PM | `ab.srm_fail•run->pause+audit`; `model.psi>0.2•24h->rollback_model` | openapi:`/ab/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-03-*.json` |
| NPL/Open Auction | F‑F‑04 | PM/SRE | `halt_auction` | openapi:`/auction/open` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-04-*.json` |
| Default Orchestrator | F‑F‑05 | RSK/OPS | `default_orchestration_guard` | openapi:`/defaults/*` • schema:`contract.v1.json` • evidence:`evidence/feat-F-F-05-*.json` |
| Privacy Ledger & DPIA | F‑F‑06 | SEC/PM | `privacy_budget>1.5x•1h->freeze` | openapi:`/privacy/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-F-06-*.json` |
| DR Drill & Tabletop | F‑F‑07 | SRE/OPS | `drill_guard` | openapi:`/dr/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-F-07-*.json` |
| Anti‑Stacking Guard | F‑F‑08 | RSK/PM | `concentration_guard` | openapi:`/stacking/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-08-*.json` |
| Evidence JSON Linter | F‑F‑09 | PLAT/SEC | `evidence_null_guard` | openapi:`/evidence/lint` • schema:`evidence.v1.json` • evidence:`evidence/feat-F-F-09-*.json` |
| Golden Files Catalog | F‑F‑10 | PLAT/OPS | `golden_file_regression_watch` | openapi:`/golden/*` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-10-*.json` |
| SRM Alerts | F‑F‑11 | ML/SRE | `ab.srm_fail•run->pause+audit` | openapi:`/ab/alerts` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-11-*.json` |
| Model Rollback Kit | F‑F‑12 | ML/SRE | `model.psi>0.2•24h->rollback_model` | openapi:`/model/rollback` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-12-*.json` |
| Audit Exports | F‑F‑13 | SEC/OPS | `audit` | openapi:`/audit/export` • schema:`audit.v1.json` • evidence:`evidence/feat-F-F-13-*.json` |
| Status Page + SLA | F‑F‑14 | SRE/OPS | `slo_burn_freeze` | openapi:`/status/*` • schema:`audit.v1.json` • evidence:`evidence/feat-F-F-14-*.json` |
| Concentration Heatmap | F‑F‑15 | RSK/DATA | `concentration_guard` | openapi:`/risk/heatmap` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-15-*.json` |
| Anti‑Stacking Scenarios | F‑F‑16 | RSK/PM | `concentration_guard` | openapi:`/stacking/scenarios` • schema:`events.v1.json` • evidence:`evidence/feat-F-F-16-*.json` |

---

# 7) Busca inversa (ID → Clássico)
> Use a busca do editor por `F-` para localizar o ID e ler a coluna “Clássico”. Exemplos:  
> `F‑A‑11` → Login (com MFA) • Sessão  
> `F‑B‑04` → Idempotency & Retries  
> `F‑D‑01` → Motor de decisão  
> `F‑E‑02` → Agência de Pagamentos  

---

# 8) Próximos passos
- Adicionar **links reais** para cada rota no `openapi.yaml` e para cada arquivo em `schemas/*.json` no repositório.  
- Marcar **Owner principal** por card (exato squad) e incluir **hook_id** referenciando `hooks.yaml`.  
- Opcional: filtros de **Now/Next/Later** e SLA de **DoR/DoD** por card.

