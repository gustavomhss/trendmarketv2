---
file: 04-Hooks-Policies-e-Runbooks.md
version: v1.1 (A1 KB — Deepdive Ilustres)
date: 2025-09-09
author: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: hooks-canonical
---

# 04) Hooks, Policies & Runbooks — A1 (v1.1 — Padrão Ouro)
> **Propósito:** tornar **automático, auditável e reversível** o controle operacional do A1 (PM, Oráculos, FX) usando **watchers → hooks** (A110), **políticas com histerese** e **runbooks P1/P2**. *Sem hook para métrica crítica ⇒ sem release.* Esta versão inclui **cobertura 100% dos watchers must‑have**, **ladder de degradação L1→L4**, **simulador/dry‑run**, **ChatOps**, e **evidence** para promoção.

---

## 0) Readiness & Handshake
- **Fonte canônica**: `brief_context.yaml` (Arquivo 01) carregado e **STABLE**.  
- **Watchers must‑have ON**: todos com owner e hook (ver §2).  
- **Contratos (Arq. 03)** e **Domínio (Arq. 02)** validados.  
- **Gates**: `hooks_a110==READY` • `schema_breaking==0` • `contract_tests==PASS` • `evidence.json` anexado.

**Checklist (antes do deploy):**
```yaml
pre_deploy:
  - check: watchers_online
  - check: hooks_yaml_lint
  - check: owners_present
  - check: rollback_defined
  - check: runbooks_linked
  - check: dry_run_passed
```

---

## 1) Gramática A110 (DSL) — v2
```yaml
hook_grammar:
  rule: "metric@window -> action[, action...]"
  window_ops: ["m","h","d"]     # minutos, horas, dias
  comparators: [">","<","==","!=",">=","<="]
  actions:
    catalog: [
      pause_market, switch_to_twap_failover, ban_source_temp, recalc_quorum,
      prefer_low_latency, degradar_para_pack_lite, alternate_venue,
      block_release, rollback_FE, throttle, notify
    ]
  fields:
    id: "id único"
    when: "condição (ex.: oracle.staleness_ms>30000•5m)"
    then: "ações (1..N)"
    owner: "A1|A2|A3|A4|A5"
    rollback: "yes|manual|custom:<id>"
    severity: "P1|P2"
    notes: "contexto"
  semantics:
    - "condições com • agregam no tempo (p.ex. p95>limiar por 5m)"
    - "ações executam em ordem; falha parcial gera rollback"
    - "histerese via policies.clear_when"
```

**Modo `dry_run`** (shadow): avalia `when`/`then` e loga ações **sem executar**; obrigatório em staging e em produção quando mudarmos limiares.

---

## 2) Cobertura Watchers → Hooks → Runbooks (100%)
> **Meta:** todo watcher must‑have (Arq. 01 §6) mapeado para ≥1 hook e ≥1 runbook.

| Watcher | Hook(s) | Runbook |
|---|---|---|
| `oracle_divergence_watch` | `a1_oracle_divergence_guard` | §4.1 (P1 Staleness/Divergência) |
| `cdc_lag_watch` | `a2_cdc_lag_guard` | §4.5 (P1 Drift/Lag CDC) |
| `schema_registry_drift_watch` | `a2_schema_drift_guard` | §4.5 |
| `api_breaking_change_watch` | `a3_api_breaking_guard` | §4.7 (P1 API Breaking) |
| `web_cwv_regression_watch` | `a3_web_cwv_guard` | §4.8 (P2 Web Regressão CWV) |
| `oracle_staleness_watch`* | `a1_oracle_staleness_guard` | §4.1 |
| `slo_budget_breach_watch` | `a5_slo_burn_guard` | §4.9 (P1 Burn Rate) |
| `capacity_headroom_watch` | `a5_capacity_headroom_guard` | §4.9 |
| `image_vuln_regression_watch` | `a5_image_vuln_guard` | §4.10 (P1 Supply Chain) |
| `idp_keys_rotation_watch` | `a5_idp_keys_rotation_guard` | §4.10 |
| `model_drift_watch` | `a4_model_drift_guard` | §4.6 (P1 Model Drift) |
| `ab_srm_watch` | `a4_ab_srm_guard` | §4.6 |
| `auction_invariant_breach_watch` | `a1_auction_invariant_guard` | §4.2 (P1 Invariantes PM) |
| `cls_payin_cutoff_watch` | `a1_cls_cutoff_guard` | §4.4 (P1 CLS Miss) |

\* `oracle_staleness_watch` está implícito em 01/02; explicitamos aqui.

---

## 3) Catálogo de Hooks (A110) — v1.1
```yaml
hooks:
  - id: a1_oracle_staleness_guard
    when: "oracle.staleness_ms>30000•5m"
    then: ["switch_to_twap_failover","notify=A1"]
    owner: A1
    rollback: yes
    severity: P1
    notes: "ativa TWAP(K) e rebaixa peso de fontes lentas"

  - id: a1_oracle_divergence_guard
    when: "oracle.divergence_eps>EPS_LIMIT•10m"
    then: ["ban_source_temp","recalc_quorum","notify=A1"]
    owner: A1
    rollback: yes
    severity: P1

  - id: a1_fx_router_latency_guard
    when: "fx.route_latency.p95>1500•5m"
    then: ["degradar_para_pack_lite","prefer_low_latency","alternate_venue","notify=A1"]
    owner: A1
    rollback: yes
    severity: P2

  - id: a1_auction_invariant_guard
    when: "pm.auction_invariant_breach>0•1m"
    then: ["pause_market","block_release","notify=A1"]
    owner: A1
    rollback: manual
    severity: P1

  - id: a1_cip_delta_guard
    when: "fx.cip_delta_eps>EPS_CIP•10m"
    then: ["degradar_para_pack_lite","alternate_venue","notify=A1"]
    owner: A1
    rollback: yes
    severity: P2

  - id: a2_cdc_lag_guard
    when: "cdc.lag_p95_s>120•15m"
    then: ["block_release","notify=A2"]
    owner: A2
    rollback: manual
    severity: P1

  - id: a2_schema_drift_guard
    when: "schema_registry.drift==INCOMPATIBLE•1m"
    then: ["block_release","notify=A2"]
    owner: A2
    rollback: manual
    severity: P1

  - id: a3_api_breaking_guard
    when: "api.breaking_change_detected==true•1m"
    then: ["block_release","rollback_FE","notify=A3"]
    owner: A3
    rollback: custom:fe_rollback
    severity: P1

  - id: a3_web_cwv_guard
    when: "web.inp_p75_ms>200•30m"
    then: ["rollback_FE","notify=A3"]
    owner: A3
    rollback: yes
    severity: P2

  - id: a4_model_drift_guard
    when: "ml.psi>0.2•30m OR ml.ks>0.1•30m"
    then: ["pause_experiment","notify=A4"]
    owner: A4
    rollback: yes
    severity: P1

  - id: a4_ab_srm_guard
    when: "ab.srm!=OK•10m"
    then: ["pause_experiment","notify=A4"]
    owner: A4
    rollback: yes
    severity: P1

  - id: a5_slo_burn_guard
    when: "slo.error_budget.burn>1.0•30m"
    then: ["throttle","notify=A5"]
    owner: A5
    rollback: yes
    severity: P1

  - id: a5_capacity_headroom_guard
    when: "infra.capacity_headroom<20%•10m"
    then: ["throttle","notify=A5"]
    owner: A5
    rollback: yes
    severity: P2

  - id: a5_image_vuln_guard
    when: "supply_chain.high_vulns>0•1m"
    then: ["block_release","notify=A5"]
    owner: A5
    rollback: manual
    severity: P1

  - id: a5_idp_keys_rotation_guard
    when: "idp.keys.age_days>90•1d"
    then: ["block_release","notify=A5"]
    owner: A5
    rollback: manual
    severity: P1

  - id: a1_cls_cutoff_guard
    when: "fx.cls_payin_miss>0•1d"
    then: ["pause_market","notify=A1"]
    owner: A1
    rollback: manual
    severity: P1
```

---

## 4) Policies com Histerese — Ladder L1→L4
> **Objetivo:** degradar **gradualmente** com reversão automática quando as métricas normalizarem.
```yaml
policies:
  - id: pack_lite_L1
    when: "fx.route_latency.p95>1500•5m"
    then: ["prefer_low_latency","reduce_venues","reduce_timeout=500ms"]
    clear_when: "fx.route_latency.p95<1200•10m"
    owner: A1
  - id: pack_lite_L2
    when: "fx.route_latency.p95>1700•10m"
    then: ["alternate_venue","reduce_timeout=300ms"]
    clear_when: "fx.route_latency.p95<1400•15m"
    owner: A1
  - id: pack_lite_L3
    when: "fx.route_latency.p95>2000•10m"
    then: ["alternate_venue","degradar_para_pack_lite"]
    clear_when: "fx.route_latency.p95<1600•20m"
    owner: A1
  - id: pack_lite_L4
    when: "fx.route_latency.p95>2500•10m"
    then: ["pause_market"]
    clear_when: "fx.route_latency.p95<1800•30m"
    owner: A1

  - id: twap_failover
    when: "oracle.staleness_ms>30000•5m"
    then: ["switch_to_twap_failover","quorum_reweight"]
    clear_when: "oracle.staleness_ms<20000•10m"
    owner: A1

  - id: pause_market
    when: "pm.auction_invariant_breach>0•1m"
    then: ["pause_market","open_postmortem"]
    clear_when: "pm.auction_invariant_breach==0•30m"
    owner: A1

  - id: block_release
    when: "schema_registry.drift==INCOMPATIBLE•1m OR api.breaking_change_detected==true•1m"
    then: ["block_release","notify=Owners"]
    clear_when: "drift==COMPATIBLE AND api.breaking_change_detected==false•30m"
    owner: A2
```

---

## 5) Runbooks P1/P2 — passo‑a‑passo executável
> **Formato padrão:** Detectar → Triagem → Mitigar → Verificar → Comunicar → Fechar/Postmortem. Sempre anexar **evidence**.

### 5.1 P1 — *Oracle Staleness/Divergência*
**Detectar**: `oracle.staleness_ms.p95>30000•5m` **OU** `oracle.divergence_eps>EPS_LIMIT•10m`.  
**Triagem**: identificar fonte lenta (uptime/recency), checar TAU/K e quorum.  
**Mitigar**: hooks `a1_oracle_staleness_guard`/`a1_oracle_divergence_guard`.  
**Verificar**: staleness <20s por 10m; divergência ε normalizada.  
**Comunicar**: `#ops-a1` + incidente P1.  
**Fechar**: RCA (5 porquês), PR com ajuste TAU/K.

### 5.2 P1 — *Auction Invariant Breach*
**Detectar**: `pm.auction_invariant_breach>0•1m`.  
**Triagem**: dump do book/seed; conferir determinismo.  
**Mitigar**: `pause_market` + `block_release`.  
**Verificar**: invariantes=0 por 30m.  
**Comunicar**: statuspage interna.  
**Fechar**: ADR de correção + property‑tests extras.

### 5.3 P2 — Latência de Rota FX
**Detectar**: `fx.route_latency.p95>1500•5m`.  
**Triagem**: venue outlier (lat/slip/up) e rede.  
**Mitigar**: ladder `pack_lite_L1→L4` + `alternate_venue`.  
**Verificar**: p95<1200 por 10m.  
**Fechar**: ajustar pesos α/β/γ.

### 5.4 P2 — CIP Desancorado
**Detectar**: `fx.cip_delta_eps>EPS_CIP•10m`.  
**Triagem**: checar day‑count/tenor; NDF.  
**Mitigar**: `a1_cip_delta_guard`.  
**Verificar**: Δ≤ε por 15m.  
**Fechar**: recalibrar ε por par/tenor.

### 5.5 P1 — Drift/Lag de CDC
**Detectar**: `cdc.lag_p95_s>120•15m` **ou** `schema_registry.drift==INCOMPATIBLE`.  
**Mitigar**: `block_release`.  
**Verificar**: consumidores críticos (A3/A2).  
**Fechar**: changelog/ADR.

### 5.6 P1 — Model Drift / SRM inválido
**Detectar**: `ml.psi>0.2`/`ml.ks>0.1` **ou** `ab.srm!=OK`.  
**Mitigar**: `pause_experiment`.  
**Verificar**: telemetria/contramedidas.  
**Fechar**: recalibração/features.

### 5.7 P1 — CLS Pay‑in Miss
**Detectar**: `fx.cls_payin_miss>0•1d`.  
**Triagem**: calendário/feriado; janela local.  
**Mitigar**: `pause_market`.  
**Verificar**: normalização no próximo cutoff.  
**Fechar**: ajustar tabela CLS (Arq. 01).

### 5.8 P1 — Supply Chain / Keys
**Detectar**: `supply_chain.high_vulns>0` ou `idp.keys.age_days>90`.  
**Mitigar**: `block_release`.  
**Verificar**: SBOM/rotação.  
**Fechar**: pipeline verde.

### 5.9 P1/P2 — Burn Rate / Headroom
**Detectar**: `slo.error_budget.burn>1.0` **ou** `infra.capacity_headroom<20%`.  
**Mitigar**: `throttle`.  
**Verificar**: headroom>30%.  
**Fechar**: capacity plan.

### 5.10 P1 — API Breaking / CWV Regression
**Detectar**: `api.breaking_change_detected==true` / `web.inp_p75_ms>200•30m`.  
**Mitigar**: `block_release` / `rollback_FE`.  
**Verificar**: lint + métricas CWV.  
**Fechar**: correções publish.

---

## 6) Simulador, Testes e Dry‑Run
### 6.1 Simulador de Hooks (cenários)
```yaml
simulations:
  - name: oracle_staleness_spike
    inputs: { oracle.staleness_ms: [10000, 50000, 60000, 15000] }
    expect:  [ no_action, a1_oracle_staleness_guard, a1_oracle_staleness_guard, clear ]
  - name: fx_latency_surge
    inputs: { fx.route_latency.p95: [1200, 1800, 2100, 2600] }
    expect:  [ no_action, L1, L2, L3_or_L4 ]
```

### 6.2 Testes (CI)
```bash
make hooks-lint             # valida sintaxe e owners/rollback
make hooks-dry-run          # executa simulações sem efeitos colaterais
make hooks-coverage         # verifica cobertura watchers→hooks
```

### 6.3 Shadow Mode em Produção
- Ative `hooks.shadow=true` por 24h antes de efetivar limiares novos.  
- Compare `fired_shadow` vs `fired_live` nos dashboards.

---

## 7) Observabilidade, Alertas & Noise‑Budget
- **Baggage**: `market_id`, `region`, `seed_id` (PM); `pair`, `tenor`, `route_id` (FX).  
- **SLIs principais**: `oracle.staleness_ms.p95`, `oracle.divergence_eps`, `pm.clearing_latency_ms`, `fx.route_latency.p95`, `fx.cip_delta_eps`.  
- **Alertas**: use agregações temporais (`•`) para evitar flaps; `mute_window` durante manutenções.  
- **Noise‑budget**: ≤2 alertas/hora por domínio em período estável; acima disso, revisar thresholds.

---

## 8) Segurança, Mudança & Governança
- **RBAC** para alterar hooks/policies: somente A1 lead/A5 SRE.  
- **Approvals**: 2‑eyes para mudanças P1.  
- **Assinaturas**: commit assinado + checksum do YAML.  
- **Drift**: `hooks_drift_watch` (interno) alerta quando produção≠git.  
- **Rollback**: sempre definido; `custom:<id>` se depender de FE.

---

## 9) Drills & Auditoria Contínua
- **GameDays** trimestrais: staleness/divergência/rota com cenários do simulador.  
- **Table‑top CLS** mensal.  
- **Chaos‑lite** semanal em 1 feed/venue (latência artificial).  
- **Postmortems** sem culpa; ações com owners e prazos.

**Evidence mínima (por release):**
```json
{
  "hooks_exercised": ["a1_oracle_staleness_guard","a1_fx_router_latency_guard"],
  "watchers": {"online": true},
  "rollback_drill": {"date": "2025-09-09", "result": "pass"}
}
```

---

## 10) ChatOps, Templates & Comandos
```yaml
chatops_templates:
  p1_open:   "[P1][A1] ${incident} — owner=${owner} bridge=${link} ETA=${eta}"
  p1_update: "[P1][A1][${min}m] mitigando=${action} métricas=${metrics}"
  p_close:   "[Px][A1] incidente fechado — RCA=${doc}"
commands:
  - "/a1 hooks status"
  - "/a1 hooks dry-run scenario=oracle_staleness_spike"
  - "/a1 pause market=${market_id}"
```

---

## 11) Estrutura de Repositório & Make Targets
```text
hooks/
  a1.yaml                # este catálogo
  simulations.yaml       # §6.1
runbooks/
  a1_staleness.md        # §5.1
  a1_invariants.md       # §5.2
  a1_fx_latency.md       # §5.3
  a1_cip_delta.md        # §5.4
  a1_cdc_drift.md        # §5.5
  a1_model_drift.md      # §5.6
  a1_cls_miss.md         # §5.7
  a1_supply_keys.md      # §5.8
scripts/
  hooks_lint.js
  hooks_dry_run.js
Makefile
```

**Make targets**
```makefile
hooks-lint:       node scripts/hooks_lint.js hooks/a1.yaml
hooks-dry-run:    node scripts/hooks_dry_run.js hooks/simulations.yaml
hooks-coverage:   node scripts/hooks_coverage.js hooks/a1.yaml
```

---

## 12) Go/No‑Go — Gates Objetivos
- `hooks_a110==READY` (lint + owners + rollback + coverage 100%).  
- `dry_run_passed==true` (simulações).  
- `evidence.json` anexado (NSM p95, staleness p95, route p95).  
- `statusboards` atualizados (Reliability, Oracles/FX).  
- **No‑Go**: watcher crítico sem owner; métrica crítica sem hook; `breaking!=0` (Arq. 03); violação de privacidade.

---

## 13) Artefatos & Onde Encontrar
- **Hooks/Policies YAML:** `hooks/a1.yaml` (este catálogo).  
- **Runbooks:** `runbooks/a1/*.md` (derivados das seções 5.x).  
- **Dashboards & SLOs:** ver Arquivo 05.  
- **Contratos & OpenAPI:** ver Arquivo 03.  
- **Domínio (PM/Oráculos/FX):** ver Arquivo 02.  
- **Segurança/Privacidade/On‑chain:** ver Arquivo 06.

---
**Fim (v1.1).** Hooks, policies e runbooks **padrão ouro**: cobertura total dos watchers, degradações com histerese, **dry‑run** e **simulações**; tudo auditável, reversível e pronto para produção sob o **NSM** (p95 ≤ 800 ms).

