---
file: 06-Seguranca-Privacidade-e-OnChain.md
version: v1.1 (A1 KB — Deepdive Supremo)
date: 2025-09-09
author: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: security-canonical
---

# 06) Segurança, Privacidade & On‑Chain — A1 (v1.1 • Deepdive Supremo)
> **Propósito:** operacionalizar **segurança por padrão**, **privacidade por design** e **integridade auditável** com **evidências**. Esta versão inclui **políticas machine‑readable completas**, **checklists executáveis**, **evidence.security** e **âncoras on‑chain** com parâmetros práticos. *Sem segurança/privacidade compatível ⇒ sem release.*

---

## 0) Readiness & Handshake
- **Contexto**: `brief_context.yaml` (Arq. 01); horários/regiões (CLS; America/Bahia).  
- **Domínios & contratos**: Arq. 02 (PM/Oráculos/FX) e Arq. 03 (Schemas/OpenAPI).  
- **Hooks/Runbooks**: Arq. 04 (watchers de segurança ON).  
- **Observabilidade & Evidence**: Arq. 05.  

**Self‑check (YAML)**
```yaml
security_readiness:
  classification_policy_loaded: true
  rbac_in_place: true
  mtls_all_services: true
  secrets_vault: on
  kms_rotation_days: 90
  sbom_policy: enforced
  artifact_signing: cosign
  tz: America/Bahia
```

---

## 1) Threat Model & Fronteiras de Confiança (STRIDE + Abuse)
**Alvos críticos:** PM Core (clearing), Oráculos (feeds/qualidade), FX (router/CIP), CDC/Registry, APIs.  
**Abuse cases:** scraping agressivo, *quote stuffing*, *venue poisoning*, replay de bids, *MEV* em commits.

| Categoria | Risco | Mitigações chave |
|---|---|---|
| **S**poofing | Falsificação de feed/origem | mTLS, allowlist FQDN/IP, assinaturas de eventos, `quality_score` + quorum, chaves por conector |
| **T**ampering | Alteração de payload/lance | JSON Schema v1 (Arq. 03), checksum SHA‑256, EIP‑712 (opcional), hash‑chain de logs |
| **R**epudiation | Negar envio/ação | `Idempotency-Key`, `audit_log` imutável, carimbo de tempo (NTP), âncora on‑chain |
| **I**nformation Disclosure | Vazamento PII/token | Pseudonimização/FLE, mTLS, redaction de logs, DLP em CI/CD |
| **D**enial of Service | Flood/RPS/rota lenta | Token‑bucket, *breaker* (FX), quotas por venue, `throttle`/`pack_lite` |
| **E**levation of Privilege | Privilégios indevidos | RBAC mínimo, JIT access, MFA, *break‑glass* auditado |

**Trust boundaries:** Internet↔API GW; API↔A1; A1↔A2 (CDC/Registry); A1↔venues FX; A1↔Oráculos; A1↔On‑chain.

---

## 2) Classificação de Dados & Privacidade (LGPD/GDPR/CCPA)
### 2.1 Níveis & Políticas
```yaml
data_classification:
  levels:
    PUBLIC:    { retention_days: 3650, pii: false }
    INTERNAL:  { retention_days: 1095, pii: false }
    RESTRICTED:{ retention_days: 365,  pii: true }
    SENSITIVE: { retention_days: 180,  pii: true }
  defaults:
    logs: INTERNAL
    metrics: INTERNAL
    traces: INTERNAL
    participants: RESTRICTED
  dpo_contact: dpo@creditengine.local
```

### 2.2 Inventário de Dados (catálogo)
```yaml
data_inventory:
  - id: oracles_prices
    owner: A1
    level: INTERNAL
    fields: [event_id, feed_id, region, asset, ts_event, ts_ingest, price, quality_score]
    retention_days: 365
  - id: participants
    owner: Security
    level: RESTRICTED
    fields: [participant_id, email_hash]
    retention_days: 180
  - id: audit_logs
    owner: A5
    level: INTERNAL
    retention_days: 365
```

### 2.3 Retenção & DSR
- **Retenção padrão:** 12 meses telemetria; 180 dias PII.  
- **DSR** (Data Subject Request): remover/anonimizar dentro de 30 dias, registrar em **evidence.security**.

### 2.4 Pseudonimização & FLE
- PII sempre **pseudonimizada**; em repouso, **FLE** opcional com data‑keys por tabela/tenancy.  
- Catálogo de FLE em `security/fle_catalog.yaml` (exemplo §10).

---

## 3) Identidade, Acesso & Segredos (IAM)
### 3.1 RBAC — papéis mínimos
```yaml
rbac:
  roles:
    A1-runner:   ["A1:read","A1:write"]
    A2-registry: ["Contracts:publish","CDC:read"]
    A3-consumer: ["A1:read"]
    SRE:         ["Infra:manage","A1:ops"]
    Security:    ["Keys:manage","Evidence:read"]
  policies:
    least_privilege: true
    mfa_required: true
    session_max_hours: 8
    jit_access:
      - resource: prod-database-readonly
        ttl: 2h
      - resource: admin-console
        ttl: 1h
```

### 3.2 Segredos & Rotação
- **Vault** para segredos; envelope com **KMS (AES‑256)**.  
- **Rotação**: `idp.keys.age_days≤90` (hook `a5_idp_keys_rotation_guard`).  
- **Detecção**: *pre‑commit hooks* + CI (secret‑scanner).  
- **Break‑glass**: 2‑eyes, janela curta, trilha dedicada.

### 3.3 Contas de Serviço
- Service accounts por domínio; **OIDC federado** na CI; *workload identity* em runtime; **sem chaves hardcoded**.

---

## 4) Criptografia — Trânsito/Repouso/Campo
### 4.1 Em Trânsito
- **mTLS** em todos os hops (TLS≥1.2, PFS).  
- **HSTS** em endpoints públicos; pinning em feeds críticos.

### 4.2 Em Repouso
- Volumes/bancos criptografados; **backups** com chaves segregadas; **snapshots** com retenção por ambiente.

### 4.3 No Campo (FLE)
- Tabelas/colunas sensíveis com *data‑keys* distintas; rotação anual; *re‑wrap* em caso de compromisso.

---

## 5) Integridade, Não‑repúdio & Logs Imutáveis
### 5.1 Assinaturas & Checksums
- Eventos (`oracle_price_update`, `pm_clearing_result`, `fx_quote`) com `checksum` SHA‑256 e, quando ativado, **EIP‑712**.  
- `Idempotency-Key` obrigatório em `POST /bids` (Arq. 03).

### 5.2 Hash‑chain & Carimbo de Tempo
- `H(block_i) = H(block_{i-1} || event_i)` em *append‑only*; fonte de tempo NTP redundante.  
- Publicar `head` periódico (âncora on‑chain, §8.3).

---

## 6) Supply Chain & CI/CD Seguro
- **SBOM** (SPDX) obrigatório; gate `high_vulns==0`.  
- **SAST/DAST/Container scan**; registries *allowlisted*.  
- **Assinatura de imagens** (cosign) + **política de admissão** (OPA/Gatekeeper).  
- **Imagens** *distroless*, usuário não‑root, `seccomp`/`AppArmor`.

**Exemplo (Rego — admissão):**
```rego
package admission
allow {
  input.request.kind.kind == "Pod"
  input.request.object.spec.containers[_].securityContext.runAsNonRoot == true
  input.request.object.spec.containers[_].image.startswith("registry.local/creditengine/")
  input.request.object.metadata.annotations["cosign.sig"]
}
```

---

## 7) Observabilidade de Segurança & Detecção
- **Métricas**: `auth.fail_rate`, `rbac.denied`, `vault.errors`, `hooks_drift`, `image_vulns`.  
- **Traces**: `security_event` (span), `hook_fired`/`policy_applied`.  
- **Logs**: JSON‑lines com `event_id`, `actor`, `role`, `resource`, `action`, `result`.

**Alertas/Watchers** (Arq. 04): `image_vuln_regression_watch`, `idp_keys_rotation_watch`, `slo_budget_breach_watch`, `hooks_drift_watch` (interno).

---

## 8) On‑Chain — Assinaturas, Commit‑Reveal & Âncoras (opcional)
### 8.1 EIP‑712 (Assinatura)
```json
{
  "domain": {"name":"CreditEngine/PM","version":"1","chainId":1,"verifyingContract":"0x000…000"},
  "types": {"Bid":[
    {"name":"market_id","type":"bytes16"},
    {"name":"participant","type":"bytes20"},
    {"name":"side","type":"uint8"},
    {"name":"price","type":"uint256"},
    {"name":"size","type":"uint256"},
    {"name":"nonce","type":"uint256"}
  ]},
  "primaryType":"Bid"
}
```

### 8.2 Commit‑Reveal
```
Commit: hash = H(lance||salt||nonce) → janela → Reveal: lance+salt+nonce → validação → rejeitar fora da janela/duplicado.
```

### 8.3 Âncoras de Auditoria
- **Quando**: fechos de leilão relevantes, *post‑mortems*, *compliance*.  
- **O quê**: `audit_hash` de `pm_clearing_result` **ou** `hash‑chain head`.  
- **Rede**: pública (L1/L2) ou permissionada (custo/latência).  
- **Confirmações**: `confirmations=N` (parametrizável) e *reorg tolerance*.  
- **Provas**: guardar *proof‑of‑inclusion* no pacote do incidente/release.

---

## 9) Backup, DR & Continuidade
- **RTO/RPO** referência: 60m/15m (ajustar).  
- **Backups** diários + *point‑in‑time* para bancos críticos.  
- **Restores testados** trimestralmente (**evidência**).  
- **DR** multi‑AZ/região; *table‑top* semestral.

---

## 10) Políticas & Artefatos — Exemplos Completos
### 10.1 `security/rbac.yaml`
```yaml
version: 1
roles:
  - name: A1-runner
    grants: ["A1:read","A1:write"]
  - name: SRE
    grants: ["Infra:manage","A1:ops"]
  - name: Security
    grants: ["Keys:manage","Evidence:read"]
policies:
  least_privilege: true
  mfa_required: true
  session_max_hours: 8
  jit:
    resources:
      - id: prod-database-readonly
        ttl: 2h
      - id: admin-console
        ttl: 1h
approvals:
  p1_changes: ["A1-lead","Security-lead"]
```

### 10.2 `security/fle_catalog.yaml`
```yaml
version: 1
collections:
  participants:
    fields:
      email_hash: { fle: true, key: fle-key-participants-v1 }
      doc_id:     { fle: true, key: fle-key-participants-v1 }
  audit_logs:
    fields:
      actor:      { fle: false }
keys:
  - id: fle-key-participants-v1
    source: kms
    rotation_days: 365
```

### 10.3 `security/onchain.yaml`
```yaml
version: 1
signing:
  eip712:
    domain:
      name: CreditEngine/PM
      version: "1"
      chainId: 1
      verifyingContract: 0x0000000000000000000000000000000000000000
    typed:
      Bid:
        - { name: market_id,  type: bytes16 }
        - { name: participant, type: bytes20 }
        - { name: side,       type: uint8 }
        - { name: price,      type: uint256 }
        - { name: size,       type: uint256 }
        - { name: nonce,      type: uint256 }
anchors:
  enabled: true
  network: l2
  confirmations: 12
  cadence: daily
  payload: pm_clearing_result.audit_hash
```

### 10.4 `security/pipeline_policies.yaml`
```yaml
supply_chain:
  sbom_required: true
  high_vulns: 0
  image_signing: cosign
  admission_policy: opa/gatekeeper
  base_image: distroless
  run_as_non_root: true
```

---

## 11) Incidentes, Severidades & Runbooks (IR)
- **Severidades**: P1 (vazamento/assinatura inválida), P2 (rota FX lenta), P3 (alerta de postura).  
- **Watchers**: `image_vuln_regression_watch`, `idp_keys_rotation_watch`, `slo_budget_breach_watch`, `hooks_drift_watch`.  
- **Runbooks**: ver Arq. 04 §5 (Supply Chain/Keys, Burn/Headroom).  
- **Comunicação**: ChatOps (Arq. 04 §10).  
- **Reguladores**: notificar conforme jurisdição/prazo.

**Checklist P1 (executável)**
```yaml
p1_breach:
  - isolate_system: true
  - rotate_keys: true
  - revoke_tokens: true
  - snapshot_forensics: true
  - notify_ic_and_dpo: true
  - evidence_bundle: attach
```

---

## 12) Compliance — Mapeamento de Controles
| Padrão | Controles & Onde vivem |
|---|---|
| **SOC 2** | acesso/mudança/disponibilidade/confidencialidade/processamento — RBAC (§3), CI/CD (§6), DR (§9), Logs (§5), Evidence (§13) |
| **ISO/IEC 27001** | A.5 Políticas; A.8 Ativos; A.9 Acesso; A.10 Cripto; A.12 Operações; A.16 Incidentes — ver §§3–11 |
| **LGPD/GDPR** | Minimização, base legal, DSR, *privacy by design* — §§2, 5, 11 |

---

## 13) Evidence — Seção de Segurança
### 13.1 Esquema `evidence.security.json`
```json
{
  "$schema":"https://json-schema.org/draft/2020-12/schema",
  "title":"a1_evidence_security",
  "type":"object",
  "additionalProperties":false,
  "required":["release_id","timestamp","rbac","crypto","supply_chain","ir","anchors"],
  "properties":{
    "release_id": {"type":"string"},
    "timestamp":  {"type":"string","format":"date-time"},
    "rbac": {"type":"object","required":["mfa","jit","keys_rotation_days"],"properties":{
      "mfa": {"type":"boolean"},
      "jit": {"type":"boolean"},
      "keys_rotation_days": {"type":"integer"}
    }},
    "crypto": {"type":"object","required":["mtls","fle","checksum"],"properties":{
      "mtls": {"type":"boolean"},
      "fle": {"type":"boolean"},
      "checksum": {"type":"boolean"}
    }},
    "supply_chain": {"type":"object","required":["sbom","high_vulns","image_signed"],"properties":{
      "sbom": {"type":"boolean"},
      "high_vulns": {"type":"integer","maximum":0},
      "image_signed": {"type":"boolean"}
    }},
    "ir": {"type":"object","required":["drill_date","result"],"properties":{
      "drill_date": {"type":"string","format":"date"},
      "result": {"type":"string","enum":["pass","fail"]}
    }},
    "anchors": {"type":"object","required":["enabled","confirmations"],"properties":{
      "enabled": {"type":"boolean"},
      "confirmations": {"type":"integer","minimum":0}
    }}
  }
}
```

### 13.2 Exemplo (pré‑promoção)
```json
{
  "release_id": "a1-2025-09-09-rc2",
  "timestamp": "2025-09-09T16:12:00Z",
  "rbac": { "mfa": true, "jit": true, "keys_rotation_days": 60 },
  "crypto": { "mtls": true, "fle": true, "checksum": true },
  "supply_chain": { "sbom": true, "high_vulns": 0, "image_signed": true },
  "ir": { "drill_date": "2025-09-01", "result": "pass" },
  "anchors": { "enabled": true, "confirmations": 12 }
}
```

---

## 14) Go/No‑Go — Gates Objetivos (Segurança/Privacidade)
- `mtls_all_services==true` • `RBAC==least_privilege` • `keys_rotation_days<=90`  
- `high_vulns==0` • **SBOM anexado** • **images signed** (cosign)  
- `logs.redaction==ON` • `pii_catalog==UPDATED` • `retention_policies==ENFORCED`  
- **Evidence** inclui `evidence.security.json` **válido**  
- **No‑Go**: PII em logs; segredo exposto; drift entre `hooks/a1.yaml` e produção; ausência de DR test recente.

---

## 15) Artefatos & Referências Cruzadas
- **Políticas & RBAC**: `security/rbac.yaml`, `security/data_classification.yaml`  
- **Criptografia**: `security/kms_keys.yaml`, `security/fle_catalog.yaml`  
- **On‑chain**: `security/onchain.yaml`  
- **Supply chain**: `security/sbom/*.spdx`, `security/pipeline_policies.yaml`  
- **Incidentes/IR**: runbooks (Arq. 04 §5)  
- **Evidence**: `evidence.security.json` (este §13)

---
**Conclusão:** **padrão ouro** end‑to‑end — IAM mínimo, segredos com KMS, criptografia em todas as camadas, supply chain com SBOM/assinatura e *admission control*, privacidade por design, detecção e respostas operacionais, e **âncoras on‑chain** quando exigidas. Tudo **machine‑readable**, auditável e com **gates** claros. Pronto para produção. 

