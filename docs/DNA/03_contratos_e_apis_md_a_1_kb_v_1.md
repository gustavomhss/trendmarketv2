---
file: 03-Contratos-e-APIs.md
version: v1.1 (A1 KB — Deepdive Ilustres)
date: 2025-09-09
owner: Agente A1 (Markets & Oracles — PM + FX)
editors: Bezos × Jobs × Knuth × Perez (bar-raiser)
status: contracts-canonical
---

# 03) Contratos & APIs — Especificações Canônicas (v1.1)
> **Propósito:** definir **contratos de dados** (JSON Schema), **APIs** (OpenAPI), **compatibilidade SemVer**, **taxonomia de erros**, **idempotência**, **segurança**, **observabilidade** e **testes de contrato**. *Sem contrato compatível ⇒ sem release*.

---

## 0) Readiness & Handshake
- **Registry (A2)** configurado (`schema_registry_url`, token).  
- **Baseline:** `contracts@1.x` (somente **backward‑compatible**).  
- **Linters:** `make contract && make hooks-lint && redocly lint openapi/a1.yaml`.  
- **Gates de promoção:** `schema_breaking==0` • `openapi_lint==OK` • `contract_tests==PASS` • `hooks_a110==READY`.

---

## 1) Política de Versionamento & Compatibilidade (SemVer)
**Regras:**  
- **MAJOR (X.0.0)**: *breaking changes* (**PROIBIDO** promover).  
- **MINOR (1.Y.0)**: adições **opcionais** (novos campos `nullable=false` com `default`, novos eventos, novos enums **apenas adicionando valores**).  
- **PATCH (1.0.Z)**: correções não funcionais (descrições, exemplos, limites não restritivos).

**Breaking (exemplos):** remover campo `required`; mudar `type`; estreitar `minimum/maximum`; mudar `pattern`; tornar campo antes opcional em obrigatório; remover valor de enum.  
**Compat:** adicionar campo opcional; relaxar limites; adicionar valor de enum (consumidor deve ser tolerante).

**Matriz em produção:** aceita **[≥1.0.0, <2.0.0)**; *consumidores* devem ignorar **campos extras**.

---

## 2) `$defs` comuns (reuso)
> Para evitar repetição e garantir consistência entre schemas.
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://kb.a1/contracts/common.defs.json",
  "$defs": {
    "uuid": { "type": "string", "format": "uuid" },
    "semver1": { "type": "string", "pattern": "^1\\.\\d+\\.\\d+$" },
    "checksum": { "type": "string", "pattern": "^[A-Fa-f0-9]{64}$" },
    "ts": { "type": "string", "format": "date-time" },
    "region": { "type": "string", "minLength": 2, "maxLength": 32 },
    "asset": { "type": "string", "minLength": 2, "maxLength": 64 },
    "money": { "type": "number", "exclusiveMinimum": 0 },
    "qty": { "type": "number", "minimum": 0 },
    "pair": { "type": "string", "pattern": "^[A-Z]{3}\/[A-Z]{3}$" }
  }
}
```

---

## 3) JSON Schemas v1 (Draft 2020‑12)
> Todos com `additionalProperties:false`, exemplos **válido** e **inválido**, e **notas de invariantes** a validar em runtime (cross‑field).

### 3.1 `oracle_price_update.schema.json`
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://kb.a1/contracts/oracle_price_update.schema.json",
  "title": "oracle_price_update",
  "type": "object",
  "additionalProperties": false,
  "required": ["event_id","feed_id","region","asset","ts_event","ts_ingest","price","quality_score","schema_version","checksum"],
  "properties": {
    "event_id": { "$ref": "common.defs.json#/$defs/uuid" },
    "feed_id": { "type": "string", "minLength": 2, "maxLength": 64 },
    "region": { "$ref": "common.defs.json#/$defs/region" },
    "asset": { "$ref": "common.defs.json#/$defs/asset" },
    "ts_event": { "$ref": "common.defs.json#/$defs/ts" },
    "ts_ingest": { "$ref": "common.defs.json#/$defs/ts" },
    "price": { "$ref": "common.defs.json#/$defs/money" },
    "quality_score": { "type": "number", "minimum": 0, "maximum": 1 },
    "schema_version": { "$ref": "common.defs.json#/$defs/semver1" },
    "checksum": { "$ref": "common.defs.json#/$defs/checksum" },
    "sequence": { "type": "integer", "minimum": 0 }
  },
  "$comment": "Invariantes: ts_event<=ts_ingest; price>0; 0<=quality_score<=1; monotonicidade opcional por sequence."
}
```
**Válido**
```json
{"event_id":"5f9b7c2e-7d5e-4f5f-a7dc-7b0b2c8f9a10","feed_id":"provider_alpha","region":"BR","asset":"PM:ELEICAO2026","ts_event":"2025-09-09T11:31:00Z","ts_ingest":"2025-09-09T11:31:01Z","price":0.63,"quality_score":0.92,"schema_version":"1.0.0","checksum":"9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08","sequence":1024}
```
**Inválido** (price=0; `quality_score`>1; falta `asset`)
```json
{"event_id":"5f9b7c2e-7d5e-4f5f-a7dc-7b0b2c8f9a10","feed_id":"provider_alpha","region":"BR","ts_event":"2025-09-09T11:31:00Z","ts_ingest":"2025-09-09T11:31:01Z","price":0,"quality_score":1.2,"schema_version":"1.0.0","checksum":"abcd"}
```

### 3.2 `pm_bid_submitted.schema.json`
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://kb.a1/contracts/pm_bid_submitted.schema.json",
  "title": "pm_bid_submitted",
  "type": "object",
  "additionalProperties": false,
  "required": ["bid_id","market_id","participant_id","side","price","size","ts_client","ts_server","idempotency_key","schema_version"],
  "properties": {
    "bid_id": { "$ref": "common.defs.json#/$defs/uuid" },
    "market_id": { "type": "string", "minLength": 2, "maxLength": 64 },
    "participant_id": { "type": "string", "minLength": 2, "maxLength": 64 },
    "side": { "type": "string", "enum": ["buy","sell"] },
    "price": { "$ref": "common.defs.json#/$defs/money" },
    "size": { "$ref": "common.defs.json#/$defs/qty" },
    "ts_client": { "$ref": "common.defs.json#/$defs/ts" },
    "ts_server": { "$ref": "common.defs.json#/$defs/ts" },
    "idempotency_key": { "type": "string", "minLength": 8, "maxLength": 128 },
    "signature": { "type": "string", "minLength": 16 },
    "schema_version": { "$ref": "common.defs.json#/$defs/semver1" }
  },
  "$comment": "Invariantes: ts_client<=ts_server; side∈{buy,sell}; idempotency_key único por 24h."
}
```
**Válido**
```json
{"bid_id":"4a2d6b0c-1c2b-4f31-9ad7-2b7a9aee9f10","market_id":"PM:ELEICAO2026","participant_id":"0x9C7...AB","side":"buy","price":0.58,"size":1200,"ts_client":"2025-09-09T11:31:00Z","ts_server":"2025-09-09T11:31:00Z","idempotency_key":"c1c1a1e0-77ee-4404-9c7d-2e9f","schema_version":"1.0.0"}
```
**Inválido** (`side`=hold; `price`<0; `idempotency_key` curto)
```json
{"bid_id":"4a2d6b0c-1c2b-4f31-9ad7-2b7a9aee9f10","market_id":"PM:ELEICAO2026","participant_id":"0x9C7...AB","side":"hold","price":-1,"size":500,"ts_client":"2025-09-09T11:31:00Z","ts_server":"2025-09-09T11:31:01Z","idempotency_key":"key","schema_version":"1.0.0"}
```

### 3.3 `pm_clearing_result.schema.json`
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://kb.a1/contracts/pm_clearing_result.schema.json",
  "title": "pm_clearing_result",
  "type": "object",
  "additionalProperties": false,
  "required": ["clearing_id","market_id","ts_cleared","clearing_price","allocations","seed_id","invariants_ok","schema_version"],
  "properties": {
    "clearing_id": { "$ref": "common.defs.json#/$defs/uuid" },
    "market_id": { "type": "string", "minLength": 2, "maxLength": 64 },
    "ts_cleared": { "$ref": "common.defs.json#/$defs/ts" },
    "clearing_price": { "type": "number", "minimum": 0 },
    "allocations": {
      "type": "array", "minItems": 1, "items": {
        "type": "object", "additionalProperties": false,
        "required": ["bid_id","qty"],
        "properties": {
          "bid_id": { "$ref": "common.defs.json#/$defs/uuid" },
          "qty": { "$ref": "common.defs.json#/$defs/qty" }
        }
      }
    },
    "seed_id": { "type": "string", "minLength": 8, "maxLength": 64 },
    "invariants_ok": { "type": "boolean" },
    "audit_hash": { "$ref": "common.defs.json#/$defs/checksum" },
    "schema_version": { "$ref": "common.defs.json#/$defs/semver1" }
  },
  "$comment": "Invariantes: sum(alloc.qty)<=cap(K*); determinismo dado seed_id; clearing_price>=0."
}
```
**Válido**
```json
{"clearing_id":"c0bb2d7b-ae9f-4a00-9012-d6a8b7a3e001","market_id":"PM:ELEICAO2026","ts_cleared":"2025-09-09T11:31:02Z","clearing_price":0.61,"allocations":[{"bid_id":"4a2d6b0c-1c2b-4f31-9ad7-2b7a9aee9f10","qty":800},{"bid_id":"9f1a9f1a-2b2b-3c3c-4d4d-5e5e6f6f7a7a","qty":400}],"seed_id":"seed-2025-W37","invariants_ok":true,"audit_hash":"9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08","schema_version":"1.0.0"}
```
**Inválido** (allocations vazio; `clearing_price`<0)
```json
{"clearing_id":"c0bb2d7b-ae9f-4a00-9012-d6a8b7a3e001","market_id":"PM:ELEICAO2026","ts_cleared":"2025-09-09T11:31:02Z","clearing_price":-1,"allocations":[],"seed_id":"seed-2025-W37","invariants_ok":true,"schema_version":"1.0.0"}
```

### 3.4 `fx_quote.schema.json`
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://kb.a1/contracts/fx_quote.schema.json",
  "title": "fx_quote",
  "type": "object",
  "additionalProperties": false,
  "required": ["quote_id","pair","tenor","spot","forward","points","route_latency_ms","venue","cip_delta_eps","ts_quote","expires_at","schema_version"],
  "properties": {
    "quote_id": { "$ref": "common.defs.json#/$defs/uuid" },
    "pair": { "$ref": "common.defs.json#/$defs/pair" },
    "tenor": { "type": "string", "enum": ["SPOT","1W","1M","3M","6M","1Y"] },
    "spot": { "$ref": "common.defs.json#/$defs/money" },
    "forward": { "$ref": "common.defs.json#/$defs/money" },
    "points": { "type": "number" },
    "route_latency_ms": { "type": "integer", "minimum": 0 },
    "venue": { "type": "string", "minLength": 2, "maxLength": 64 },
    "cip_delta_eps": { "type": "number", "minimum": 0 },
    "ts_quote": { "$ref": "common.defs.json#/$defs/ts" },
    "expires_at": { "$ref": "common.defs.json#/$defs/ts" },
    "schema_version": { "$ref": "common.defs.json#/$defs/semver1" }
  },
  "$comment": "Invariantes: expires_at>ts_quote; |F_mkt−F_model|<=ε (runtime)."
}
```
**Válido**
```json
{"quote_id":"0a1b2c3d-4e5f-6071-8192-a3b4c5d6e7f8","pair":"USD/BRL","tenor":"SPOT","spot":5.21,"forward":5.25,"points":40,"route_latency_ms":980,"venue":"venue_x","cip_delta_eps":0.0007,"ts_quote":"2025-09-09T11:31:01Z","expires_at":"2025-09-09T11:31:06Z","schema_version":"1.0.0"}
```
**Inválido** (`pair` inválido; `expires_at`<`ts_quote`)
```json
{"quote_id":"0a1b2c3d-4e5f-6071-8192-a3b4c5d6e7f8","pair":"USDBRL","tenor":"SPOT","spot":5.21,"forward":5.25,"points":40,"route_latency_ms":1980,"venue":"venue_x","cip_delta_eps":0.002,"ts_quote":"2025-09-09T11:31:10Z","expires_at":"2025-09-09T11:31:06Z","schema_version":"1.0.0"}
```

---

## 4) OpenAPI (excertos) — Serviço A1
```yaml
openapi: 3.0.3
info:
  title: A1 — Markets & Oracles API
  version: 1.0.0
servers:
  - url: https://api.creditengine.local/a1
security:
  - mutualTLS: []
  - rbac: ["A1:write","A1:read"]
components:
  securitySchemes:
    mutualTLS:
      type: mutualTLS
    rbac:
      type: apiKey
      in: header
      name: X-Role
  headers:
    Idempotency-Key:
      schema: { type: string }
      description: Obrigatório nos POST idempotentes
    Retry-After:
      schema: { type: integer }
      description: Segundos até nova tentativa (429/503)
  schemas:
    Error:
      type: object
      additionalProperties: false
      required: [code, message]
      properties:
        code: { type: string, pattern: '^A1-[0-9]{4}$' }
        message: { type: string }
        details: { type: object }
        retry_after: { type: integer, minimum: 0 }
paths:
  /bids:
    post:
      summary: Submeter lance (PM)
      operationId: submitBid
      parameters:
        - in: header
          name: Idempotency-Key
          required: true
          schema: { type: string, minLength: 8 }
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: 'https://kb.a1/contracts/pm_bid_submitted.schema.json'
      responses:
        '202': { description: Aceito }
        '400': { $ref: '#/components/responses/A1-4001' }
        '409': { $ref: '#/components/responses/A1-4091' }
        '429': { $ref: '#/components/responses/A1-4290' }
        '503': { $ref: '#/components/responses/A1-5030' }
  /quotes/pm:
    get:
      summary: Obter cotação do PM
      parameters:
        - in: query
          name: market_id
          required: true
          schema: { type: string }
      responses:
        '200': { description: OK }
        '503': { $ref: '#/components/responses/A1-5030' }
  /quotes/fx:
    get:
      summary: Obter cotação FX
      parameters:
        - in: query
          name: pair
          required: true
          schema: { type: string, pattern: '^[A-Z]{3}/[A-Z]{3}$' }
        - in: query
          name: tenor
          required: true
          schema: { type: string, enum: [SPOT,1W,1M,3M,6M,1Y] }
      responses:
        '200': { description: OK }
        '429': { $ref: '#/components/responses/A1-4290' }
        '503': { $ref: '#/components/responses/A1-5030' }
components:
  responses:
    A1-4001:
      description: invalid_bid
      content:
        application/json:
          schema: { $ref: '#/components/schemas/Error' }
          examples:
            example:
              value: { code: 'A1-4001', message: 'invalid_bid', details: { field: 'price' } }
    A1-4091:
      description: duplicate_bid_id
      content:
        application/json:
          schema: { $ref: '#/components/schemas/Error' }
          examples:
            example:
              value: { code: 'A1-4091', message: 'duplicate_bid_id' }
    A1-4290:
      description: rate_limited — honrar header Retry-After
      headers:
        Retry-After:
          $ref: '#/components/headers/Retry-After'
      content:
        application/json:
          schema: { $ref: '#/components/schemas/Error' }
          examples:
            example:
              value: { code: 'A1-4290', message: 'rate_limited', retry_after: 5 }
    A1-5030:
      description: service_unavailable — tente depois
      content:
        application/json:
          schema: { $ref: '#/components/schemas/Error' }
          examples:
            example:
              value: { code: 'A1-5030', message: 'service_unavailable' }
```

---

## 5) Taxonomia de Erros & Headers (resumo)
| Código | HTTP | Significado | Ação do cliente |
|---|---:|---|---|
| **A1‑4001** | 400 | `invalid_bid` | Corrigir payload |
| **A1‑4091** | 409 | `duplicate_bid_id` | Não retry; novo `bid_id` |
| **A1‑4290** | 429 | `rate_limited` | Honrar `Retry-After` |
| **A1‑5030** | 503 | `service_unavailable` | Retry exponencial + *jitter* |

**Headers padrão:** `Idempotency-Key` (POST /bids), `Retry‑After` (429/503), `X-Trace-Id`, `X-Route-Id` (FX), `X-Seed-Id` (PM).

---

## 6) Testes de Contrato (CDC) — Consumidor & Produtor
**Consumidor (A3/FE, A2):**  
1) Importar **schemas v1**.  
2) Gerar *fixtures* válidos/ inválidos.  
3) Validar em CI (falha ⇒ **bloqueia deploy**).  

**Produtor (A1):**  
1) `make contract` (lint + validação).  
2) Publicar no **registry** (A2).  
3) Rodar **contract tests** com consumidores críticos (A3/A2).  
4) **Só promover** se todos passarem.

**Harness:**
```bash
ajv validate -s contracts/*.schema.json -d examples/*.json --strict=true
redocly lint openapi/a1.yaml
```

---

## 7) Integração com Registry & Drift (A2)
- **Registry**: registrar `id`, `semver`, `owner`, `checksum`, *deprecation date*.  
- **Drift Watch**: `schema_registry_drift_watch` bloqueia deploy com incompatibilidade.  
- **Change Log**: ADR para remoções; *waiver A106* (temporário) para exceções.

---

## 8) Segurança, Privacidade & Anti‑abuso
- **mTLS** obrigatório; **RBAC** por rota (`X-Role`).  
- **Rate limit**: token‑bucket (burst 50; rps 10) por `participant_id`.  
- **Idempotência**: `POST /bids` exige `Idempotency-Key`; rejeitar replays.  
- **Clock‑skew**: tolerância ≤ 3s; garantir `ts_client ≤ ts_server`.  
- **PII off‑chain**; **checksum SHA‑256**; logs pseudonimizados.  
- **SBOM** e `high_vulns=0` no gate de release.

---

## 9) Observabilidade & Traço
- **Baggage**: `market_id`, `region`, `seed_id` (PM); `pair`, `tenor`, `route_id` (FX).  
- **Métricas**: `api.rps`, `api.err_rate`, `api.p95`, `pm.clearing_latency_ms`, `fx.route_latency.p95`.  
- **Logs estruturados**: incluir `event_id|bid_id|quote_id`.

---

## 10) Promoção — Gates Objetivos (Go/No‑Go)
- `openapi_lint==OK`  
- `schema_breaking==0`  
- `contract_tests==PASS`  
- `hooks_a110==READY`  
- `evidence.json` anexado (NSM p95, staleness p95, route p95)

---

## 11) Artefatos & Onde Encontrar
- **Schemas (JSON):** `contracts/*.schema.json`  
- **Exemplos:** `examples/*.{valid,invalid}.json`  
- **OpenAPI:** `openapi/a1.yaml`  
- **Scripts:** `scripts/validate_contracts.js`, `make contract`, `make hooks-lint`  
- **Registry (A2):** `schema_registry_url` com token

---
**Fim (v1.1).** Contratos & APIs endurecidos pelo **Comitê de Ilustres**: prontos para **execução, auditoria e reversão** no A1. *Sem contrato compatível, sem release.*

