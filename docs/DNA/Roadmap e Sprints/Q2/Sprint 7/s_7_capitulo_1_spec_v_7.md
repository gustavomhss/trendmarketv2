# Sprint Q2 — S7 (Stabilize)
## Capítulo 1 — Especificação & Entregáveis (Blueprint para o Codex)
Versão: v7.1 FINAL (2025-10-31)  
Owner: PO • Eng: Codex • ORR: SRE  
Escopo: somente Cap.1. Cap.2 (Gates) e Cap.3 (Filemap) virão após sua aprovação.
Changelog v7.1: micro‑ajustes finais aplicados — (1) **casing normativo** (currency UPPERCASE; unit/source lowercase); (2) **hash/bytes canônicos** (sem newline; sha256 **hex lowercase 64**); (3) **Base64 padrão com padding** e `domain_tag` **exato** `tm.s7.batch.v1\n`; (4) **EXIT 0 iff pós‑condições verdadeiras** para cada CLI; (5) **vetores negativos** de reprodutibilidade adicionados.

---

### 0) Normas de redação (RFC‑2119)
Termos **MUST/SHOULD/MAY** seguem RFC‑2119. Tudo que está marcado como **normativo** é obrigatório ao Codex.

---

### 1) North Star (uma frase)
Tornar **determinístico, verificável e auditável** o pipeline inicial do Oráculo (normalização → batch canônico → Merkle → assinatura/verify → log append‑only), pronto para destravar S8–S12.

---

### 2) Escopo, Dependências, Restrições
**Inclui:** normalização determinística (schema v1), `entries_hash`, raiz Merkle, assinatura/verify Ed25519, log **append‑only**, evidências e observabilidade mínima.  
**Não inclui:** conectores (S8), consenso (S9), MBP/settlement (S10+), UI.  
**Dependências:** Python 3.11+, TZ=UTC, locale `C`; libs hashing/ed25519; acesso a `data/raw/`.  
**Restrições:** chaves **de teste** somente; zero segredos reais; runner ubuntu‑22.04.

---

### 3) Suposições e Metas
**Suposições:** entradas brutas podem conter ruído (serão ajustadas/descartadas com log).  
**Metas:** reprocesso bit‑a‑bit idêntico; 10k registros/batch ≤ **2s** total; logs/metrics mínimas padronizadas.

---

### 4) Glossário e Normalizações (normativo)
**Unicode:** strings MUST ser normalizadas para **NFKC**; whitespace externo MUST ser **trimado**.  
**Case:** `currency` MUST ser **UPPERCASE** ISO‑4217 (ex.: `BRL`); `unit` e `source` MUST ser **lowercase**.  
**Separadores decimais:** somente ponto (`.`); vírgula nas entradas MUST ser normalizada.  
**Canonical JSON:** `sort_keys=true`, `ensure_ascii=false`, `separators=(",", ":")`, UTF‑8 (sem BOM), **sem newline final**; encoder Decimal **4 casas** (ver §8).  
**Hashes (sha256):** representação MUST ser **hex lowercase de 64 chars**.  
**entries_hash:** `sha256(canonical_json(records))`.  
**root (Merkle):** `sha256` da raiz sobre folhas `sha256(canonical_json(record))`; se N ímpar, duplicar última folha; pai = `sha256(left||right)`.  
**idempotency_key:** `sha256(source|product|region|observed_at|value(4dp))` (após normalizações).  
**Tempo:** `observed_at`/`ingested_at` MUST ser **UTC (RFC3339 com Z)**; `ingested_at ≥ observed_at`.

---

## 5) Arquitetura de alto nível
E1 **Normalizador** → `records[]` ordenados  
E2 **Builder** → `entries_hash` + `stats` + `created_at`  
E3 **Merkle** → `root` no `batch.json`  
E4 **Assinatura/Verify** → `*.sig.json` válido  
E5 **Append‑only Log** → `{index, root, prev_root, ...}` + relatório  
E6 **Observabilidade** → logs/metrics  
E7 **Evidências** → `out/evidence/T*/` + `s7-evidence.zip`

---

## 6) Entregáveis (E1..E7)

### E1 — Normalizador determinístico (schema v1)
**Explicação simples:** consolida e padroniza entradas heterogêneas, com ordem/tipos fixos.  
**Como funciona:**
1. Ler `data/raw/*.{json,csv}` (UTF‑8); aplicar **NFKC**, trimming e coerções (`unit`, `currency`, decimal).  
2. Validar contra **Schema v1** (§7); descartar inválidos com log estruturado.
3. Calcular `idempotency_key` após normalizações.  
4. **Ordenar** por comparador formal (§6.A).  
5. Exportar `records[]` determinísticos.  
**Finalidade:** base reprodutível para hashing/assinatura.  
**CLI:** §13.1.  
**Regras/Contratos:** determinismo; rounding bankers; BRL default; idempotência.  
**Pré/Pós:** arquivos legíveis → `records[]` válidos/ordenados.  
**Exemplos (before/after) + unidade:** §9.  
**Erros & EXIT:** `21 invalid_record`, `22 csv_parse_error`.  
**Evidências:** `out/evidence/T5_props/properties_summary.json`.  
**Obs.:** `normalize_records_count`, `normalize_elapsed_ms`.

**§6.A — Comparador de ordenação (normativo)**  
`key(x)` = `(x.observed_at, x.source, x.product, x.region, x.idempotency_key)`; ordenar por **ordem lexicográfica ascendente** sobre `key(x)`. `observed_at` comparado como **timestamp UTC**; strings já normalizadas (NFKC, trimmed). Empates (tuplas idênticas) implicam **deduplicação**.

### E2 — Builder de batch canônico (`entries_hash` + stats)
Recebe `records[]` ordenados; calcula `entries_hash`; agrega `stats` (`count,min_ts,max_ts,sources,regions`); define `created_at` (UTC); grava `batch.json` **sem** `root`. `entries_hash` depende **apenas** de `records`.  
**CLI:** §13.2 (opcional).  
**EXIT:** `31 serialization_mismatch`.

### E3 — Raiz Merkle
Folhas = `sha256(JSON(record))`; pareamento até raiz; duplicar última se ímpar; escrever `root` no `batch.json`. Pai MUST ser `sha256(left_bytes || right_bytes)`.  
**CLI:** §13.3.  
**EXIT:** `41 merkle_inconsistent`.

### E4 — Assinatura Ed25519 + Verificação
Canonicalizar payload `{root, entries_hash, schema_version, created_at}`; **domain‑tag exato** `tm.s7.batch.v1\n` (byte 0x0A no final); assinar com chave de teste; verificador reconstrói payload e falha se `schema_version` divergir.  
`public_key`/`signature` MUST ser **Base64 padrão com padding `=`** (sem quebras).  
**CLIs:** §13.4–§13.5.  
**EXIT:** `51 invalid_signature`, `52 missing_constant`.

### E5 — Log **append‑only** + Guard (especificação temporal)
`L[i] = {index, created_at, root, prev_root, batch_sha256}` com `index` iniciando em 1. Invariantes: `L[i].prev_root=L[i-1].root`; `L[i].index=L[i-1].index+1`; `created_at` da linha ≥ `batch.created_at`; `batch_sha256` = sha256 do **arquivo** `batch.json` (já com `root`).  
**CLI:** §13.6.  
**EXIT:** `61 reorder_detected`, `62 prev_root_mismatch`.

### E6 — Observabilidade mínima
Logs JSON‑lines `{ts, level, service, op, elapsed_ms, count[, trace_id]}`; métricas em `out/metrics/*.json`.  
**EXIT:** `71 obs_missing`.

### E7 — Evidências padronizadas (estrutura)
Organizar saídas em `out/evidence/T1..T8/` e empacotar `s7-evidence.zip` + `sha256_s7_evidence.txt` (+ `SUMMARY.md` por T*).  
**CLI:** §13.7.  
**EXIT:** `81 duplicate_artifact`.

**Contrato de totalidade (normativo):** cada CLI **MUST** retornar **EXIT 0 iff** (e somente se) **todas** as **pós‑condições** do respectivo E‑item forem verdadeiras.

---

## 7) JSON Schema v1 (normativo, draft‑07)
```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "TM S7 Record v1",
  "type": "object",
  "required": [
    "source","region","category","product","value","unit","currency",
    "observed_at","ingested_at","quality","confidence","idempotency_key","schema_version"
  ],
  "properties": {
    "source": {"type": "string", "pattern": "^[a-z0-9_\-]{2,32}$"},
    "region": {"type": "string", "pattern": "^BR-[A-Z]{2}(-[A-Za-z0-9]{1,10})?$"},
    "category": {"type": "string", "enum": ["alimentos","combustiveis","energia","transporte","higiene","outros"]},
    "product": {"type": "string", "minLength": 2, "maxLength": 64},
    "value": {"type": "number", "multipleOf": 0.0001, "minimum": 0.0, "maximum": 1000000.0},
    "unit": {"type": "string", "enum": ["kg","g","l","ml","un","pct"]},
    "currency": {"type": "string", "enum": ["BRL","USD"]},
    "observed_at": {"type": "string", "format": "date-time"},
    "ingested_at": {"type": "string", "format": "date-time"},
    "quality": {"type": "string", "enum": ["A","B","C"]},
    "confidence": {"type": "number", "minimum": 0.0, "maximum": 1.0},
    "idempotency_key": {"type": "string", "pattern": "^[a-f0-9]{64}$"},
    "schema_version": {"type": "string", "const": "1"}
  },
  "additionalProperties": false
}
```

**Restrições cruzadas (normativas):** `ingested_at ≥ observed_at`; se `currency != "BRL"`, conversão explícita MUST ser aplicada ou registro rejeitado; `confidence` SHOULD acompanhar `quality` (ex.: `A ≥ 0.9`, `B ≥ 0.7`, `C ≥ 0.5`).

---

## 8) Canonicalização — Encoder Decimal (4 casas)
```python
from decimal import Decimal, ROUND_HALF_EVEN
import json

class Decimal4Encoder(json.JSONEncoder):
  def default(self, obj):
    if isinstance(obj, Decimal):
      q = obj.quantize(Decimal("0.0001"), rounding=ROUND_HALF_EVEN)
      return float(f"{q:.4f}")
    return super().default(obj)

def canonical_json(obj) -> bytes:
  """Serializa sem BOM, sem newline final, UTF‑8, chaves ordenadas e separadores fixos."""
  return json.dumps(
    obj,
    sort_keys=True,
    ensure_ascii=False,
    separators=(",", ":"),
    cls=Decimal4Encoder
  ).encode("utf-8")
```
**Propriedade:** `sha256(canonical_json(x))` é único e reprodutível (locale‑independente com `LC_ALL=C`).

---

## 9) Receita de Reprodutibilidade + Vetores (positivos e negativos)
**Ambiente normativo:** `Python==3.11.14`, `TZ=UTC`, `LC_ALL=C`, `LANG=C.UTF-8`.  
**Dataset‑A (3 registros) — POSITIVO:**
- `entries_hash` = `f830ec4f7b468dc569c56d6b4a18e7379a4958ea8789f36dcaf13f44ff472112`
- Folhas: `1ada972b1985ad3270335bf121a4644b0c67705dcf2c864eb7f21643c7beeec0`, `56089c09c07ef28609edfcec038123f1a25dd090c31cd371f7170ad520ae0703`, `3460bf3d6e1fad050236f94b2925505c46a2e0439b0f444a94bc10a72f0e911a`
- `root` = `cc1fd0ae131fd0c78e111655ae057b282327f896f19e8bf38f862f901dda0793`
- `batch_sha256` = `514b3a78aa5883cdb899bb4e9b442657e7213704c2652673956b364f46184ceb`

**Dataset‑N1 (NEGATIVO — domain_tag errado):** espera **falhar** com `EXIT 51 invalid_signature`.  
**Dataset‑N2 (NEGATIVO — `prev_root` divergente):** espera **falhar** com `EXIT 62 prev_root_mismatch`.  
**Padrão de erro estruturado (ex.):**
```json
{"ok":false,"exit_code":62,"error":"prev_root_mismatch","hint":"L[3].prev_root != L[2].root","context":{"index":3}}
```

---

## 10) Tabela Única de Contratos (Meyer)
| Entregável | Pré‑condições | Pós‑condições | Invariantes/Contratos | EXIT codes |
|---|---|---|---|---|
| E1 Normalizador | Entradas em `data/raw/` | `records[]` válidos e ordenados | determinismo; rounding; idempotência | 21 invalid_record; 22 csv_parse_error |
| E2 Builder | `records[]` prontos | `batch.json` com `entries_hash` (sem `root`) | `entries_hash` depende só de `records` | 31 serialization_mismatch |
| E3 Merkle | `batch.json` sem `root` | `batch.json` com `root` | raiz reprodutível; duplicação de folha ímpar | 41 merkle_inconsistent |
| E4 Assinatura/Verify | `root` presente; chaves teste | `*.sig.json` válido | payload c/ domain‑tag exata; Base64 com padding; drift≤5m | 51 invalid_signature; 52 missing_constant |
| E5 Append‑only | `batch.json` & assinatura válidos | linha adicionada + relatório ok | prev_root=raiz anterior; index++ | 61 reorder_detected; 62 prev_root_mismatch |
| E6 Observabilidade | CLIs executadas | métricas/logs presentes | logs JSON‑lines; métricas por etapa | 71 obs_missing |
| E7 Evidências | pastas `out/evidence/T*/` | `s7-evidence.zip` + sha256 | ZIP único; caminhos estáveis | 81 duplicate_artifact |

**EXIT 0 iff:** todas as **pós‑condições** na linha da tabela são verdadeiras.

---

## 11) Escolhas Cripto & Ameaças (Vitalik)
**Algoritmo:** Ed25519 (PyNaCl/`cryptography`).  
**Domain separation:** **exato** `tm.s7.batch.v1\n` (0x0A).  
**Encoding:** `public_key` & `signature` em **Base64 padrão com padding `=`**, sem quebras.  
**Ameaças ↔ Contramedidas:** replay/resign → domain‑tag + `schema_version`; reorder → Merkle + invariantes append‑only; truncamento → verificação `index/prev_root`; confusables Unicode → **NFKC**.

---

## 12) Critérios de Aceite (DoD do Cap.1)
Cap.1 **publicável**, com E1..E7 no formato do Playbook; Schema v1 reforçado; encoder Decimal 4dp; NFKC; comparador de ordenação formal; exemplo com **hashes esperados**; vetores **negativos**; invariantes temporais; tabela de contratos/EXIT; escolhas cripto (Base64 + domain‑tag exata); CLIs tipadas; domínios canônicos; SLOs; compatibilidade/versão; concorrência/determinismo.

---

## 13) Interfaces das CLIs — Tabela + JSON Schema
> Todas as CLIs **MUST** retornar **EXIT 0 iff** todas as **pós‑condições** do E‑item forem verdadeiras. Caso contrário, retornar o EXIT code normativo.

### 13.1 `normalize_batch`
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--in` | string | sim | — | Diretório/arquivo de entrada |
| `--out` | string | não | `out/normalized/batch.json` | Arquivo de saída |
| `--fail_on_invalid` | bool | não | `false` | Aborta no 1º inválido |
| `--max_records` | int | não | `0` | 0=ilimitado |
**EXIT:** `21`, `22`  
**JSON schema (args):** `{ "type":"object","required":["in"],"properties":{"in":{"type":"string"},"out":{"type":"string","default":"out/normalized/batch.json"},"fail_on_invalid":{"type":"boolean","default":false},"max_records":{"type":"integer","default":0}}}`

### 13.2 `build_batch` (opcional)
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--in` | string | sim | — | `batch.json` sem `root` |
| `--out` | string | não | `out/normalized/batch.json` | Saída |
**EXIT:** `31`

### 13.3 `merkle_build`
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--in` | string | sim | — | `batch.json` |
| `--out` | string | não | `out/normalized/batch.json` | Saída |
| `--leaf_hash` | enum | não | `sha256` | Hash de folhas |
**EXIT:** `41`

### 13.4 `sign_batch`
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--in` | string | sim | — | `batch.json` com `root` |
| `--out` | string | não | `out/signatures/latest.sig.json` | Saída |
| `--domain_tag` | string | não | `tm.s7.batch.v1` | Domain‑sep (verificador aplica `"\n"`) |
| `--privkey` | string | não | `tests/fixtures/crypto/test_ed25519_priv.pem` | Chave priv |
| `--pubkey` | string | não | `tests/fixtures/crypto/test_ed25519_pub.pem` | Chave pub |
**EXIT:** `52` (missing_constant); `51` (invalid_signature se self‑verify falhar)

### 13.5 `verify_batch`
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--in` | string | sim | — | `batch.json` |
| `--sig` | string | sim | — | `*.sig.json` |
| `--domain_tag` | string | não | `tm.s7.batch.v1` | Domain‑sep (aplica `"\n"` ao payload) |
| `--pubkey` | string | não | `tests/fixtures/crypto/test_ed25519_pub.pem` | Chave pub |
**EXIT:** `51`, `52`

### 13.6 `append_only_guard`
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--log` | string | sim | — | `data/log/log.jsonl` |
| `--out` | string | não | `out/evidence/T7_append_only/append_only_report.json` | Saída |
**EXIT:** `61`, `62`

### 13.7 `pack_evidence`
| Arg | Tipo | Obrig. | Default | Descrição |
|---|---|---|---|---|
| `--out` | string | não | `out/s7-evidence.zip` | ZIP |
| `--root` | string | não | `out/evidence/` | Raiz evidências |
**EXIT:** `81`

---

## 14) Domínios canônicos iniciais (enumerados)
**unit:** `kg`, `g`, `l`, `ml`, `un`, `pct`  
**category:** `alimentos`, `combustiveis`, `energia`, `transporte`, `higiene`, `outros`  
**currency:** `BRL`, `USD`

---

## 15) SLOs por etapa (p95, runner ubuntu‑22.04, 10k registros)
| Etapa | Métrica | Warn | Hard |
|---|---|---|---|
| E1 Normalizar | `normalize_elapsed_ms` | ≤ 900 ms | ≤ 1,2 s |
| E2 Build batch | `build_batch_ms` | ≤ 180 ms | ≤ 250 ms |
| E3 Merkle | `merkle_build_ms` | ≤ 350 ms | ≤ 500 ms |
| E4 Assinar | `sign_ms` | ≤ 60 ms | ≤ 90 ms |
| E4 Verificar | `verify_ms` | ≤ 60 ms | ≤ 90 ms |
| E5 Append‑only guard | `append_only_guard_ms` | ≤ 120 ms | ≤ 180 ms |
| E7 Empacotar evidências | `pack_evidence_ms` | ≤ 240 ms | ≤ 360 ms |
| **Total** | — | ≤ 2.2 s | **≤ 3.0 s** |

---

## 16) Padrão de erro estruturado (todas as CLIs)
```json
{
  "ok": false,
  "exit_code": 21,
  "error": "invalid_record",
  "hint": "campo 'value' fora do domínio (multipleOf 0.0001)",
  "context": {"file": "data/raw/x.csv", "line": 128}
}
```

---

## 17) Compatibilidade & Versão (normativo)
**Schema SemVer:** `schema_version` segue **MAJOR.MINOR**; S7 fixa `"1"` (MAJOR=1). Alterações que quebrem determinismo/formatos elevam **MAJOR**.  
**Forward compat:** consumidores que aceitam `1.x` MUST validar apenas campos normativos presentes.  
**Back compat:** produtores `1.x` MUST não alterar semântica de campos existentes.

---

## 18) Concorrência & Determinismo
Ferramentas MAY paralelizar leitura/conversões, mas MUST aplicar o **comparador** (§6.A) e **canonicalização** (§8) antes de hashing/assinatura. Proibido usar entropia não determinística nos cálculos normativos.

---

## 19) EXIT codes — Espaço reservado (normativo)
`20–29` Normalização/I‑O; `30–39` Serialização/Batch; `40–49` Merkle; `50–59` Cripto; `60–69` Append‑only; `70–79` Observabilidade; `80–89` Evidências. Códigos novos MUST manter unicidade e semântica.

---

## 20) Exemplo end‑to‑end (determinístico)
1) **Before**: 3 registros com variações (`Kg`/`kg`, vírgula decimal, `sp`/`BR‑SP`).  
2) **After**: normalizados (NFKC, trimmed, coerções); ordenados; `entries_hash`=`f830...2112`.  
3) **Merkle**: folhas `1ada...eec0`, `5608...0703`, `3460...11a`; `root`=`cc1f...0793`.  
4) **Assinatura**: payload canonical `{root, entries_hash, schema_version:"1", created_at}` com domain‑tag exata ⇒ `*.sig.json` válido (Base64 com padding).  
5) **Append**: `index=1, prev_root=null, root=cc1f...0793` no `log.jsonl`; `append_only_report.ok=true`.

---

## 21) Anexos
- **JSON Schema v1** (§7)  
- **Encoder canônico** (§8)  
- **Vetores (pos/neg)** (§9)  
- **Tabela de contratos** (§10)  
- **Cripto & ameaças** (§11)  
- **CLIs tipadas** (§13)  
- **SLOs** (§15)  
- **Compat/Versão** (§17)  
- **Concorrência/Determinismo** (§18)

