# ADR: Event Model v1

## Status
Accepted – October 29, 2025

## Context
The Oracle BR/LatAm programme requires an append-only, verifiable event pipeline. Prior sprints delivered ingestion prototypes without a canonical schema, making deduplication, hashing and cross-language reconciliation brittle. Sprint S7 establishes the canonical contract (`contracts/data/event_v1.json`) to unblock deterministic hashing, equivalence grouping and downstream audit evidence.

## Decision
- Adopt JSON Schema 2020-12 as the normative contract for event batches.
- Normalise human-readable strings using Unicode NFKD → ASCII7 → lowercase → whitespace collapse to guarantee deterministic comparisons across PT/ES sources.
- Enforce kebab-case tokens for `category` and `source` via canonical tokeniser to remove inconsistent spacing/punctuation.
- Require `equivalenceHash = sha256(canon_text(title) + "|" + canon_text(category))` as the stable grouping identifier across languages.
- Derive the event identifier as `sha256(json.dumps(event_without_id, sort_keys=True, separators=(',', ':')))`, guaranteeing canonical ordering before hashing.
- Reject payload objects containing keys prefixed with `_` to avoid hidden or control metadata in evidences.
- Canonicalise `observed_at` timestamps to UTC (`Z`) and enforce a maximum future skew of five minutes relative to ingestion.

## Consequences
- All ingestion paths must pass through the canonical normaliser before persistence or hashing.
- Golden fixtures in `tests/goldens/normalizer/` encode PT and ES expectations and must remain stable; changes require ADR updates.
- Downstream consumers can rely on deterministic `equivalenceHash`/`id` pairs for deduplication and equivalence-class auditing.
- Payload producers need to avoid underscore-prefixed keys; future schema evolution must version the contract (e.g., `event_v2.json`) instead of mutating the current definition.
