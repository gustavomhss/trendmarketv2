# ADR: Event Batch Signing

## Status
Accepted – October 29, 2025

## Context
Oracle batches must be independently verifiable and tamper-evident. Prior to Sprint S7, append-only proofs relied on implicit ordering without cryptographic guarantees, and signatures were absent. Audit gates require deterministic Merkle roots, explicit evidence bundles (`out/evidence/S7_event_model/`) and a signing workflow that survives rotations and incident response.

## Decision
- Canonical batch payload: events sorted lexicographically by `id`, leaf hash = `sha256(json(event))` with canonical separators.
- Merkle tree construction duplicates the final hash on odd levels to keep deterministic tree depth.
- The signed message concatenates `merkle_root|batch_ts` encoded as UTF-8 to bind the tree to the declared timestamp.
- Signatures use Ed25519 with public material recorded in `tools/crypto/keystore.json`; private material stays outside the repository and is injected via environment variable (`ORACLE_ED25519_SEED[_<KID>]`).
- Verification script enforces algorithm matching, time-window compliance (`active` or `retiring` with +7 day overlap) and recomputes the same message to detect tampering.
- Evidence artefacts (`batch_<ts>.json`, `batch_latest.json`, `signature.json`, `proof_append_only.json`) are rewritten atomically; monotonic timestamps prevent regressions in append-only proofs.

## Consequences
- CI workflows must run `sign_batch.py` and `verify_signature.py` sequentially; failure in either step blocks `_s4-orr` promotion.
- Operators must provision the Ed25519 seed material via CI/CD secrets; local runs without the seed abort with actionable messages.
- Any change to Merkle leaf encoding or message format is a breaking change requiring new ADR + schema version bump.
- Threat model coverage: tampering with batch contents invalidates the Merkle root; replaying signatures outside the allowed time window is rejected; revocation relies on keystore rotation policy (see ADR-Key-Rotation).
