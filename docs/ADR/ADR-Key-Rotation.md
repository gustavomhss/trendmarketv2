# ADR: Ed25519 Key Rotation and Custody

## Status
Accepted – October 29, 2025

## Context
To maintain trust in the Oracle evidence chain, signing keys must rotate predictably and survive compromise events. Prior practice left long-lived keys in CI, violating the 90-day rotation requirement and lacking custody documentation.

## Decision
- Rotation cadence: every 90 days. Keys transition through `active → retiring (7 day overlap) → retired`; only `active` keys may issue new signatures.
- Keystore format (`tools/crypto/keystore.json`): list of key metadata with `kid`, `alg`, `created_at`, `not_after`, `issuer`, `pubkey`, `status`.
- Custody: private seeds are generated offline (air-gapped workstation), sealed in the vault, and only the base64 public key enters the repository. Deployment environments inject the seed via secret management; no private key material is committed.
- Incident response: on suspected compromise, mark the affected key `retired`, generate a replacement (new `kid`), re-sign the latest Merkle root, and document RCA + mitigations in the custody log.
- Drift mitigation: keystore updates are version-controlled; every rotation requires checksum publication and validation in the CI gate report.

## Consequences
- CI validation (`scripts/ci/validate_s7.py`) fails if no `active` key matches the rotation window, preventing stale or compromised keys from signing.
- Operators must maintain an auditable generation log (timestamp, operator, entropy source, checksum) stored alongside the custody record.
- When transitioning to `retiring`, keep both the previous and new keys available for seven days to avoid verification gaps.
- Any revocation triggers immediate notification to downstream consumers and re-issuance of the last valid Merkle root using the new active key.
