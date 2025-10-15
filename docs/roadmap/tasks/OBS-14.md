# OBS-14 — Segurança & PII
**Objetivo:** negar PII em logs/código e auditar deps.
**Aceite:** `gitleaks` 0 achados; `cargo audit` ok; `SBOM_OK` gerado.
**Artefatos:** `ops/security/gitleaks.toml`, `ops/security/log_denylist.json`, `scripts/obs_sbom.sh`.
**Evidências:** `sbom.cdx.json` + hash; logs sem PII.
