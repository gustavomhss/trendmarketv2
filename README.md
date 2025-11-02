# TrendMarket Sprint 7

## Overview S7
This repository contains the canonical implementation of Sprint 7 (Stabilize). The normative specification lives in:
- `docs/specs/s7/cap1_spec.md`
- `docs/specs/s7/cap2_gates.md`
- `docs/specs/s7/cap3_filemap.md`

## Run Local
```bash
python -m scripts.normalizer.normalize_batch --in data/raw --out out/normalized/batch.json
python -m scripts.merkle.merkle_build --in out/normalized/batch.json --out out/normalized/batch.json
python -m scripts.crypto.sign_batch --in out/normalized/batch.json --out out/signatures/latest.sig.json
pytest -q tests/
```

## Gates and Evidence
Gate outputs are written under `out/evidence/T*/`. The manifest (`out/MANIFEST.json`), scorecard (`out/scorecards/s7.json`) and the reproducible archive (`out/s7-evidence.zip`) document the run.

## Test Key Policy
Ed25519 keys located at `tests/fixtures/crypto/` are non-production fixtures and are the only secrets allowlisted via `.gitleaks.toml`.
