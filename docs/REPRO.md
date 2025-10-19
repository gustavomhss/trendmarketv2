# REPRO — S4 • Gate Pre-GA (M2)

1. **Bootstrap toolchain:** `python3 -m venv .venv && source .venv/bin/activate && pip install -r requirements.lock`.
2. **Instalar Node deps:** `npm ci --ignore-scripts` (usa `package-lock.json`).
3. **Validar toolchain:** `bash scripts/env_pin_check.sh` (falha em ausência de locks/digests).
4. **Preparar observabilidade local:** `node fe/rum/server.js &` e `cargo fetch && cargo build` (bench harness).
5. **Executar ORR completo:** `make prega` (env pin → ORR → bundle → anchors → export notebook de performance).
6. **Publicar release/tag:** `bash scripts/anchor_integrity.sh && git push origin --tags && gh release create s4-v1.4 out/s4_evidence_bundle_*.zip`.
