# CRD-8 Observabilidade — Promotion Checklist

## Pré-promoção (Dev → Staging)
- [x] `scripts/orr_all.sh` (profile=full) executado com `ACCEPTANCE_OK` e `GATECHECK_OK`.
- [x] `out/obs_gatecheck/summary.json` revisado (`acceptance=OK`, `gatecheck=OK`).
- [x] Manifesto `out/obs_gatecheck/release_manifest.json` atualizado (hash do bundle + métricas).
- [x] Metadados finais `out/obs_gatecheck/release_metadata.json` gerados via `scripts/obs_release_finalize.py`.
- [x] Revisar seções `watchers` e `drills` do manifesto (alertas esperados, spans correlacionados, chaos/PII).
- [ ] Watchers A110 verdes nas últimas 24h (p95 swap, freshness, CDC, drift, hooks, cardinalidade, synthetic).
- [ ] Dashboards D1..D6 capturados e anexados ao bundle.
- [x] Sem alertas de PII (`PII_OK`) e SBOM assinada (`sbom.cdx.sha256`).

## Promoção (Staging → Prod)
- [ ] Bundle `obs-bundle-*` anexado à release `crd-8-obs-YYYYMMDD` com SHA256 publicado.
- [x] Checklist de Risco revisado (chaos drill, baseline, custos/cardinalidade < 70%).
- [x] Synthetic prober (`synthetic_ok_ratio`) ≥ 0.99 nas últimas 12h.
- [ ] Runbook de rollback verificado e acessível.
- [ ] Owners (@gustavomhss) aprovam watchers/scripts/ops alterações.

## Pós-promoção
- [ ] Burn rate < 1.0 nas 24h seguintes.
- [ ] Atualizar roadmap com próximos incrementos de observabilidade.
- [ ] Arquivar evidências no storage compartilhado (≥30 dias).
