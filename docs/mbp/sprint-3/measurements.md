# Sprint 3 – MBP Measurements

| KPI | Target | Result | Evidence |
| --- | --- | --- | --- |
| Template creation success rate | >= 99% | 100% (3/3 seeds) | `out/s3_gatecheck/evidence/audit_market_created_template.jsonl` |
| Rule engine evaluated seeds | 100% | 100% | `out/s3_gatecheck/evidence/rule_eval.json` |
| TWAP freeze violations | < 1 per run | 0 | `out/s3_gatecheck/evidence/twap_freeze.json` |
| Abuse detections reviewed | 100% | 100% manual approvals | `out/s3_gatecheck/evidence/abuse_flags.json` |

## Notes
- Measurements collected via `scripts/s3/run_all_s3.sh` bundle after telemetry emission.
- Evidence bundle hashes stored alongside `out/s3_gatecheck/bundle.sha256.txt` for reproducibility.
