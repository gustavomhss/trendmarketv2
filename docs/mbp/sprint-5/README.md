# MBP Sprint 5 Gate Summary

- **Gate Script**: `scripts/orr_s5_run.sh` executes oracle, TWAP, fees, moderation, auto-resolution, and simulation checks.
- **Telemetry**: Prometheus/OTel instrumentation spans `oracle.fetch`, `oracle.aggregate`, `fee.update`, `moderation.apply`, `resolve.decision`, and `sim.run`.
- **Evidence Bundle**: Generated via `scripts/s5_bundle.sh` with artifacts in `out/obs_gatecheck/` including oracle reports, fee audits, moderation ops report, resolution metrics, simulation reports, and dbt outputs (`ce.duckdb`, `manifest.json`, `run_results.json`, docs).
- **SLAs**: Moderation MTTD ≤ 5m and MTTM ≤ 15m enforced during gate execution.
- **Reproduction**:
  1. `pip install -r requirements.lock`
  2. `make orr`
  3. Inspect `out/obs_gatecheck/evidence`
  4. `make bundle`
- **Bundle SHA**: Located at `out/obs_gatecheck/bundle.sha256.txt`.
