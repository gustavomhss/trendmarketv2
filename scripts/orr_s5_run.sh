#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

ROOT=$(git rev-parse --show-toplevel)
OUT_ROOT="$ROOT/out"
OBS_DIR="$OUT_ROOT/obs_gatecheck"
EVID_DIR="$OBS_DIR/evidence"
DBT_OUT="$OUT_ROOT/dbt"
SIM_OUT="$OUT_ROOT/sim"
ORACLE_OUT="$OUT_ROOT/oracles"
FEES_OUT="$OUT_ROOT/fees"
MOD_OUT="$OUT_ROOT/moderation"
RESOLVE_OUT="$OUT_ROOT/resolve"

log() {
  printf '[orr-s5] %s\n' "$1"
}

mkdir -p "$OBS_DIR" "$EVID_DIR" "$DBT_OUT" "$SIM_OUT" "$ORACLE_OUT" "$FEES_OUT" "$MOD_OUT" "$RESOLVE_OUT"

export MBP_ORACLE_EVENT_LOG="$ORACLE_OUT/quorum_events.jsonl"
export MBP_TWAP_EVENT_LOG="$ORACLE_OUT/twap_events.jsonl"
export MBP_FEE_EVENT_LOG="$FEES_OUT/events.jsonl"
export MBP_MODERATION_EVENT_LOG="$MOD_OUT/events.jsonl"
export MBP_SIM_EVENT_LOG="$SIM_OUT/events.jsonl"

log "Running deterministic service validations"
python3 - <<'PY'
from __future__ import annotations

from datetime import datetime, timedelta
from pathlib import Path
import json

from services.auto_resolution.service import AutoResolutionService, TruthSourceSignal
from services.fees.engine import FeeBounds, FeeEngine
from services.moderation.service import ModerationService
from services.oracles.aggregator import Quote, aggregate_quorum
from services.oracles.twap import TwapEngine

ROOT = Path(".").resolve()
OUT_ROOT = ROOT / "out"
ORACLE_OUT = OUT_ROOT / "oracles"
FEES_OUT = OUT_ROOT / "fees"
MOD_OUT = OUT_ROOT / "moderation"
RESOLVE_OUT = OUT_ROOT / "resolve"

now = int(datetime.utcnow().timestamp() * 1000)
quotes = [
    Quote(symbol="BRLUSD", price=5.4375, ts_ms=now - 1000, source="alpha"),
    Quote(symbol="BRLUSD", price=5.4377, ts_ms=now - 800, source="beta"),
    Quote(symbol="BRLUSD", price=5.4376, ts_ms=now - 600, source="gamma"),
]
result = aggregate_quorum("BRLUSD", quotes, now_ms=now)
if not result.quorum_ok:
    raise SystemExit("Oracle quorum check failed")
(ORACLE_OUT / "quorum_report.json").write_text(json.dumps(result.__dict__, indent=2) + "\n", encoding="utf-8")

engine = TwapEngine(symbol="BRLUSD")
for quote in quotes:
    engine.ingest("primary", quote.price, quote.ts_ms)
    engine.ingest("secondary", quote.price * 1.0002, quote.ts_ms)

twap_snapshot = engine.compute(now_ms=now)
(ORACLE_OUT / "twap_snapshot.json").write_text(json.dumps(twap_snapshot, indent=2) + "\n", encoding="utf-8")

fee_engine = FeeEngine(base=0.002, alpha=1e-6, beta=0.05, bounds=FeeBounds(0.001, 0.01))
fee_engine.update_fee(volume=250_000, depth=1_200_000)
fee_engine.update_fee(volume=240_000, depth=1_100_000, now=fee_engine.history[-1].ts + 600)
fees_payload = [update.__dict__ for update in fee_engine.history]
(FEES_OUT / "audit.json").write_text(json.dumps(fees_payload, indent=2) + "\n", encoding="utf-8")

moderation = ModerationService(audit_log=MOD_OUT / "audit.log")
incident_ts = datetime.utcnow() - timedelta(minutes=3)
moderation.pause(
    symbol="BRLUSD",
    reason="sudden_divergence",
    actor="oncall",
    role="moderator",
    evidence_uri="s3://evidence/moderation-1",
    detected_at=incident_ts.timestamp(),
    trace_id="gate-orr-1",
)
moderation.resume(symbol="BRLUSD", actor="oncall", role="moderator", trace_id="gate-orr-2")
ops_report = moderation.generate_ops_report(MOD_OUT / "ops_report.json")
if ops_report["mttd_seconds"] is None or ops_report["mttd_seconds"] > 300:
    raise SystemExit("Moderation MTTD SLA violated")
if ops_report["mttm_seconds"] is None or ops_report["mttm_seconds"] > 900:
    raise SystemExit("Moderation MTTM SLA violated")

resolver = AutoResolutionService(
    audit_log=RESOLVE_OUT / "audit.log",
    event_log=RESOLVE_OUT / "events.jsonl",
    metrics_log=RESOLVE_OUT / "metrics.jsonl",
)
truth_signal = TruthSourceSignal(
    source="oracle",
    verdict="accepted",
    confidence=0.95,
    observed_at=datetime.utcnow().isoformat(),
    evidence_uri="s3://evidence/resolve",
).with_status("final")
resolution = resolver.apply(
    event_id="evt-orr-1",
    actor="auto",
    role="system",
    quorum_votes={
        "votes": [
            {"verdict": "accepted", "weight": 0.7},
            {"verdict": "accepted", "weight": 0.2},
            {"verdict": "rejected", "weight": 0.1},
        ],
        "divergence_pct": 0.002,
    },
    quorum=True,
    truth_source=truth_signal,
    metadata={"source": "orr_s5"},
)
if not resolution.quorum_ok:
    raise SystemExit("Auto-resolution quorum check failed")

PY

log "Running deterministic simulations"
SEED=42 python -m tools.sim_harness --fixtures "$ROOT/fixtures" --scenario spike --out "$SIM_OUT/spike.report.json"
SEED=42 python -m tools.sim_harness --fixtures "$ROOT/fixtures" --scenario gap --out "$SIM_OUT/gap.report.json"
SEED=42 python -m tools.sim_harness --fixtures "$ROOT/fixtures" --scenario burst --out "$SIM_OUT/burst.report.json"

log "Executing dbt pipeline"
mkdir -p "$DBT_OUT"
PROFILE_DIR="$OBS_DIR/dbt_profile"
mkdir -p "$PROFILE_DIR"
cat > "$PROFILE_DIR/profiles.yml" <<'YAML'
ce_profile:
  target: duckdb
  outputs:
    duckdb:
      type: duckdb
      path: out/dbt/ce.duckdb
      schema: main
      threads: 4
YAML

dbt deps --profiles-dir "$PROFILE_DIR" --profile ce_profile
dbt debug --profiles-dir "$PROFILE_DIR" --profile ce_profile
dbt run --profiles-dir "$PROFILE_DIR" --profile ce_profile
dbt test --profiles-dir "$PROFILE_DIR" --profile ce_profile
dbt docs generate --profiles-dir "$PROFILE_DIR" --profile ce_profile

log "Collecting evidence"
cp "$ORACLE_OUT/quorum_report.json" "$EVID_DIR/" 2>/dev/null || true
cp "$ORACLE_OUT/twap_snapshot.json" "$EVID_DIR/" 2>/dev/null || true
cp "$FEES_OUT/audit.json" "$EVID_DIR/" 2>/dev/null || true
cp "$MOD_OUT/ops_report.json" "$EVID_DIR/" 2>/dev/null || true
cp "$RESOLVE_OUT/metrics.jsonl" "$EVID_DIR/" 2>/dev/null || true
cp -r "$SIM_OUT" "$EVID_DIR/sim" 2>/dev/null || true
cp -r "$ROOT/target" "$EVID_DIR/dbt_target" 2>/dev/null || true
cp "$DBT_OUT/ce.duckdb" "$EVID_DIR/" 2>/dev/null || true

log "Generating Sprint 5 bundle"
bash "$ROOT/scripts/s5_bundle.sh"

log "Sprint 5 ORR gate complete"
