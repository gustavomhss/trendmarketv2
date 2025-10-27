import json
import os
import subprocess

POLICY = """
version: 1
risk_caps:
  template_yesno:
    max_trade_rate_per_min: 2
    max_exposure_per_user: 150
    max_open_interest: 1000
    cooldown_s: 90
feature_flags:
  mbp.create.by_template: true
"""

ORDERS = [
    {
        "user": "u",
        "market_id": "m",
        "template_category": "binary",
        "qty": 60,
        "ts": 1000,
    },
    {
        "user": "u",
        "market_id": "m",
        "template_category": "binary",
        "qty": 60,
        "ts": 1005,
    },
    {
        "user": "u",
        "market_id": "m",
        "template_category": "binary",
        "qty": 60,
        "ts": 1010,
    },
    {
        "user": "u",
        "market_id": "m",
        "template_category": "binary",
        "qty": 200,
        "ts": 1015,
    },
    {
        "user": "u",
        "market_id": "m",
        "template_category": "binary",
        "qty": 10,
        "ts": 1020,
    },
]


def test_anti_abuse_flags(tmp_path):
    policy_path = tmp_path / "policy.yml"
    policy_path.write_text(POLICY, encoding="utf-8")
    orders_path = tmp_path / "orders.json"
    orders_path.write_text(json.dumps(ORDERS), encoding="utf-8")
    evidence = tmp_path / "evidence"
    env = os.environ.copy()
    env.update(
        MBP_POLICY_FILE=str(policy_path),
        MBP_ABUSE_FLAGS=str(tmp_path / "flags.json"),
        MBP_EVIDENCE_DIR=str(evidence),
    )
    subprocess.check_call(
        ["python3", "scripts/s3/anti_abuse.py", str(orders_path)], env=env
    )
    events = json.loads((tmp_path / "flags.json").read_text())
    reasons = {event["reason"] for event in events}
    assert {"burst", "exposure", "cooldown_violation"}.issubset(reasons)
    telemetry = (
        (evidence / "telemetry_anti_abuse.jsonl").read_text().strip().splitlines()
    )
    assert telemetry and all("abuse.detect" in line for line in telemetry)
