import json
import os
import subprocess

RULES_YAML = """
version: 1
rules:
  - id: RS-TEST-TABLE
    name: test_table
    source_kind: table
    table: test_table
    field_question: key
    field_answer: value
    resolution_window_h: 24
  - id: RS-TEST-ENDPOINT
    name: test_endpoint
    source_kind: endpoint
    url: http://example.com
fallback:
  manual:
    required_evidence: true
    approvers: ["ops@trend"]
"""

SEEDS = [
    {"rule_id": "RS-TEST-TABLE", "payload": {"key": "A"}},
    {"rule_id": "RS-TEST-ENDPOINT", "payload": {"market_id": "m1"}},
    {
        "rule_id": "RS-TEST-TABLE",
        "payload": {"key": "missing"},
        "manual": {"approver": "ops@trend", "ticket": "MBP-1"},
    },
]

CSV = "key,value\nA,YES\n"


def test_rule_engine_outputs(tmp_path):
    rules_path = tmp_path / "rules.yml"
    rules_path.write_text(RULES_YAML, encoding="utf-8")
    seeds_path = tmp_path / "seeds.json"
    seeds_path.write_text(json.dumps(SEEDS), encoding="utf-8")
    table_csv = tmp_path / "test_table.csv"
    table_csv.write_text(CSV, encoding="utf-8")
    evidence = tmp_path / "evidence"
    env = os.environ.copy()
    env.update(
        MBP_RULES_FILE=str(rules_path),
        MBP_RULE_SEEDS=str(seeds_path),
        MBP_RULE_SEEDS_DIR=str(tmp_path),
        MBP_EVIDENCE_DIR=str(evidence),
    )
    subprocess.check_call(
        ["python3", "scripts/s3/rule_engine.py", "evaluate", str(seeds_path)], env=env
    )

    rule_eval = json.loads((evidence / "rule_eval.json").read_text())
    table_statuses = [
        row["result"]["status"]
        for row in rule_eval
        if row["rule_id"] == "RS-TEST-TABLE"
    ]
    assert "ok" in table_statuses
    statuses = {row["rule_id"]: row["result"]["status"] for row in rule_eval}
    assert statuses["RS-TEST-ENDPOINT"] == "ok"
    manual_entries = [row for row in rule_eval if row["result"]["status"] == "manual"]
    assert manual_entries, "expected manual fallback"
    approvals = (
        (evidence / "rule_manual_approvals.jsonl").read_text().strip().splitlines()
    )
    assert any("MBP-1" in line for line in approvals)
