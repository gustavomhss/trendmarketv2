import json
import os
import subprocess
from pathlib import Path


def run_creator(tmp_path: Path, catalog: dict, policy: str, name: str = "Market Test"):
    catalog_path = tmp_path / "catalog.json"
    catalog_path.write_text(json.dumps(catalog), encoding="utf-8")
    policy_path = tmp_path / "policy.yml"
    policy_path.write_text(policy, encoding="utf-8")
    generated = tmp_path / "generated.json"
    evidence = tmp_path / "evidence"
    env = os.environ.copy()
    env.update(
        MBP_TEMPLATE_CATALOG=str(catalog_path),
        MBP_POLICY_FILE=str(policy_path),
        MBP_GENERATED_MARKETS=str(generated),
        MBP_EVIDENCE_DIR=str(evidence),
    )
    result = subprocess.run(
        ["python3", "scripts/s3/create_market_from_template.py", "TPL-YESNO-01", name],
        env=env,
        capture_output=True,
        text=True,
    )
    return result, generated, evidence


def base_catalog():
    return {
        "version": 2,
        "validation": {
            "min_liquidity_bounds": {"binary": {"min": 100, "max": 2000}},
            "allowed_truth_sources": {"binary": ["RS-YESNO-001"]},
            "resolution_window_h": {"min": 1, "max": 48},
        },
        "templates": [
            {
                "id": "TPL-YESNO-01",
                "category": "binary",
                "truth_source": "RS-YESNO-001",
                "min_liquidity": 500,
                "resolution_window_h": 24,
            }
        ],
    }


def base_policy(flag: bool = True) -> str:
    return "version: 1\nfeature_flags:\n  mbp.create.by_template: {flag}\n".format(
        flag=str(flag).lower()
    )


def test_create_market_success(tmp_path):
    result, generated, evidence = run_creator(tmp_path, base_catalog(), base_policy())
    assert result.returncode == 0, result.stderr
    data = json.loads(generated.read_text())
    assert data[0]["template_id"] == "TPL-YESNO-01"
    audit = next(evidence.glob("audit_market_created_template.jsonl"))
    assert "market_created_template" in audit.read_text()


def test_create_market_flag_disabled(tmp_path):
    result, _, _ = run_creator(tmp_path, base_catalog(), base_policy(False))
    assert result.returncode == 3
    assert "feature flag" in result.stderr


def test_create_market_validation_failure(tmp_path):
    catalog = base_catalog()
    catalog["templates"][0]["min_liquidity"] = 50
    result, _, _ = run_creator(tmp_path, catalog, base_policy())
    assert result.returncode != 0
    assert "min_liquidity" in result.stderr + result.stdout
