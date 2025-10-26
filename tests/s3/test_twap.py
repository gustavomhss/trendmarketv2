import json
import os
import subprocess
from pathlib import Path

CSV_HEADER = "ts,price\n"


def write_prices(path: Path, rows):
    path.write_text(
        CSV_HEADER + "\n".join(f"{ts},{price}" for ts, price in rows),
        encoding="utf-8",
    )


def run_twap(tmp_path: Path, rows):
    prices = tmp_path / "prices.csv"
    write_prices(prices, rows)
    output = tmp_path / "twap.csv"
    evidence = tmp_path / "evidence"
    env = os.environ.copy()
    env["MBP_EVIDENCE_DIR"] = str(evidence)
    subprocess.check_call(["python3", "scripts/s3/twap_compute.py", str(prices), str(output)], env=env)
    return output, evidence


def test_freeze_by_divergence(tmp_path):
    rows = [
        ("2024-01-01T00:00:00+00:00", "100"),
        ("2024-01-01T00:01:00+00:00", "100"),
        ("2024-01-01T00:02:00+00:00", "100"),
        ("2024-01-01T00:03:00+00:00", "110"),
        ("2024-01-01T00:04:00+00:00", "111"),
    ]
    twap_csv, evidence = run_twap(tmp_path, rows)
    verdict = subprocess.check_output(
        [
            "bash",
            "scripts/s3/twap_freeze_check.sh",
            str(twap_csv),
            str(evidence / "twap_events.json"),
        ],
        text=True,
    ).strip()
    assert verdict == "FREEZE=YES"
    data = json.loads((twap_csv.parent / "twap_freeze.json").read_text())
    assert data["reason"] in {"divergence", "ic99"}


def test_freeze_by_ic99(tmp_path):
    rows = [
        ("2024-01-01T00:00:00+00:00", "100"),
        ("2024-01-01T00:01:00+00:00", "100"),
        ("2024-01-01T00:02:00+00:00", "100"),
        ("2024-01-01T00:03:00+00:00", "100.6"),
        ("2024-01-01T00:10:00+00:00", "100"),
        ("2024-01-01T00:11:00+00:00", "100"),
        ("2024-01-01T00:12:00+00:00", "100"),
        ("2024-01-01T00:13:00+00:00", "100.6"),
        ("2024-01-01T00:20:00+00:00", "100"),
        ("2024-01-01T00:21:00+00:00", "100"),
        ("2024-01-01T00:22:00+00:00", "100"),
        ("2024-01-01T00:23:00+00:00", "100.6"),
    ]
    twap_csv, evidence = run_twap(tmp_path, rows)
    verdict = subprocess.check_output(
        [
            "bash",
            "scripts/s3/twap_freeze_check.sh",
            str(twap_csv),
            str(evidence / "twap_events.json"),
        ],
        text=True,
    ).strip()
    data = json.loads((twap_csv.parent / "twap_freeze.json").read_text())
    assert verdict == "FREEZE=YES"
    assert data["ic99_exceeded"] >= 3
    assert data["reason"] in {"divergence", "ic99"}
