#!/usr/bin/env python3
"""Validation harness for Sprint S7 oracle deliverables."""
from __future__ import annotations

import json
import math
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

sys.path.append(str(Path(__file__).resolve().parents[2]))
from scripts.crypto.verify_signature import VerificationError, verify_signature

BATCH_PATH = Path("out/evidence/S7_event_model/batch_latest.json")
PROOF_PATH = Path("out/evidence/S7_event_model/proof_append_only.json")
SIGNATURE_PATH = Path("out/evidence/S7_event_model/signature.json")
KEYSTORE_PATH = Path("tools/crypto/keystore.json")
REPORT_PATH = Path("out/reports/validation/s7_gate_report.json")
CI_REPORT_PATH = Path("out/reports/validation/ci_gates_report.json")

REQUIRED_FILES = [BATCH_PATH, PROOF_PATH, SIGNATURE_PATH, KEYSTORE_PATH]


def _load_json(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return data


def _compute_merkle(leaves: List[str]) -> str:
    import hashlib

    if not leaves:
        return hashlib.sha256(b"").hexdigest()
    level = [bytes.fromhex(leaf) for leaf in leaves]
    while len(level) > 1:
        next_level: List[bytes] = []
        for idx in range(0, len(level), 2):
            left = level[idx]
            right = level[idx + 1] if idx + 1 < len(level) else level[idx]
            next_level.append(hashlib.sha256(left + right).digest())
        level = next_level
    return level[0].hex()


def _check_files_exist() -> Dict[str, Any]:
    missing = [str(path) for path in REQUIRED_FILES if not path.exists()]
    if missing:
        return {"status": "fail", "detail": f"Missing artefacts: {', '.join(missing)}"}
    return {"status": "ok", "detail": "All required artefacts present"}


def _check_merkle_consistency(batch: Dict[str, Any]) -> Dict[str, Any]:
    leaves = batch.get("leaves")
    if not isinstance(leaves, list):
        return {"status": "fail", "detail": "Batch must include leaf hashes"}
    try:
        recomputed = _compute_merkle([str(leaf) for leaf in leaves])
    except ValueError as exc:
        return {"status": "fail", "detail": f"Invalid leaf encoding: {exc}"}
    if recomputed != batch.get("merkle_root"):
        return {"status": "fail", "detail": "Merkle root mismatch"}
    return {"status": "ok", "detail": "Merkle root matches leaves"}


def _check_proof(proof: Dict[str, Any], batch: Dict[str, Any]) -> Dict[str, Any]:
    if proof.get("latest_root") != batch.get("merkle_root"):
        return {"status": "fail", "detail": "Proof root does not match batch"}
    if proof.get("ts") != batch.get("batch_ts"):
        return {"status": "fail", "detail": "Proof timestamp does not match batch"}
    return {"status": "ok", "detail": "Append-only proof aligned"}


def _check_signature(batch: Dict[str, Any]) -> Dict[str, Any]:
    try:
        verify_signature(SIGNATURE_PATH, KEYSTORE_PATH, BATCH_PATH)
    except VerificationError as exc:
        return {"status": "fail", "detail": f"Signature verification failed: {exc}"}
    return {"status": "ok", "detail": "Signature verified"}


def _microbench_normalizer() -> Dict[str, Any]:
    from services.oracle.normalizer.normalizer import build_event

    base = {
        "title": "Evento base",
        "lang": "pt",
        "category": "mercado",
        "source": "operador",
        "observed_at": "2025-10-29T18:59:00Z",
        "payload": {"valor": 1},
    }
    durations: List[float] = []
    for idx in range(1000):
        raw = dict(base)
        raw["title"] = f"{base['title']} {idx}"
        start = time.perf_counter()
        build_event(raw, now=datetime(2025, 10, 29, 19, 10, tzinfo=timezone.utc))
        durations.append(time.perf_counter() - start)
    durations.sort()
    p95_index = max(0, math.ceil(0.95 * len(durations)) - 1)
    p95_ms = durations[p95_index] * 1000
    detail = f"p95={p95_ms:.3f}ms"
    if p95_ms > 150:
        return {"status": "fail", "detail": detail}
    return {"status": "ok", "detail": detail}


def _check_keystore_window() -> Dict[str, Any]:
    data = _load_json(KEYSTORE_PATH)
    keys = data.get("keys")
    now = datetime.now(timezone.utc)
    if not isinstance(keys, list):
        return {"status": "fail", "detail": "Keystore missing keys list"}
    for key in keys:
        if key.get("status") != "active":
            continue
        created = datetime.fromisoformat(key["created_at"].replace("Z", "+00:00")).astimezone(timezone.utc)
        not_after = datetime.fromisoformat(key["not_after"].replace("Z", "+00:00")).astimezone(timezone.utc)
        if not (created <= now <= not_after):
            continue
        if (not_after - created).days > 90:
            return {"status": "fail", "detail": "Active key exceeds 90-day validity"}
        return {"status": "ok", "detail": f"Active key {key['kid']} valid"}
    return {"status": "fail", "detail": "No active key within validity window"}


def main() -> int:
    checks: List[Dict[str, Any]] = []

    presence = _check_files_exist()
    checks.append({"name": "artefacts_present", **presence})
    if presence["status"] == "fail":
        report = {"all_ok": False, "checks": checks}
        REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REPORT_PATH.write_text(json.dumps(report, indent=2))
        CI_REPORT_PATH.write_text(json.dumps(report, indent=2))
        print(presence["detail"])
        return 1

    batch = _load_json(BATCH_PATH)
    proof = _load_json(PROOF_PATH)

    checks.append({"name": "merkle_consistency", **_check_merkle_consistency(batch)})
    checks.append({"name": "proof_alignment", **_check_proof(proof, batch)})
    checks.append({"name": "signature_verification", **_check_signature(batch)})
    checks.append({"name": "keystore_window", **_check_keystore_window()})
    checks.append({"name": "normalizer_microbench", **_microbench_normalizer()})

    all_ok = all(item["status"] == "ok" for item in checks)
    report = {"all_ok": all_ok, "checks": checks}

    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(json.dumps(report, indent=2))
    CI_REPORT_PATH.write_text(json.dumps(report, indent=2))

    if not all_ok:
        for item in checks:
            if item["status"] != "ok":
                print(f"[FAIL] {item['name']}: {item['detail']}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
