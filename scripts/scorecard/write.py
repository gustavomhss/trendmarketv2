from __future__ import annotations

import argparse
import hashlib
import json
import string
from datetime import UTC, datetime
from pathlib import Path
from typing import Dict, Iterable, Mapping

DEFAULT_OUT = Path("out/scorecards/s7.json")
BATCH_PATH = Path("out/normalized/batch.json")
EVIDENCE_ROOT = Path("out")

GATE_EVIDENCE: Dict[str, Path] = {
    "T0": Path("out/evidence/T0_ruleset_sanity/ruleset_check.json"),
    "T1": Path("out/evidence/T1_yaml/filemap_check.json"),
    "T2": Path("out/evidence/T2_security/gitleaks_report.json"),
    "T3": Path("out/evidence/T3_pins/pins_report.json"),
    "T4": Path("out/evidence/T4_tests/pytest_report.json"),
    "T5": Path("out/evidence/T5_props/properties_summary.json"),
    "T6": Path("out/evidence/T6_determinism/hash_match.json"),
    "T7": Path("out/evidence/T7_append_only/append_only_report.json"),
    "T8": Path("out/evidence/T8_pack/verify.json"),
}

SLO_THRESHOLDS: Dict[str, Dict[str, int]] = {
    "T0": {"warn": 3000, "hard": 10000},
    "T1": {"warn": 5000, "hard": 15000},
    "T2": {"warn": 20000, "hard": 60000},
    "T3": {"warn": 5000, "hard": 15000},
    "T4": {"warn": 60000, "hard": 120000},
    "T5": {"warn": 90000, "hard": 180000},
    "T6": {"warn": 20000, "hard": 60000},
    "T7": {"warn": 5000, "hard": 15000},
    "T8": {"warn": 10000, "hard": 30000},
}

HEX_SET = set(string.hexdigits.lower())


def load_json(path: Path) -> Mapping:
    return json.loads(path.read_text(encoding="utf-8"))


def _sanitize_hex(value: object) -> str:
    if isinstance(value, str):
        lowered = value.lower()
        if len(lowered) == 64 and all(ch in HEX_SET for ch in lowered):
            return lowered
    return "0" * 64


def build_hashes(batch: Mapping) -> Dict[str, str]:
    hashes: Dict[str, str] = {
        "entries_hash": _sanitize_hex(batch.get("entries_hash")),
        "root": _sanitize_hex(batch.get("root")),
        "batch_sha256": "0" * 64,
        "evidence_zip": "0" * 64,
    }
    if BATCH_PATH.exists():
        hashes["batch_sha256"] = hashlib.sha256(BATCH_PATH.read_bytes()).hexdigest()
    zip_path = EVIDENCE_ROOT / "s7-evidence.zip"
    if zip_path.exists():
        hashes["evidence_zip"] = hashlib.sha256(zip_path.read_bytes()).hexdigest()
    return hashes


def _gate_duration(payload: Mapping) -> int:
    value = payload.get("duration_ms")
    if isinstance(value, (int, float)):
        return max(0, int(value))
    return 0


def _evaluate_pytest_report(payload: Mapping) -> bool:
    summary = payload.get("summary", {})
    if isinstance(summary, Mapping):
        failed = summary.get("failed", 0) or 0
        errors = summary.get("errors", 0) or 0
        return failed == 0 and errors == 0
    return bool(payload.get("ok", False))


def _evaluate_properties(payload: Mapping) -> bool:
    if not payload.get("ok", False):
        return False
    props = payload.get("properties", [])
    if isinstance(props, list):
        return all(isinstance(item, Mapping) and item.get("result") for item in props)
    return False


def _read_gate_result(gate: str, path: Path) -> Dict[str, object]:
    if not path.exists():
        return {"status": "pending", "duration_ms": 0}
    payload = load_json(path)
    duration = _gate_duration(payload)
    if gate == "T4":
        ok = _evaluate_pytest_report(payload)
    elif gate == "T5":
        ok = _evaluate_properties(payload)
    else:
        ok = bool(payload.get("ok", False))
    status = "pass" if ok else "fail"
    return {"status": status, "duration_ms": duration}


def build_gates() -> Dict[str, Dict[str, object]]:
    results: Dict[str, Dict[str, object]] = {}
    for gate in ["T0", "T1", "T2", "T3", "T4", "T5", "T6", "T7", "T8"]:
        path = GATE_EVIDENCE.get(gate)
        results[gate] = _read_gate_result(gate, path) if path else {"status": "pending", "duration_ms": 0}
    return results


def compute_slo_metrics(gates: Mapping[str, Mapping[str, object]]) -> Dict[str, int]:
    metrics = {
        "normalize": 0,
        "build_batch": 0,
        "merkle": 0,
        "sign": 0,
        "verify": 0,
        "append_guard": int(gates["T7"].get("duration_ms", 0)),
        "pack": int(gates["T8"].get("duration_ms", 0)),
        "total": 0,
    }
    normalize_metrics = EVIDENCE_ROOT / "metrics" / "normalize.json"
    if normalize_metrics.exists():
        data = load_json(normalize_metrics)
        value = data.get("normalize_elapsed_ms")
        if isinstance(value, (int, float)):
            metrics["normalize"] = int(value)
    metrics["total"] = sum(int(info.get("duration_ms", 0)) for info in gates.values())
    return metrics


def compute_gating(gates: Mapping[str, Mapping[str, object]]) -> Dict[str, object]:
    warnings: Dict[str, int] = {}
    hard_fail = False
    slo_violations: list[str] = []
    for gate, info in gates.items():
        duration = int(info.get("duration_ms", 0))
        thresholds = SLO_THRESHOLDS.get(gate)
        if thresholds:
            if duration > thresholds["hard"]:
                hard_fail = True
                slo_violations.append(f"{gate}_hard")
            elif duration > thresholds["warn"]:
                warnings[gate] = duration
                slo_violations.append(f"{gate}_warn")
        if info.get("status") == "fail":
            hard_fail = True
            if f"{gate}_fail" not in slo_violations:
                slo_violations.append(f"{gate}_fail")
    return {
        "warnings": warnings,
        "hard_fail": hard_fail,
        "slo_violations": slo_violations,
        "warn_count": len(warnings),
    }


def build_scorecard(commit_sha: str) -> Mapping:
    batch = load_json(BATCH_PATH) if BATCH_PATH.exists() else {}
    hashes = build_hashes(batch)
    gates = build_gates()
    gating_info = compute_gating(gates)
    now = datetime.now(tz=UTC)
    timestamp = now.isoformat(timespec="seconds").replace("+00:00", "Z")
    slo_metrics = compute_slo_metrics(gates)

    return {
        "sprint": "Q2-S7",
        "commit_sha": commit_sha,
        "started_at": timestamp,
        "finished_at": timestamp,
        "gates": gates,
        "hashes": hashes,
        "slo_p95_ms": slo_metrics,
        "warnings_by_gate": gating_info["warnings"],
        "waivers_by_gate": {},
        "slo_violations": gating_info["slo_violations"],
        "gating": {"hard_fail": gating_info["hard_fail"], "warn_count": gating_info["warn_count"]},
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Write Sprint 7 scorecard")
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--commit", default="0" * 40)
    args = parser.parse_args(list(argv) if argv is not None else None)

    scorecard = build_scorecard(args.commit)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(scorecard, separators=(",", ":")), encoding="utf-8")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
