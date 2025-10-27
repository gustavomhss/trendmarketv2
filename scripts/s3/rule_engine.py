#!/usr/bin/env python3
"""Rule engine evaluator for Sprint 3 gatecheck."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from _telemetry import AuditLog, TelemetryEmitter, ensure_evidence_dir  # noqa: E402
from _yaml import load as yaml_load  # noqa: E402

RULES_PATH = Path(os.getenv("MBP_RULES_FILE", "configs/rulesets/v1/rules.yml"))
SEEDS_DEFAULT = Path(os.getenv("MBP_RULE_SEEDS", "seeds/engine/rule_seeds.json"))
EVIDENCE = ensure_evidence_dir()
RULE_EVAL_PATH = EVIDENCE / "rule_eval.json"
RULE_POLICY_HASH_PATH = EVIDENCE / "rule_policy_hash.txt"
APPROVALS_PATH = EVIDENCE / "rule_manual_approvals.jsonl"
TELEMETRY = TelemetryEmitter("rule_engine")
AUDIT = AuditLog("rule_engine")


@dataclass
class Rule:
    id: str
    source_kind: str
    config: Dict[str, Any]

    @classmethod
    def from_yaml(cls, raw: Dict[str, Any]) -> "Rule":
        cfg = raw.copy()
        return cls(
            id=str(cfg.pop("id")), source_kind=str(cfg.pop("source_kind")), config=cfg
        )


class Ruleset:
    def __init__(self, rules: Iterable[Rule], fallback: Dict[str, Any]) -> None:
        self._rules = {rule.id: rule for rule in rules}
        self.fallback = fallback or {}

    def get(self, rule_id: str) -> Rule:
        if rule_id not in self._rules:
            raise ValueError(f"unknown rule id {rule_id}")
        return self._rules[rule_id]


def load_rules(path: Path = RULES_PATH) -> Ruleset:
    raw = yaml_load(path) or {}
    rule_objs = [Rule.from_yaml(r) for r in raw.get("rules", [])]
    fallback = raw.get("fallback", {})
    RULE_POLICY_HASH_PATH.write_text(
        hashlib.sha256(path.read_bytes()).hexdigest() + "\n", encoding="utf-8"
    )
    return Ruleset(rule_objs, fallback)


def deterministic_hash(*parts: Any) -> str:
    encoded = json.dumps(parts, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def evaluate_table(rule: Rule, payload: Dict[str, Any]) -> Dict[str, Any]:
    seeds_dir = Path(os.getenv("MBP_RULE_SEEDS_DIR", "seeds"))
    table_name = rule.config["table"]
    field_q = rule.config.get("field_question", "question_id")
    field_a = rule.config.get("field_answer", "resolved_value")
    csv_path = seeds_dir / f"{table_name}.csv"
    if not csv_path.exists():
        raise FileNotFoundError(f"missing table seed {csv_path}")
    key = str(payload.get(field_q))
    with csv_path.open("r", encoding="utf-8") as fp:
        reader = csv.DictReader(fp)
        for row in reader:
            if str(row.get(field_q)) == key:
                return {
                    "status": "ok",
                    "value": row.get(field_a),
                    "evidence": row.get("evidence_uri"),
                    "resolution_window_h": rule.config.get("resolution_window_h"),
                }
    return {"status": "not_found"}


def evaluate_endpoint(rule: Rule, payload: Dict[str, Any]) -> Dict[str, Any]:
    # Deterministic stub based on hash of context
    salt = rule.config.get("url", "endpoint")
    digest = deterministic_hash(rule.id, salt, payload)
    score = int(digest[:8], 16) / 0xFFFFFFFF
    return {
        "status": "ok",
        "value": round(score, 6),
        "resolution_window_h": rule.config.get("resolution_window_h"),
    }


def manual_fallback(
    rule: Rule, payload: Dict[str, Any], seed: Dict[str, Any]
) -> Dict[str, Any]:
    manual = seed.get("manual") or {}
    approver = manual.get("approver")
    ticket = manual.get("ticket")
    if not approver or not ticket:
        raise ValueError(
            f"manual fallback requires approver and ticket (rule {rule.id})"
        )
    approval_record = {
        "rule_id": rule.id,
        "approver": approver,
        "ticket": ticket,
        "payload": payload,
    }
    with APPROVALS_PATH.open("a", encoding="utf-8") as fp:
        fp.write(json.dumps(approval_record, ensure_ascii=False) + "\n")
    AUDIT.append(
        {
            "event": "manual_fallback",
            "rule_id": rule.id,
            "approver": approver,
            "ticket": ticket,
            "payload": payload,
        }
    )
    return {"status": "manual", "approver": approver, "ticket": ticket}


def evaluate_rule(
    rule: Rule, payload: Dict[str, Any], seed: Dict[str, Any]
) -> Dict[str, Any]:
    if rule.source_kind == "table":
        result = evaluate_table(rule, payload)
        if result.get("status") == "ok":
            return result
        return manual_fallback(rule, payload, seed)
    if rule.source_kind == "endpoint":
        return evaluate_endpoint(rule, payload)
    if rule.source_kind == "manual":
        return manual_fallback(rule, payload, seed)
    raise ValueError(f"unsupported source_kind {rule.source_kind}")


def evaluate_seeds(
    ruleset: Ruleset, seeds: Iterable[Dict[str, Any]]
) -> List[Dict[str, Any]]:
    evaluations: List[Dict[str, Any]] = []
    for seed in seeds:
        rule_id = seed["rule_id"]
        payload = seed.get("payload", {})
        rule = ruleset.get(rule_id)
        result = evaluate_rule(rule, payload, seed)
        trace = TELEMETRY.emit(
            "rule.eval",
            {
                "rule_id": rule_id,
                "status": result.get("status"),
            },
        )
        evaluations.append(
            {
                "rule_id": rule_id,
                "result": result,
                "trace_id": trace["trace_id"],
            }
        )
    RULE_EVAL_PATH.write_text(
        json.dumps(evaluations, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    return evaluations


def load_seeds(path: Optional[Path]) -> List[Dict[str, Any]]:
    if path is None:
        path = SEEDS_DEFAULT
    if not path.exists():
        return []
    return json.loads(path.read_text(encoding="utf-8"))


def cli(argv: Optional[Iterable[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Evaluate rule seeds for S3 gatecheck")
    parser.add_argument("command", choices=["evaluate"], help="Command to execute")
    parser.add_argument(
        "seed_file", nargs="?", help="JSON file with seeds", default=str(SEEDS_DEFAULT)
    )
    args = parser.parse_args(argv)

    if args.command == "evaluate":
        seeds = load_seeds(Path(args.seed_file))
        ruleset = load_rules()
        evaluate_seeds(ruleset, seeds)
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(cli())
