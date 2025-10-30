#!/usr/bin/env python3
"""Audit reusable workflow contracts and invocations."""
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional

try:
    import yaml
except ModuleNotFoundError as exc:  # pragma: no cover - dependency gate
    raise SystemExit(
        "PyYAML is required to audit workflows. Install with 'pip install pyyaml'."
    ) from exc

WORKFLOW_DIR = Path(".github/workflows")
REPORT_PATH = Path("out/reports/validation/ci_refactor_report.json")
RESERVED_SECRET_NAMES = {"GITHUB_TOKEN"}


@dataclass(frozen=True)
class WorkflowContract:
    path: Path
    has_workflow_call: bool
    inputs: Dict[str, Mapping[str, Any]]
    secrets: Dict[str, Mapping[str, Any]]


@dataclass(frozen=True)
class WorkflowInputs:
    path: Path
    has_workflow_call: bool
    inputs: Dict[str, Mapping[str, Any]]


def _load_yaml(path: Path) -> Mapping[str, Any]:
    data = yaml.safe_load(path.read_text())
    if not isinstance(data, Mapping):
        return {}
    return data


def _workflow_contract(path: Path, cfg: Mapping[str, Any]) -> WorkflowContract:
def _workflow_inputs(path: Path, cfg: Mapping[str, Any]) -> WorkflowInputs:
    on_section = cfg.get("on", {})
    workflow_call: Optional[Mapping[str, Any]] = None
    if isinstance(on_section, Mapping):
        workflow_call = on_section.get("workflow_call")
    has_call = isinstance(workflow_call, Mapping)
    inputs: Dict[str, Mapping[str, Any]] = {}
    secrets: Dict[str, Mapping[str, Any]] = {}
    if has_call and isinstance(workflow_call, Mapping):
        raw_inputs = workflow_call.get("inputs", {})
        if isinstance(raw_inputs, Mapping):
            inputs = {
                str(name): meta if isinstance(meta, Mapping) else {}
                for name, meta in raw_inputs.items()
            }
        raw_secrets = workflow_call.get("secrets", {})
        if isinstance(raw_secrets, Mapping):
            secrets = {
                str(name): meta if isinstance(meta, Mapping) else {}
                for name, meta in raw_secrets.items()
            }
    return WorkflowContract(path=path, has_workflow_call=has_call, inputs=inputs, secrets=secrets)
    return WorkflowInputs(path=path, has_workflow_call=has_call, inputs=inputs)


def _iter_local_calls(cfg: Mapping[str, Any]) -> Iterable[Dict[str, Any]]:
    jobs = cfg.get("jobs", {})
    if not isinstance(jobs, Mapping):
        return []

    for job_name, job_cfg in jobs.items():
        if not isinstance(job_cfg, Mapping):
            continue
        job_uses = job_cfg.get("uses")
        if isinstance(job_uses, str) and job_uses.startswith("./.github/workflows/"):
            yield {
                "job": str(job_name),
                "step": None,
                "uses": job_uses,
                "with": job_cfg.get("with") if isinstance(job_cfg.get("with"), Mapping) else {},
            }
        steps = job_cfg.get("steps", [])
        if not isinstance(steps, list):
            continue
        for step in steps:
            if not isinstance(step, Mapping):
                continue
            step_uses = step.get("uses")
            if isinstance(step_uses, str) and step_uses.startswith("./.github/workflows/"):
                yield {
                    "job": str(job_name),
                    "step": str(step.get("name") or "<unnamed>"),
                    "uses": step_uses,
                    "with": step.get("with") if isinstance(step.get("with"), Mapping) else {},
                }


def _list_workflow_files() -> List[Path]:
    yml = list(WORKFLOW_DIR.glob("*.yml"))
    yaml_files = list(WORKFLOW_DIR.glob("*.yaml"))
    return sorted(set(yml + yaml_files))


def _normalise_key(path: Path) -> str:
    return f"./{path.as_posix()}"


def main() -> None:
    workflows = _list_workflow_files()
    inputs_index: Dict[str, WorkflowContract] = {}
    for path in workflows:
        cfg = _load_yaml(path)
        inputs_index[_normalise_key(path)] = _workflow_contract(path, cfg)
    inputs_index: Dict[str, WorkflowInputs] = {}
    for path in workflows:
        cfg = _load_yaml(path)
        inputs_index[_normalise_key(path)] = _workflow_inputs(path, cfg)

    report: Dict[str, Any] = {
        "workflows": [],
        "calls": [],
        "summary": {
            "workflow_total": len(workflows),
            "workflow_without_call": 0,
            "workflow_with_reserved_secrets": 0,
            "call_total": 0,
            "call_with_unknown_inputs": 0,
            "call_missing_required_inputs": 0,
            "call_missing_workflow": 0,
        },
    }

    for wf in workflows:
        info = inputs_index[_normalise_key(wf)]
        reserved = sorted(name for name in info.secrets if name in RESERVED_SECRET_NAMES)
        if reserved:
            report["summary"]["workflow_with_reserved_secrets"] += 1
        report["workflows"].append(
            {
                "path": info.path.as_posix(),
                "has_workflow_call": info.has_workflow_call,
                "inputs": [
                    {
                        "name": name,
                        "required": bool(meta.get("required", False)),
                        "type": meta.get("type"),
                        "default_provided": "default" in meta,
                    }
                    for name, meta in sorted(info.inputs.items())
                ],
                "secrets": [
                    {
                        "name": name,
                        "required": bool(meta.get("required", False)),
                        "reserved": name in RESERVED_SECRET_NAMES,
                    }
                    for name, meta in sorted(info.secrets.items())
                ],
                "reserved_secrets": reserved,
            }
        )
        if not info.has_workflow_call:
            report["summary"]["workflow_without_call"] += 1

    for wf in workflows:
        cfg = _load_yaml(wf)
        for call in _iter_local_calls(cfg):
            callee_key = call["uses"]
            provided_inputs = sorted(call.get("with", {}).keys())
            missing_required: List[str] = []
            unknown_inputs: List[str] = []
            callee_info = inputs_index.get(callee_key)
            if callee_info is None:
                report["summary"]["call_missing_workflow"] += 1
            else:
                for input_name, meta in callee_info.inputs.items():
                    if bool(meta.get("required", False)) and input_name not in call.get("with", {}):
                        missing_required.append(input_name)
                for input_name in provided_inputs:
                    if input_name not in callee_info.inputs:
                        unknown_inputs.append(input_name)
                if missing_required:
                    report["summary"]["call_missing_required_inputs"] += 1
                if unknown_inputs:
                    report["summary"]["call_with_unknown_inputs"] += 1
            report_entry = {
                "caller": wf.as_posix(),
                "job": call["job"],
                "step": call["step"],
                "callee": callee_key,
                "provided_inputs": provided_inputs,
                "missing_required_inputs": missing_required,
                "unknown_inputs": unknown_inputs,
                "status": "ok",
            }
            if callee_info is None:
                report_entry["status"] = "missing_workflow"
            elif missing_required or unknown_inputs:
                report_entry["status"] = "needs_alignment"
            report["calls"].append(report_entry)
            report["summary"]["call_total"] += 1

    failure_reasons: List[str] = []
    summary = report["summary"]
    if summary["workflow_with_reserved_secrets"]:
        reserved_names = ", ".join(sorted(summary["reserved_secret_names"]))
        failure_reasons.append(
            "reserved_secrets" + (f" ({reserved_names})" if reserved_names else "")
        )
    if summary["call_with_unknown_inputs"]:
        failure_reasons.append("unknown_inputs")
    if summary["call_missing_required_inputs"]:
        failure_reasons.append("missing_required_inputs")
    if summary["call_missing_workflow"]:
        failure_reasons.append("missing_workflow")

    if failure_reasons:
        summary["status"] = "needs_attention"
        summary["failure_reasons"] = failure_reasons

    summary["reserved_secret_names"] = sorted(set(summary["reserved_secret_names"]))

    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(json.dumps(report, indent=2, sort_keys=True))
    print(f"audit report written to {REPORT_PATH.as_posix()}")

    if failure_reasons:
        print(
            "workflow audit detected contract issues: "
            + ", ".join(failure_reasons),
            file=sys.stderr,
        )
        raise SystemExit(1)


if __name__ == "__main__":
    main()
