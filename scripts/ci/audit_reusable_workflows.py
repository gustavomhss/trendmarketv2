#!/usr/bin/env python3
from __future__ import annotations
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import yaml

WF_DIR = Path('.github/workflows')
REPORT = Path('out/reports/validation/ci_refactor_report.json')
REPORT.parent.mkdir(parents=True, exist_ok=True)

def load_yaml(p: Path) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    try:
        return yaml.safe_load(p.read_text(encoding='utf-8')), None
    except Exception as e:  # noqa: BLE001
        return None, f"{type(e).__name__}: {e}"

def find_local_uses(doc: Dict[str, Any]) -> List[str]:
    out: List[str] = []
    jobs = (doc or {}).get('jobs', {}) or {}
    for job in jobs.values():
        steps = (job or {}).get('steps', []) or []
        for st in steps:
            if isinstance(st, dict):
                uses = st.get('uses')
                if isinstance(uses, str) and uses.startswith('./.github/workflows/') and uses.endswith(('.yml', '.yaml')):
                    out.append(uses.replace('./.github/workflows/', ''))
    return out

def workflow_call_inputs(doc: Dict[str, Any]) -> Dict[str, str]:
    on = doc.get('on') or {}
    if isinstance(on, dict):
        wc = on.get('workflow_call')
        if isinstance(wc, dict):
            inputs = wc.get('inputs', {}) or {}
            out: Dict[str, str] = {}
            for k, v in inputs.items():
                if isinstance(v, dict):
                    t = v.get('type')
                    if isinstance(t, str):
                        out[k] = t
            return out
    return {}

summary: Dict[str, Any] = {"scanned": [], "missing_workflow_call": [], "unknown_inputs": [], "errors": []}

wf_docs: Dict[str, Optional[Dict[str, Any]]] = {}
for p in sorted(WF_DIR.glob('*.y*ml')):
    doc, err = load_yaml(p)
    wf_docs[p.name] = doc
    summary['scanned'].append(p.name)
    if err:
        summary['errors'].append({"file": p.name, "error": err})

decl_inputs: Dict[str, Dict[str, str]] = {name: workflow_call_inputs(doc or {}) for name, doc in wf_docs.items() if doc is not None}

for caller_name, caller_doc in wf_docs.items():
    if not isinstance(caller_doc, dict):
        continue
    callees = find_local_uses(caller_doc)
    caller_text = Path(WF_DIR / caller_name).read_text(encoding='utf-8', errors='ignore')
    for callee in callees:
        callee_doc = wf_docs.get(callee)
        if not isinstance(callee_doc, dict):
            summary['errors'].append({"file": caller_name, "error": f"callee_not_found:{callee}"})
            continue
        on = callee_doc.get('on') or {}
        if not (isinstance(on, dict) and 'workflow_call' in on):
            summary['missing_workflow_call'].append({"callee": callee, "used_by": caller_name})
        pat = re.compile(rf"uses:\s*\./\.github/workflows/{re.escape(callee)}\s*[\r\n]+(?:\s+with:\s*[\r\n]+(?P<body>(?:\s+.+\s*[\r\n]+)+))?", re.MULTILINE)
        for m in pat.finditer(caller_text):
            body = m.group('body') or ''
            passed = re.findall(r"^\s+([A-Za-z0-9_]+)\s*:", body, re.MULTILINE)
            if passed:
                known = set(decl_inputs.get(callee, {}).keys())
                unknown = sorted(set(passed) - known)
                if unknown:
                    summary['unknown_inputs'].append({"callee": callee, "used_by": caller_name, "unknown": unknown})

REPORT.write_text(json.dumps(summary, indent=2, ensure_ascii=False), encoding='utf-8')
print('[audit] wrote', REPORT)
