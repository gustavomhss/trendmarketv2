#!/usr/bin/env python3
import json
import pathlib
import re
import sys
from typing import Dict

try:  # Prefer PyYAML, fallback to bundled parser when unavailable
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - fallback path for minimal envs
    sys.path.append(str(pathlib.Path(__file__).resolve().parents[2]))
    import yaml_fallback as yaml  # type: ignore

ROOT = pathlib.Path(__file__).resolve().parents[2]
WF_DIR = ROOT / ".github" / "workflows"
OUT_DIR = ROOT / "out" / "guard" / "s4"
LOCK_PATH = OUT_DIR / "actions.lock.json"
REPORT = OUT_DIR / "actions_lock_report.json"

USES_RE = re.compile(
    r"^(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)@(?P<ref>[A-Za-z0-9_.-]+)$"
)
HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")


def parse_uses() -> Dict[str, str]:
    uses = {}
    for yml in sorted(WF_DIR.glob("*.yml")) + sorted(WF_DIR.glob("*.yaml")):
        with open(yml, "r", encoding="utf-8", errors="ignore") as f:
            try:
                doc = yaml.safe_load(f) or {}
            except Exception:
                continue
        for job in (doc.get("jobs") or {}).values():
            for step in job.get("steps") or []:
                u = (step or {}).get("uses")
                if not u:
                    continue
                s = str(u).strip()
                if s.startswith("./") or s.startswith("docker://"):
                    continue
                m = USES_RE.match(s)
                if not m:
                    continue
                uses[f"{m.group('owner')}/{m.group('repo')}"] = m.group("ref")
    return uses


def main() -> int:
    if not LOCK_PATH.exists():
        print("[verify-lock] lock ausente", file=sys.stderr)
        return 2
    lock = json.loads(LOCK_PATH.read_text("utf-8"))
    uses = parse_uses()
    report = {"ok": True, "mismatches": []}
    for key, ref in sorted(uses.items()):
        locked_entry = lock.get(key)
        if not locked_entry:
            report["ok"] = False
            report["mismatches"].append(
                {"key": key, "reason": "ausente_no_lock", "ref": ref}
            )
            continue
        sha = locked_entry.get("sha", "").lower()
        if HEX40_RE.match(ref):
            if ref.lower() != sha:
                report["ok"] = False
                report["mismatches"].append(
                    {
                        "key": key,
                        "reason": "sha_divergente",
                        "workflow": ref,
                        "lock": sha,
                    }
                )
        else:
            # quando por tag, aceitamos desde que o lock possua um sha válido
            if not sha:
                report["ok"] = False
                report["mismatches"].append(
                    {"key": key, "reason": "sha_vazio_no_lock", "ref": ref}
                )
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(f"[verify-lock] relatório em {REPORT}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
