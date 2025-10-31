#!/usr/bin/env python3
import os, sys, json, textwrap
from pathlib import Path

try:
    import yaml
except Exception:
    import subprocess, sys as _sys
    subprocess.run([_sys.executable, "-m", "pip", "install", "PyYAML==6.0.2"], check=True)
    import yaml

BASE = Path(os.environ.get("SPRINT_DIR", ".sprint"))
OUT = Path("docs/Storyboard.md")

def load(p):
    with open(p, "r", encoding="utf-8") as f:
        return yaml.safe_load(f)

def main():
    d = load(BASE / "deliverables.yml")
    g = load(BASE / "gates.yml")
    f = load(BASE / "filemap.yml")

    lines = []
    lines.append(f"# Storyboard — {d.get('sprint_name','(sprint)')}")
    lines.append("")
    lines.append("## Deliverables (DbC)")
    for it in d["deliverables"]:
        lines.append(f"### {it['id']} — {it['title']}")
        lines.append(it.get("description","").strip())
        if it.get("require"):
            lines.append("**Require**: " + "; ".join(it["require"]))
        if it.get("ensure"):
            lines.append("**Ensure**: " + "; ".join(it["ensure"]))
        if it.get("invariants"):
            lines.append("**Invariants**: " + "; ".join(it["invariants"]))
        lines.append("")

    lines.append("## Gates")
    for it in g["gates"]:
        lines.append(f"### {it['id']} — {it['name']}")
        lines.append(it.get("purpose",""))
        if it.get("ltl"):
            lines.append(f"**LTL**: `{it['ltl']}`")
        if it.get("contracts"):
            c = it["contracts"]
            if c.get("require"): lines.append("**Require**: " + "; ".join(c["require"]))
            if c.get("ensure"): lines.append("**Ensure**: " + "; ".join(c["ensure"]))
        if it.get("run"):
            lines.append("**Run**:")
            for cmd in it["run"]:
                lines.append(f"- `{cmd}`")
        if it.get("evidence"):
            lines.append("**Evidence**:")
            for ev in it["evidence"]:
                lines.append(f"- `{ev['path']}`{' (optional)' if not ev.get('must_exist', True) else ''}")
        lines.append("")

    lines.append("## Filemap")
    for it in f["files"]:
        lines.append(f"- `{it['path']}` — {it['purpose']}")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {OUT}")

if __name__ == "__main__":
    main()
