#!/usr/bin/env python3
import os, sys, re, json, shutil, subprocess, time
from pathlib import Path

try:
    import yaml  # PyYAML
except Exception:
    print("[guard] Installing PyYAML==6.0.2 ...", flush=True)
    subprocess.run([sys.executable, "-m", "pip", "install", "PyYAML==6.0.2"], check=True)
    import yaml

try:
    import jsonschema
except Exception:
    print("[guard] Installing jsonschema==4.23.0 ...", flush=True)
    subprocess.run([sys.executable, "-m", "pip", "install", "jsonschema==4.23.0"], check=True)
    import jsonschema

BASE = Path(os.environ.get("SPRINT_DIR", ".sprint"))
SCHEMAS = BASE / "schemas"
OUT = Path("out")
EVID = OUT / "evidence"
SCORE = OUT / "scorecards"
EVID.mkdir(parents=True, exist_ok=True)
SCORE.mkdir(parents=True, exist_ok=True)

def load_yaml(p: Path):
    with p.open("r", encoding="utf-8") as f:
        return yaml.safe_load(f)

def validate_schema(doc, schema_path: Path, name: str):
    schema = load_yaml(schema_path)
    jsonschema.validate(doc, schema)
    print(f"[guard] schema OK for {name}")

def check_filemap(filemap):
    ok = True
    for f in filemap["files"]:
        p = Path(f["path"])
        must = f.get("must_exist", True)
        if must and not p.exists():
            print(f"[guard] MISSING: {p} — {f['purpose']}")
            ok = False
    return ok

def run_cmd(cmd: str, evid_dir: Path, fname: str = "logs.txt", timeout=1800):
    evid_dir.mkdir(parents=True, exist_ok=True)
    print(f"[guard] RUN: {cmd}")
    proc = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, text=True, executable="/bin/bash")
    out = proc.stdout
    (evid_dir / fname).write_text(out, encoding="utf-8")
    return proc.returncode, out

def check_pins():
    # Simple pin checker looking for actions/* under .github/workflows with @<sha>
    # Uses actions.lock mapping if present.
    lock = {}
    lock_path = Path("actions.lock")
    if lock_path.exists():
        for line in lock_path.read_text().splitlines():
            parts = line.strip().split("#")[0].strip()
            if not parts: continue
            k,v = parts.split(None, 1) if " " in parts else (parts, "")
            # Expect format: KEY=SHA or like CHK=11bd..
            if "=" in parts:
                k, v = parts.split("=", 1)
                lock[k.strip()] = v.strip()
    # scan workflows
    pat = re.compile(r"uses:\s*([A-Za-z0-9_\-./]+)/([A-Za-z0-9_\-./]+)@([A-Za-z0-9._\-]+)")
    missing = []
    for wf in Path(".github/workflows").glob("*.yml"):
        txt = wf.read_text(encoding="utf-8")
        for m in pat.finditer(txt):
            full = f"{m.group(1)}/{m.group(2)}@{m.group(3)}"
            tag = m.group(3)
            # require a SHA-like (>= 30 hex chars) not vN
            if not re.fullmatch(r"[0-9a-f]{30,}", tag):
                missing.append((str(wf), full))
    report = {"missing_sha_refs": missing, "lock_keys": sorted(list(lock.keys()))}
    (EVID / "T2_pins").mkdir(parents=True, exist_ok=True)
    (EVID / "T2_pins" / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    if missing:
        print("[guard] PINS:FAIL")
        return False
    print("[guard] PINS:OK")
    return True

def main(argv):
    if len(argv) > 1 and argv[1] == "check-pins":
        ok = check_pins()
        sys.exit(0 if ok else 2)

    deliver = load_yaml(BASE / "deliverables.yml")
    gates = load_yaml(BASE / "gates.yml")
    fmap = load_yaml(BASE / "filemap.yml")

    # Validate schemas
    validate_schema(deliver, SCHEMAS / "deliverables.schema.yaml", "deliverables")
    validate_schema(gates, SCHEMAS / "gates.schema.yaml", "gates")
    validate_schema(fmap, SCHEMAS / "filemap.schema.yaml", "filemap")

    # Filemap check
    fmap_ok = check_filemap(fmap)

    # Run gates
    results = []
    all_ok = fmap_ok
    for g in gates["gates"]:
        gid = g["id"]
        evid_dir = EVID / f"{gid}_{re.sub(r'[^A-Za-z0-9]+','_',g['name']).lower()}"
        ok = True
        logs = []
        for cmd in g.get("run", []):
            rc, out = run_cmd(cmd, evid_dir, fname="logs.txt")
            logs.append(out)
            if rc != 0:
                ok = False
        # pattern asserts
        if ok and g.get("assert_patterns"):
            combined = "\n".join(logs)
            for pat in g["assert_patterns"]:
                if not re.search(pat, combined, re.M):
                    ok = False
                    print(f"[guard] ASSERT MISS: {gid} pattern {pat}")
        # evidence presence
        for ev in g.get("evidence", []):
            path = Path(ev["path"])
            if ev.get("must_exist", True) and not path.exists():
                ok = False
                print(f"[guard] MISSING EVIDENCE: {path}")
        results.append({"id": gid, "name": g["name"], "ok": ok})
        all_ok = all_ok and ok

    # Write scorecard
    SCORE.mkdir(parents=True, exist_ok=True)
    score = {
        "sprint": deliver.get("sprint_name", ""),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "filemap_ok": fmap_ok,
        "gates": results,
        "ok": all_ok
    }
    (SCORE / "sprint_guard_scorecard.json").write_text(json.dumps(score, indent=2), encoding="utf-8")
    print(json.dumps(score, indent=2))
    sys.exit(0 if all_ok else 1)

if __name__ == "__main__":
    main(sys.argv)
