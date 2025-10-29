#!/usr/bin/env python3
import json, sys, re
from pathlib import Path

ALLOWED_STAGE_KEYS = {"status","notes","variants"}
ALLOWED_VARIANT_KEYS = {"status","notes"}
STATUS_MAP = {
    "PASS":"PASS","PASSED":"PASS","pass":"PASS","passed":"PASS","Pass":"PASS",
    "FAIL":"FAIL","FAILED":"FAIL","fail":"FAIL","failed":"FAIL","Fail":"FAIL",
    "SKIP":"SKIP","SKIPPED":"SKIP","skip":"SKIP","skipped":"SKIP","Skip":"SKIP",
}
REQUIRED_VARIANTS = ("primary","clean")

def nstatus(x):
    if x is None: return None
    s = str(x).strip()
    return STATUS_MAP.get(s, s.upper()) if s else None

def as_notes(x): return x if isinstance(x,str) else ""

def norm_variant(vd, fallback):
    out = {}
    if isinstance(vd, dict):
        st = nstatus(vd.get("status")) or fallback or "FAIL"
        for k,v in vd.items():
            if k in ALLOWED_VARIANT_KEYS: out[k]=v
        out["status"]=st
    else:
        out["status"]=fallback or "FAIL"
    out["notes"]=as_notes(out.get("notes"))
    return out

def stage_from_scalar(v):
    st = nstatus(v) or "FAIL"
    base = {"status":st,"notes":"","variants":{"primary":{"status":st,"notes":""}}}
    base["variants"]["clean"] = {"status":st,"notes":""}
    return base

def norm_stage(v):
    if isinstance(v, str): return stage_from_scalar(v)
    if not isinstance(v, dict): return stage_from_scalar("FAIL")

    top_clean = v.get("clean", None)
    st_top = nstatus(v.get("status"))
    notes = as_notes(v.get("notes"))
    variants_in = v.get("variants") if isinstance(v.get("variants"), dict) else {}

    out_variants = {name: norm_variant(vd, st_top) for name, vd in variants_in.items()}

    for req in REQUIRED_VARIANTS:
        if req not in out_variants:
            if req == "clean" and isinstance(top_clean, (bool,str,int)):
                val = str(top_clean).lower() in {"1","true","yes","y","on"}
                out_variants[req] = {"status": "PASS" if val else (st_top or "FAIL"), "notes":""}
            else:
                out_variants[req] = {"status": (st_top or "FAIL"), "notes":""}

    st_final = nstatus(out_variants["primary"].get("status")) or "FAIL"

    cleaned = {
        "status": st_final,
        "notes": notes,
        "variants": {}
    }
    for name, vd in out_variants.items():
        c = {kk: vd.get(kk) for kk in ALLOWED_VARIANT_KEYS}
        c["status"] = nstatus(c.get("status")) or "FAIL"
        c["notes"] = as_notes(c.get("notes"))
        cleaned["variants"][name] = c
    return cleaned

def apply_all(data: dict) -> dict:
    if not isinstance(data, dict): return data
    stages = data.get("stages")
    if isinstance(stages, dict):
        new_stages = {}
        for k,v in stages.items():
            new_stages[k] = norm_stage(v)
        data["stages"] = new_stages
    return data

def resolve_targets(cli_arg):
    if cli_arg:
        p = Path(cli_arg)
        return [p] if p.is_file() else []
    candidates = [
        Path("out/boss_final/report.local.json"),
        Path("out/boss_final/report.json"),
        Path("out/summary/report.json"),
        Path("out/report.json"),
        Path("boss-final-report.json"),
    ]
    for p in Path(".").rglob("report.json"):
        s = str(p.resolve())
        if "/_temp/boss-aggregate/" in s or s.endswith("/boss-aggregate/report.json"):
            candidates.append(p)
    seen=set(); out=[]
    for c in candidates:
        try:
            rp = c.resolve()
            if rp in seen: continue
            if c.is_file(): seen.add(rp); out.append(c)
        except Exception:
            pass
    return out

def main():
    targets = resolve_targets(sys.argv[1] if len(sys.argv)>1 else None)
    if not targets:
        print("[enforce] nenhum report.json encontrado", file=sys.stderr); sys.exit(0)
    for t in targets:
        try:
            data = json.loads(t.read_text(encoding="utf-8", errors="ignore"))
        except Exception as e:
            print(f"[enforce] JSON inválido em {t}: {e}", file=sys.stderr); continue
        fixed = apply_all(data)
        t.write_text(json.dumps(fixed, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"[enforce] normalizado: {t}")
    print("[enforce] DONE")
if __name__ == "__main__": main()
