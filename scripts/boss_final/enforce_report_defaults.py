#!/usr/bin/env python3
import json
import sys
from pathlib import Path

ALLOWED_STAGE_KEYS = {"status", "notes", "variants"}
ALLOWED_VARIANT_KEYS = {"status", "notes"}
STATUS_MAP = {
    "PASS": "PASS",
    "PASSED": "PASS",
    "pass": "PASS",
    "passed": "PASS",
    "Pass": "PASS",
    "FAIL": "FAIL",
    "FAILED": "FAIL",
    "fail": "FAIL",
    "failed": "FAIL",
    "Fail": "FAIL",
    "SKIP": "SKIP",
    "SKIPPED": "SKIP",
    "skip": "SKIP",
    "skipped": "SKIP",
    "Skip": "SKIP",
}
PRIMARY = "primary"


def nstatus(x):
    if x is None:
        return None
    s = str(x).strip()
    return STATUS_MAP.get(s, s.upper()) if s else None


def as_notes(x):
    return x if isinstance(x, str) else ""


def norm_variant(vd, fallback):
    out = {}
    if isinstance(vd, dict):
        st = nstatus(vd.get("status")) or fallback or "FAIL"
        for k, v in vd.items():
            if k in ALLOWED_VARIANT_KEYS:
                out[k] = v
        out["status"] = st
    else:
        out["status"] = fallback or "FAIL"
    out["notes"] = as_notes(out.get("notes"))
    return out


def norm_stage(v):
    if isinstance(v, str):
        st = nstatus(v) or "FAIL"
        return {
            "status": st,
            "notes": "",
            "variants": {PRIMARY: {"status": st, "notes": ""}},
        }
    if isinstance(v, dict):
        st_top = nstatus(v.get("status"))
        notes = as_notes(v.get("notes"))
        variants_in = v.get("variants") if isinstance(v.get("variants"), dict) else {}
        out_variants = {
            name: norm_variant(vd, st_top) for name, vd in variants_in.items()
        }
        if PRIMARY not in out_variants:
            out_variants[PRIMARY] = {"status": st_top or "FAIL", "notes": ""}
        st_final = nstatus(out_variants[PRIMARY].get("status")) or "FAIL"
        return {"status": st_final, "notes": notes, "variants": out_variants}
    return {
        "status": "FAIL",
        "notes": "",
        "variants": {PRIMARY: {"status": "FAIL", "notes": ""}},
    }


def apply_all(data: dict) -> dict:
    if not isinstance(data, dict):
        return data
    stages = data.get("stages")
    if isinstance(stages, dict):
        new_stages = {}
        for k, v in stages.items():
            st_obj = norm_stage(v)
            cleaned = {kk: st_obj[kk] for kk in ALLOWED_STAGE_KEYS}
            fixed = {}
            for name, vd in cleaned["variants"].items():
                c = {kk: vd.get(kk) for kk in ALLOWED_VARIANT_KEYS}
                c["status"] = nstatus(c.get("status")) or "FAIL"
                c["notes"] = as_notes(c.get("notes"))
                fixed[name] = c
            cleaned["variants"] = fixed
            cleaned["notes"] = as_notes(cleaned.get("notes"))
            new_stages[k] = cleaned
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
    # espelhos temporários do agregador
    for p in Path(".").rglob("report.json"):
        if "/_temp/boss-aggregate/" in str(p.resolve()):
            candidates.append(p)
    seen = set()
    out = []
    for c in candidates:
        try:
            rp = c.resolve()
            if rp in seen:
                continue
            if c.is_file():
                seen.add(rp)
                out.append(c)
        except Exception:
            pass
    return out


def main():
    targets = resolve_targets(sys.argv[1] if len(sys.argv) > 1 else None)
    if not targets:
        print("[enforce] nenhum report.json encontrado", file=sys.stderr)
        sys.exit(0)
    for t in targets:
        try:
            data = json.loads(t.read_text(encoding="utf-8", errors="ignore"))
        except Exception as e:
            print(f"[enforce] JSON inválido em {t}: {e}", file=sys.stderr)
            continue
        fixed = apply_all(data)
        t.write_text(
            json.dumps(fixed, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print(f"[enforce] normalizado: {t}")
    print("[enforce] DONE")


if __name__ == "__main__":
    main()
