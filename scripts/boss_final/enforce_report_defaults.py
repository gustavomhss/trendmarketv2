#!/usr/bin/env python3
import json, sys
from pathlib import Path

# Normaliza status e estrutura dos stages para o schema v2 (PASS|FAIL|SKIP + variants.primary)
ALLOWED_TOP = {
    "status"
}  # preservamos demais campos top-level sem tocar (schema, v, ts etc.)
ALLOWED_STAGE_KEYS = {"status", "notes", "variants"}
ALLOWED_VARIANT_KEYS = {"status", "notes"}
ST_ALLOWED = {"PASS", "FAIL", "SKIP"}
MAP = {
    "PASSED": "PASS",
    "passed": "PASS",
    "Pass": "PASS",
    "PASS": "PASS",
    "FAILED": "FAIL",
    "failed": "FAIL",
    "Fail": "FAIL",
    "FAIL": "FAIL",
    "SKIPPED": "SKIP",
    "skipped": "SKIP",
    "Skip": "SKIP",
    "SKIP": "SKIP",
}
PRIMARY = "primary"


def nstatus(x):
    if x is None:
        return None
    s = str(x).strip()
    s = MAP.get(s, s.upper())
    return s if s in ST_ALLOWED else None


def as_notes(x):
    return x if isinstance(x, str) else ""


def norm_variant(vd, fallback):
    out = {}
    if isinstance(vd, dict):
        st = nstatus(vd.get("status")) or fallback
        for k, val in vd.items():
            if k in ALLOWED_VARIANT_KEYS:
                out[k] = val
        out["status"] = st
    else:
        out["status"] = fallback
    return out


def norm_stage(v):
    # string -> stage simples
    if isinstance(v, str):
        st = nstatus(v) or "FAIL"
        return {"status": st, "notes": "", "variants": {PRIMARY: {"status": st}}}
    # dict -> limpar chaves e normalizar
    if isinstance(v, dict):
        st = nstatus(v.get("status"))
        variants_in = v.get("variants") if isinstance(v.get("variants"), dict) else {}
        prim_in = (
            variants_in.get(PRIMARY)
            if isinstance(variants_in.get(PRIMARY), dict)
            else {}
        )
        prim_st = nstatus(prim_in.get("status")) or st or "FAIL"
        out = {
            "status": st or prim_st,
            "notes": as_notes(v.get("notes")),
            "variants": {},
        }
        # normaliza todas as variants presentes
        for name, vd in variants_in.items():
            if isinstance(vd, dict):
                out["variants"][name] = norm_variant(vd, out["status"])
        # garante primary
        if PRIMARY not in out["variants"]:
            out["variants"][PRIMARY] = {"status": out["status"]}
        # strip extras no nível do stage
        return {k: out[k] for k in ALLOWED_STAGE_KEYS}
    # tipo inválido -> fallback
    return {"status": "FAIL", "notes": "", "variants": {PRIMARY: {"status": "FAIL"}}}


def apply_defaults_and_normalize(data: dict) -> dict:
    # top-level status (opcional)
    if "status" in data:
        ns = nstatus(data["status"])
        if ns:
            data["status"] = ns
    # stages
    stages = data.get("stages")
    if isinstance(stages, dict):
        new_stages = {}
        for k, v in stages.items():
            st_obj = norm_stage(v)
            # garantir notes presente
            st_obj["notes"] = as_notes(st_obj.get("notes"))
            new_stages[k] = st_obj
        data["stages"] = new_stages
    return data


def resolve_target(cli_arg: str | None) -> Path | None:
    # Ordem de procura se não foi passado caminho
    candidates = [
        Path("out/boss_final/report.local.json"),
        Path("out/boss_final/report.json"),
        Path("out/summary/report.json"),
        Path("out/report.json"),
    ]
    if cli_arg:
        p = Path(cli_arg)
        return p if p.is_file() else None
    for c in candidates:
        if c.is_file():
            return c
    return None


def main():
    target = resolve_target(sys.argv[1] if len(sys.argv) > 1 else None)
    if not target:
        print("[enforce] nenhum report.json encontrado", file=sys.stderr)
        sys.exit(0)

    raw = target.read_text(encoding="utf-8", errors="ignore")
    try:
        data = json.loads(raw)
    except Exception as e:
        print(f"[enforce] JSON inválido em {target}: {e}", file=sys.stderr)
        sys.exit(1)

    if not isinstance(data, dict):
        print(f"[enforce] objeto raiz não é dict em {target}", file=sys.stderr)
        sys.exit(1)

    data = apply_defaults_and_normalize(data)
    target.write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"[enforce] defaults+normalize aplicados em {target}")


if __name__ == "__main__":
    main()
