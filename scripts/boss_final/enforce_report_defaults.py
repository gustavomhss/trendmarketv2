#!/usr/bin/env python3
import json, sys
from pathlib import Path

CANDIDATES = [
    Path("out/boss_final/report.local.json"),
    Path("out/boss_final/report.json"),
    Path("out/summary/report.json"),
    Path("out/report.json"),
]

DROP_KEYS = {"name", "clean", "exit_code"}
ALLOWED = {"PASS", "FAIL", "SKIP"}


def norm_status(s: str) -> str:
    t = (s or "").strip().lower()
    if t in {"pass", "passed", "ok", "success", "successful", "green", "aprovado"}:
        return "PASS"
    if t in {"fail", "failed", "error", "err", "broken", "red", "reprovado"}:
        return "FAIL"
    if t in {"skip", "skipped", "ignored", "noop", "na", "n/a"}:
        return "SKIP"
    u = (s or "").strip().upper()
    if u in {"PASSED", "PASS"}:
        return "PASS"
    if u in {"FAILED", "FAIL"}:
        return "FAIL"
    if u in {"SKIPPED", "SKIP"}:
        return "SKIP"
    return "FAIL"


def load_target() -> Path | None:
    p = Path((sys.argv[1] if len(sys.argv) > 1 else "") or "")
    if p.is_file():
        return p
    for c in CANDIDATES:
        if c.is_file():
            return c
    return None


def sanitize_variants(v):
    if not isinstance(v, dict):
        return {}
    changed = False
    for vk, vv in list(v.items()):
        if isinstance(vv, str):
            v[vk] = {"status": norm_status(vv), "notes": ""}
            changed = True
        elif isinstance(vv, dict):
            vv["status"] = norm_status(vv.get("status", ""))
            if "notes" not in vv or vv.get("notes") is None:
                vv["notes"] = ""
                changed = True
            for dk in list(DROP_KEYS):
                if dk in vv:
                    del vv[dk]
                    changed = True
        else:
            v[vk] = {"status": "FAIL", "notes": ""}
            changed = True
    return v


def main():
    p = load_target()
    if not p:
        print("[enforce] nenhum report.json encontrado", file=sys.stderr)
        sys.exit(0)

    data = json.loads(p.read_text(encoding="utf-8", errors="ignore"))
    stages = data.get("stages")
    if not isinstance(stages, dict):
        print("[enforce] objeto stages ausente ou inválido — ignorando")
        sys.exit(0)

    changed = False
    for k, v in list(stages.items()):
        if isinstance(v, str):
            stages[k] = {"status": norm_status(v), "variants": {}, "notes": ""}
            changed = True
            continue
        if not isinstance(v, dict):
            stages[k] = {"status": "FAIL", "variants": {}, "notes": ""}
            changed = True
            continue

        v["status"] = norm_status(v.get("status", ""))
        if "variants" not in v or not isinstance(v.get("variants"), dict):
            v["variants"] = {}
            changed = True
        else:
            before = json.dumps(v["variants"], sort_keys=True)
            v["variants"] = sanitize_variants(v["variants"])
            after = json.dumps(v["variants"], sort_keys=True)
            if before != after:
                changed = True

        if "notes" not in v or v.get("notes") is None:
            v["notes"] = ""
            changed = True

        for dk in list(DROP_KEYS):
            if dk in v:
                del v[dk]
                changed = True

    if changed:
        p.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print(f"[enforce] normalize/sanitize aplicado em {p}")
    else:
        print("[enforce] nada a alterar")


if __name__ == "__main__":
    main()
