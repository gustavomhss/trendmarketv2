#!/usr/bin/env python3
import json
import sys
from pathlib import Path

CANDIDATES = [
    Path("out/boss_final/report.local.json"),
    Path("out/boss_final/report.json"),
    Path("out/summary/report.json"),
    Path("out/report.json"),
]

DROP_KEYS = {"name", "clean", "exit_code"}
ALLOWED = {"PASSED", "FAILED", "SKIPPED"}


def norm_status(s: str) -> str:
    t = (s or "").strip().lower()
    if t in {"pass", "passed", "ok", "success", "successful", "green", "aprovado"}:
        return "PASSED"
    if t in {"fail", "failed", "error", "err", "broken", "red", "reprovado"}:
        return "FAILED"
    if t in {"skip", "skipped", "ignored", "noop", "na", "n/a"}:
        return "SKIPPED"
    u = (s or "").strip().upper()
    if u == "PASS":
        return "PASSED"
    if u in ALLOWED:
        return u
    # Fallback seguro: se for algo inesperado, marque como FAILED
    return "FAILED"


def load_target() -> Path | None:
    p = Path((sys.argv[1] if len(sys.argv) > 1 else "") or "")
    if p.is_file():
        return p
    for c in CANDIDATES:
        if c.is_file():
            return c
    return None


def main() -> None:
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
            stages[k] = {"status": "FAILED", "variants": {}, "notes": ""}
            changed = True
            continue

        # normaliza status
        v["status"] = norm_status(v.get("status", ""))

        # garante campos exigidos
        if "variants" not in v or not isinstance(v.get("variants"), dict):
            v["variants"] = {}
            changed = True
        if "notes" not in v or v.get("notes") is None:
            v["notes"] = ""
            changed = True

        # remove chaves rejeitadas pelo schema
        for dk in list(DROP_KEYS):
            if dk in v:
                del v[dk]
                changed = True

    if changed:
        p.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print(f"[enforce] defaults/sanitize aplicados em {p}")
    else:
        print("[enforce] nada a alterar")


if __name__ == "__main__":
    main()
