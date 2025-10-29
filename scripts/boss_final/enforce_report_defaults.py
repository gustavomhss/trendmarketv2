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
        if not isinstance(v, dict):
            # Se for string como "PASSED"/"FAILED", converte para objeto mínimo válido
            stages[k] = {"status": str(v), "variants": {}, "notes": ""}
            changed = True
            continue

        # Garantir campos exigidos
        if "variants" not in v or not isinstance(v.get("variants"), dict):
            v["variants"] = {}
            changed = True
        if "notes" not in v or v.get("notes") is None:
            v["notes"] = ""
            changed = True

        # Remover chaves não permitidas pelo schema
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
