#!/usr/bin/env python3
import json
import sys
from pathlib import Path

ALLOWED_STAGE_KEYS = {
    "status",
    "checks",
    "notes",
    "variants",
    "triage",
    "evidence",
    "summary",
    "runtime",
}


def main():
    p = Path(sys.argv[1] if len(sys.argv) > 1 else "out/boss_final/report.json")
    if not p.exists():
        print("[sanitize] report não encontrado; pulando", file=sys.stderr)
        sys.exit(0)

    data = json.loads(p.read_text(encoding="utf-8", errors="ignore"))
    stages = data.get("stages")
    if isinstance(stages, dict):
        touched = False
        for k, v in list(stages.items()):
            if isinstance(v, dict):
                if "variants" not in v or v["variants"] is None:
                    v["variants"] = {}
                    touched = True
                drop = [kk for kk in list(v.keys()) if kk not in ALLOWED_STAGE_KEYS]
                for kk in drop:
                    v.pop(kk, None)
                    touched = True
        if touched:
            p.write_text(
                json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
            )
            print("[sanitize] report ajustado para o schema")
        else:
            print("[sanitize] nada a fazer")
    else:
        print("[sanitize] objeto 'stages' ausente/ inválido; nada a fazer")


if __name__ == "__main__":
    main()
