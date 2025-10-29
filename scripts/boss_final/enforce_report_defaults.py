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

p = Path((sys.argv[1] if len(sys.argv) > 1 else "") or "")
if not p.is_file():
    p = next((c for c in CANDIDATES if c.is_file()), None)
if not p:
    print("[enforce] nenhum report.json encontrado", file=sys.stderr)
    sys.exit(0)

data = json.loads(p.read_text(encoding="utf-8", errors="ignore"))
stages = data.get("stages")
if isinstance(stages, dict):
    changed = False
    for k, v in stages.items():
        if isinstance(v, dict) and ("notes" not in v or v.get("notes") is None):
            v["notes"] = ""
            changed = True
        if isinstance(v, dict) and ("variants" not in v or v.get("variants") is None):
            # garante campo exigido pelo schema para todos os stages
            v["variants"] = {}
            changed = True
    if changed:
        p.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        print(f"[enforce] defaults aplicados em {p}")
    else:
        print("[enforce] nada a alterar")
else:
    print("[enforce] objeto stages ausente ou inválido — ignorando")
