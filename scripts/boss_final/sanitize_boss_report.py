#!/usr/bin/env python3
import json
import sys
from pathlib import Path

p = Path("out/boss/boss-final-report.json")
if not p.is_file():
    print("[sanitize] report não encontrado, ignorando", file=sys.stderr)
    sys.exit(0)

data = json.loads(p.read_text(encoding="utf-8", errors="ignore"))
stages = data.get("stages")
if isinstance(stages, dict):
    fixed = {}
    for name, stage in stages.items():
        # Aceita somente objeto {"variants": ...}. Se vier o stage bruto, extrai variants.
        if (
            isinstance(stage, dict)
            and "variants" in stage
            and isinstance(stage["variants"], dict)
        ):
            fixed[name] = {"variants": stage["variants"]}
        elif isinstance(stage, dict):
            # fallback conservador: tenta achar variants embutido
            v = stage.get("variants", {})
            fixed[name] = {"variants": v if isinstance(v, dict) else {}}
        else:
            fixed[name] = {"variants": {}}
    data["stages"] = fixed
    p.write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print("[sanitize] stages normalizados (apenas {variants})")
else:
    print("[sanitize] objeto stages ausente ou inválido — ignorando")
