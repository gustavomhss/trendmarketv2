#!/usr/bin/env python3
"""Exporta sumário de performance do DEC em formato notebook-lite."""
from __future__ import annotations

import json
import os
from datetime import datetime

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
OUT_DIR = os.path.join(ROOT, "out", "s4_orr")
SUMMARY = os.path.join(OUT_DIR, "dec_perf_summary.json")

os.makedirs(OUT_DIR, exist_ok=True)

summary = {
    "generated_at": datetime.utcnow().isoformat() + "Z",
    "sources": {
        "dec_summary": os.path.join(OUT_DIR, "EVI", "dec_120rps_60m.json"),
        "cdc_series": os.path.join(OUT_DIR, "EVI", "cdc_lag_p95_seconds_5m.json"),
        "rum_snapshot": os.path.join(OUT_DIR, "EVI", "web_inp_snapshot.json"),
    },
    "metrics": {
        "dec_p95_target_ms": 800,
        "cdc_lag_target_s": 120,
        "inp_p75_target_ms": 200,
    },
}

with open(SUMMARY, "w", encoding="utf-8") as handle:
    json.dump(summary, handle, indent=2)

print(f"[nb.perf] resumo salvo em {SUMMARY}")
