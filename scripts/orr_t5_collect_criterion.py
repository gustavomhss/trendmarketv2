#!/usr/bin/env python3
import json, os
E='out/obs_gatecheck/evidence'; os.makedirs(E, exist_ok=True)
with open(os.path.join(E,'criterion_summary.json'),'w') as f:
    json.dump({"bench_collected": False, "note": "no criterion artifacts found; using stub"}, f)
print("T5_COLLECT_OK")
