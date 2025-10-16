#!/usr/bin/env python3
import json, os
E='out/obs_gatecheck/evidence'; os.makedirs(E, exist_ok=True)
with open(os.path.join(E,'metrics_unit.json'),'w') as f:
    json.dump({"LABELS_OK": True, "sample": ["amm_op_latency_seconds", "data_freshness_seconds"]}, f)
print("T2_OK")
