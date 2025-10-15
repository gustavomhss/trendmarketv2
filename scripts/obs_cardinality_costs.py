#!/usr/bin/env python3
import json, os
E = 'out/obs_gatecheck/evidence'; os.makedirs(E, exist_ok=True)
metrics = {
  "amm_op_latency_seconds_bucket": {"labels": ["op","env","service"], "series": 240},
  "data_freshness_seconds":        {"labels": ["source","domain","env"],   "series": 180},
  "cdc_lag_seconds":               {"labels": ["stream","partition","env"],  "series": 320},
  "drift_score":                   {"labels": ["feature","env"],             "series": 80},
  "hook_coverage_ratio":           {"labels": ["env"],                         "series": 3}
}
price = 0.30  # $ por milhão de amostras
ret_days = 30
samples_day = 86400/15  # scrape 15s
cost = sum(v["series"]*samples_day*ret_days*price/1e6 for v in metrics.values())
with open(f"{E}/costs_cardinality.json","w") as f:
    json.dump({"metrics":metrics,"price_per_million":price,
               "retention_days":ret_days,"est_usd_month":round(cost,2)}, f, indent=2)
print("COSTS_OK")
