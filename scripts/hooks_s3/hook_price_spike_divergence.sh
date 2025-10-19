#!/usr/bin/env bash
set -euo pipefail
IN="$1"; OUT="$2" # IN: CSV preço/ts | OUT: JSON
python3 scripts/s3/twap_compute.py "$IN" out/s3_gatecheck/twap.csv
python3 - out/s3_gatecheck/twap.csv "$OUT" <<'PY'
import csv, json, sys
csv_path, out = sys.argv[1], sys.argv[2]
win=0; viol=False
for i,row in enumerate(csv.DictReader(open(csv_path))):
    div = float(row['divergence_pct']) if row['divergence_pct'] else 0.0
    if div>1.0:
        win+=1
    else:
        win=0
    if win>=2:
        viol=True; break
open(out,'w').write(json.dumps({'hook':'price_spike_divergence','violation': viol}))
PY
