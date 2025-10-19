#!/usr/bin/env bash
set -euo pipefail
python3 scripts/s3/create_market_from_template.py TPL-YESNO-01 "Pergunta Interna 001" >/tmp/mkt_id.txt
id=$(tail -n1 /tmp/mkt_id.txt)
[[ -n "$id" ]] || { echo "no market id" >&2; exit 1; }
[[ -s out/s3_gatecheck/generated_markets.json ]] || { echo "no generated_markets.json" >&2; exit 1; }
echo "OK $id"
