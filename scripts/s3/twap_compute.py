#!/usr/bin/env python3
import sys, csv, math, statistics
from datetime import datetime, timedelta
from pathlib import Path
# Entrada: CSV com colunas: ts,price (por market_id separado por arquivo)
# Saída: CSV com twap_1m, twap_5m, twap_15m, divergence (|price-twap5|/twap5)

def parse_ts(s):
    return datetime.fromisoformat(s.replace('Z','+00:00'))

def window_avg(points, now, minutes):
    start = now - timedelta(minutes=minutes)
    xs = [p[1] for p in points if p[0] >= start and p[0] <= now]
    return sum(xs)/len(xs) if xs else float('nan')

inp = Path(sys.argv[1])
out = Path(sys.argv[2])
rows = []
with inp.open() as f:
    r = csv.DictReader(f)
    for row in r:
        rows.append((parse_ts(row['ts']), float(row['price'])))
rows.sort(key=lambda x:x[0])

out.parent.mkdir(parents=True, exist_ok=True)
with out.open('w') as f:
    w = csv.writer(f)
    w.writerow(['ts','price','twap_1m','twap_5m','twap_15m','divergence_pct'])
    for i,(ts,price) in enumerate(rows):
        tw1 = window_avg(rows[:i+1], ts, 1)
        tw5 = window_avg(rows[:i+1], ts, 5)
        tw15= window_avg(rows[:i+1], ts, 15)
        div = abs(price - tw5)/tw5*100 if (not math.isnan(tw5) and tw5!=0) else float('nan')
        w.writerow([ts.isoformat(), price, round(tw1,8), round(tw5,8), round(tw15,8), round(div,4)])
