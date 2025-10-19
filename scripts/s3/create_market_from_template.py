#!/usr/bin/env python3
import json, sys, uuid, time
from pathlib import Path
CAT = json.loads(Path('configs/templates/catalog.json').read_text())
TPL_BY_ID = {t['id']: t for t in CAT['templates']}

def main():
    if len(sys.argv) < 3:
        print('usage: create_market_from_template.py <TEMPLATE_ID> <MARKET_NAME>')
        sys.exit(1)
    tpl_id, name = sys.argv[1], sys.argv[2]
    tpl = TPL_BY_ID.get(tpl_id)
    if not tpl:
        print(f'unknown template: {tpl_id}', file=sys.stderr); sys.exit(2)
    market = {
        'market_id': str(uuid.uuid4()),
        'template_id': tpl_id,
        'name': name,
        'category': tpl['category'],
        'truth_source': tpl['truth_source'],
        'resolution_deadline': int(time.time()) + tpl['resolution_window_h']*3600,
        'status': 'open'
    }
    out = Path('out/s3_gatecheck/generated_markets.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    data = []
    if out.exists():
        data = json.loads(out.read_text())
    data.append(market)
    out.write_text(json.dumps(data, indent=2))
    print(market['market_id'])
if __name__ == '__main__':
    main()
