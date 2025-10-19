#!/usr/bin/env python3
import sys, json, time
from pathlib import Path


def load_risk_caps(path: str) -> dict:
    text = Path(path).read_text().splitlines()
    caps_section = False
    current = None
    caps = {}
    for raw in text:
        stripped = raw.strip()
        if not stripped or stripped.startswith('#'):
            continue
        if stripped == 'risk_caps:':
            caps_section = True
            continue
        if caps_section:
            if not raw.startswith('  '):
                break
            if raw.startswith('  ') and not raw.startswith('    '):
                current = stripped.rstrip(':')
                caps[current] = {}
                continue
            if current and raw.startswith('    ') and ':' in raw:
                field, value = raw.split(':', 1)
                value = value.strip()
                try:
                    parsed = int(value)
                except ValueError:
                    try:
                        parsed = float(value)
                    except ValueError:
                        parsed = value
                caps[current][field.strip()] = parsed
    return caps


RISK_CAPS = load_risk_caps('configs/policies/mbp_s3.yml')
TPL_LIMITS = {
  'binary': RISK_CAPS.get('template_yesno', {}),
  'continuous': RISK_CAPS.get('template_continuous', {})
}
# Entrada: JSON de ordens [{user, market_id, template_category, qty, ts}]
# Saída: JSON de eventos de abuso moderados
orders = json.loads(Path(sys.argv[1]).read_text())
now = int(time.time())
by_user = {}
flags = []
for o in orders:
    lim = TPL_LIMITS.get(o['template_category'], {})
    rate_limit = lim.get('max_trade_rate_per_min', 0)
    exposure_limit = lim.get('max_exposure_per_user', 0)
    key = (o['user'], o['market_id'])
    by_user.setdefault(key, []).append(o['ts'])
    recent = [t for t in by_user[key] if now - t <= 60]
    if rate_limit and len(recent) > rate_limit:
        flags.append({'market_id': o['market_id'], 'kind':'rate_limit', 'severity':'med', 'action':'limited'})
    if exposure_limit and o['qty'] > exposure_limit:
        flags.append({'market_id': o['market_id'], 'kind':'exposure', 'severity':'high', 'action':'paused'})
Path('out/s3_gatecheck/abuse_flags.json').write_text(json.dumps(flags, indent=2))
print(len(flags))
