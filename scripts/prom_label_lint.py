#!/usr/bin/env python3
import sys, re, json, os
E = 'out/obs_gatecheck/evidence'; os.makedirs(E, exist_ok=True)
allow = {
  'amm_op_latency_seconds': set(['op','env','service','version']),
  'data_freshness_seconds': set(['source','domain','service','env']),
  'cdc_lag_seconds': set(['stream','partition','service','env']),
  'drift_score': set(['feature','service','env']),
  'hook_coverage_ratio': set(['env']),
  'hook_executions_total': set(['hook_id','status','env']),
  'synthetic_requests_total': set(['route','service','env']),
  'synthetic_latency_seconds': set(['route','service','env']),
  'synthetic_ok_ratio': set(['route','service','env'])
}
reserved = set(["le", "quantile"])
violations = []
# busca simples por métricas no repo (arquivos .rs/.go/.py/.yml/.yaml)
for root,_,files in os.walk('.'):
  for fn in files:
    if not re.search(r'\.(rs|go|py|yml|yaml)$', fn):
      continue
    path = os.path.join(root, fn)
    try:
      txt = open(path,'r',errors='ignore').read()
    except: continue
    for m in re.finditer(r'(amm_op_latency_seconds|data_freshness_seconds|cdc_lag_seconds|drift_score|hook_coverage_ratio|hook_executions_total|synthetic_requests_total|synthetic_latency_seconds|synthetic_ok_ratio).*?\{([^}]*)\}', txt, re.S):
      name = m.group(1)
      labels = m.group(2)
      keys = set([kv.split('=')[0].strip().strip('"') for kv in labels.split(',') if '=' in kv])
      keys = set([k for k in keys if k not in reserved])
      extra = keys - allow.get(name,set())
      if extra:
        violations.append({'file':path,'metric':name,'extra_labels':sorted(list(extra))})
open(f"{E}/label_lint.json","w").write(json.dumps({'violations':violations},indent=2))
if violations:
  print('LABELS_FAIL'); sys.exit(1)
print('LABELS_OK')
