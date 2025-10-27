import json
import os

root = os.environ.get('ARTS_DIR') or os.path.join(os.environ.get('RUNNER_TEMP', '.'), 'boss-arts')
report_dir = os.environ.get('REPORT_DIR') or os.path.join(os.environ.get('RUNNER_TEMP', '.'), 'boss-aggregate')
os.makedirs(report_dir, exist_ok=True)
found: list[dict] = []
for d, _, fs in os.walk(root):
    for f in fs:
        if f == 'report.json':
            try:
                with open(os.path.join(d, f), encoding='utf-8') as handle:
                    payload = json.load(handle)
                if isinstance(payload, dict) and isinstance(payload.get('stages'), list):
                    found.extend(payload['stages'])
            except Exception as exc:  # pragma: no cover - defensive
                found.append({'name': 'unknown', 'status': 'error', 'errors': [str(exc)]})
names = {s.get('name') for s in found}
for idx in range(1, 7):
    stage_name = f's{idx}'
    if stage_name not in names:
        found.append({'name': stage_name, 'status': 'missing', 'errors': ['artifact not found']})
report_path = os.path.join(report_dir, 'report.json')
with open(report_path, 'w', encoding='utf-8') as handle:
    json.dump({'stages': found}, handle, ensure_ascii=False)
status = 'PASS' if all(s.get('status') == 'passed' for s in found) else 'FAIL'
with open(os.path.join(report_dir, 'guard_status.txt'), 'w', encoding='utf-8') as handle:
    handle.write(status + '\n')
lines = [f"| {s.get('name', '?')} | {s.get('status', 'unknown')} |" for s in found]
header = ['| Stage | Status |', '| --- | --- |']
comment_path = os.path.join(report_dir, 'pr_comment.md')
with open(comment_path, 'w', encoding='utf-8') as handle:
    handle.write('Q1 Boss Final — Stage Summary\n\n')
    handle.write('\n'.join(header + lines) + '\n')
