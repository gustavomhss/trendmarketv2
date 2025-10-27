import json
import os
from pathlib import Path

arts_dir = os.environ.get('ARTS_DIR') or os.path.join(os.environ.get('RUNNER_TEMP', '.'), 'boss-arts')
report_dir = os.environ.get('REPORT_DIR') or os.path.join(os.environ.get('RUNNER_TEMP', '.'), 'boss-aggregate')
os.makedirs(report_dir, exist_ok=True)
found: list[dict] = []
for dirpath, _, filenames in os.walk(arts_dir):
    for filename in filenames:
        if filename == 'report.json':
            try:
                with open(os.path.join(dirpath, filename), encoding='utf-8') as handle:
                    payload = json.load(handle)
                if isinstance(payload, dict) and isinstance(payload.get('stages'), list):
                    found.extend(payload['stages'])
            except Exception as exc:  # pragma: no cover - defensivo
                found.append({'name': 'unknown', 'status': 'error', 'errors': [str(exc)]})
names = {stage.get('name') for stage in found}
for idx in range(1, 7):
    stage_name = f's{idx}'
    if stage_name not in names:
        found.append({'name': stage_name, 'status': 'missing', 'errors': ['artifact not found']})
report_path = Path(report_dir) / 'report.json'
with report_path.open('w', encoding='utf-8') as handle:
    json.dump({'stages': found}, handle, ensure_ascii=False)
counts = {
    status: sum(1 for stage in found if stage.get('status') == status)
    for status in {'passed', 'failed', 'missing', 'error'}
}
summary = {'summary': {'counts': counts}}
print(json.dumps(summary, ensure_ascii=False))
status_value = 'PASS' if all(stage.get('status') == 'passed' for stage in found) else 'FAIL'
(Path(report_dir) / 'guard_status.txt').write_text(status_value + '\n', encoding='utf-8')
lines = ['| Stage | Status |', '| --- | --- |']
for stage in sorted(found, key=lambda item: item.get('name', '')):
    lines.append(f"| {stage.get('name', '?')} | {stage.get('status', 'unknown')} |")
(Path(report_dir) / 'pr_comment.md').write_text(
    'Q1 Boss Final — Stage Summary\n\n' + '\n'.join(lines) + '\n',
    encoding='utf-8',
)
