#!/usr/bin/env python3
from __future__ import annotations
import json
import re
from pathlib import Path

LOCK_PATHS = [
    Path('out/guard/s4/actions_lock_report.json'),
    Path('.github/actions.lock'),
]

def load_lock() -> dict[str, str]:
    mapping: dict[str, str] = {}
    for path in LOCK_PATHS:
        if not path.exists():
            continue
        if path.suffix == '.json':
            data = json.loads(path.read_text(encoding='utf-8'))
            actions = data.get('actions', [])
            for entry in actions:
                repo = str(entry.get('repo', '')).strip().lower()
                sha = str(entry.get('sha', '')).strip()
                if repo and sha:
                    mapping[repo] = sha
        else:
            # simple parser for YAML lock with lines "key: repo@ref" and "commit: sha"
            repo = None
            for line in path.read_text(encoding='utf-8').splitlines():
                line = line.strip()
                if line.startswith('key:') and '@' in line:
                    repo = line.split(':', 1)[1].strip().split('@', 1)[0].lower()
                elif line.startswith('commit:') and repo:
                    sha = line.split(':', 1)[1].strip()
                    if repo and sha:
                        mapping[repo] = sha
                        repo = None
    return mapping

RE_USES = re.compile(
    r'^(?P<prefix>\s*-?\s*uses:\s*)(?P<repo>[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)@(?P<ref>[^\s#]+)(?P<suffix>.*)$'
)
RE_PIN_COMMENT = re.compile(r'\s+#\s*pinned\s*\(was.*\)\s*$', re.IGNORECASE)


def main() -> int:
    mapping = load_lock()
    if not mapping:
        raise SystemExit('no lock mapping found')

    changed_files = 0
    for wf in sorted(Path('.github/workflows').glob('*.yml')) + sorted(Path('.github/workflows').glob('*.yaml')):
        original = wf.read_text(encoding='utf-8')
        lines = original.splitlines()
        updated = []
        modified = False
        for line in lines:
            m = RE_USES.match(line)
            if m:
                repo = m.group('repo')
                key = repo.lower()
                sha = mapping.get(key)
                if sha and sha != m.group('ref'):
                    line = f"{m.group('prefix')}{repo}@{sha}{m.group('suffix')}"
                    modified = True
                # Remove pinned comments regardless of replacement
                new_line = RE_PIN_COMMENT.sub('', line)
                if new_line != line:
                    modified = True
                line = new_line
            updated.append(line)
        if modified:
            wf.write_text('\n'.join(updated) + '\n', encoding='utf-8')
            changed_files += 1
    print(f'[patch] arquivos alterados: {changed_files}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
